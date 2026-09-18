/*
 * Copyright (c) 2014-2026 Bjoern Kimminich & the OWASP Juice Shop contributors.
 * SPDX-License-Identifier: MIT
 */

import fs from 'node:fs'
import { Readable } from 'node:stream'
import { finished } from 'node:stream/promises'
import { type Request, type Response, type NextFunction } from 'express'
import net from 'node:net'
import dns from 'node:dns'

import * as security from '../lib/insecurity'
import { UserModel } from '../models/user'
import * as utils from '../lib/utils'
import logger from '../lib/logger'

function isPrivateIPv4 (a: number, b: number, c: number, d: number): boolean {
  if (a === 0) return true
  if (a === 10) return true
  if (a === 127) return true
  if (a === 169 && b === 254) return true
  if (a === 172 && b >= 16 && b <= 31) return true
  if (a === 192 && b === 168) return true
  if (a === 100 && b >= 64 && b <= 127) return true
  if (a === 192 && b === 0 && (c === 0 || c === 2)) return true
  if (a === 198 && (b === 18 || b === 19)) return true
  if (a === 198 && b === 51 && c === 100) return true
  if (a === 203 && b === 0 && c === 113) return true
  if (a >= 224) return true
  return false
}

function parseIPv6 (ip: string): number[] | null {
  let clean = ip.toLowerCase()
  if (clean.startsWith('[') && clean.endsWith(']')) {
    clean = clean.slice(1, -1)
  }
  if (clean.includes('.')) {
    const lastColon = clean.lastIndexOf(':')
    const v4Part = clean.slice(lastColon + 1)
    const v4Parts = v4Part.split('.').map(Number)
    if (v4Parts.length !== 4 || v4Parts.some(n => isNaN(n) || n < 0 || n > 255)) return null
    const hex1 = ((v4Parts[0] << 8) | v4Parts[1]).toString(16)
    const hex2 = ((v4Parts[2] << 8) | v4Parts[3]).toString(16)
    clean = clean.slice(0, lastColon) + ':' + hex1 + ':' + hex2
  }
  const parts = clean.split('::')
  if (parts.length > 2) return null
  const left = parts[0] ? parts[0].split(':') : []
  const right = parts.length === 2 && parts[1] ? parts[1].split(':') : []
  if (parts.length === 1) {
    if (left.length !== 8) return null
    return left.map(h => parseInt(h, 16))
  }
  const missing = 8 - (left.length + right.length)
  if (missing < 1) return null
  const middle = new Array(missing).fill('0')
  return [...left, ...middle, ...right].map(h => parseInt(h || '0', 16))
}

function isPrivateIP (ip: string): boolean {
  const v4Match = ip.match(/^(\d+)\.(\d+)\.(\d+)\.(\d+)$/)
  if (v4Match) {
    const [, a, b, c, d] = v4Match.map(Number)
    return isPrivateIPv4(a, b, c, d)
  }
  try {
    const w = parseIPv6(ip)
    if (!w || w.length !== 8 || w.some(isNaN)) return true
    if (w.every(x => x === 0)) return true
    if (w.slice(0, 7).every(x => x === 0) && w[7] === 1) return true
    if ((w[0] & 0xffc0) === 0xfe80) return true
    if ((w[0] & 0xfe00) === 0xfc00) return true
    if ((w[0] & 0xff00) === 0xff00) return true
    if (w[0] === 0x2001 && (w[1] === 0x0db8 || w[1] === 0x0002)) return true
    if (w.slice(0, 5).every(x => x === 0) && w[5] === 0xffff) {
      return isPrivateIPv4((w[6] >> 8) & 0xff, w[6] & 0xff, (w[7] >> 8) & 0xff, w[7] & 0xff)
    }
    if (w[0] === 0x0064 && w[1] === 0xff9b && w.slice(2, 6).every(x => x === 0)) {
      return isPrivateIPv4((w[6] >> 8) & 0xff, w[6] & 0xff, (w[7] >> 8) & 0xff, w[7] & 0xff)
    }
    if (w.slice(0, 6).every(x => x === 0)) {
      return isPrivateIPv4((w[6] >> 8) & 0xff, w[6] & 0xff, (w[7] >> 8) & 0xff, w[7] & 0xff)
    }
    if (w[0] === 0x2002) {
      return isPrivateIPv4((w[1] >> 8) & 0xff, w[1] & 0xff, (w[2] >> 8) & 0xff, w[2] & 0xff)
    }
  } catch {
    return true
  }
  return false
}

async function isSafeUrl (urlString: string): Promise<boolean> {
  let parsedUrl: URL
  try {
    parsedUrl = new URL(urlString)
  } catch {
    return false
  }

  if (parsedUrl.protocol !== 'http:' && parsedUrl.protocol !== 'https:') {
    return false
  }

  let host = parsedUrl.hostname.toLowerCase().replace(/\.+$/, '')
  if (!host) {
    return false
  }

  if (host.startsWith('[') && host.endsWith(']')) {
    host = host.slice(1, -1)
  }

  if (host === 'localhost' || host.endsWith('.localhost') || host.endsWith('.local') || host.endsWith('.internal') || host.endsWith('.lan') || host.endsWith('.intra')) {
    return false
  }

  if (net.isIP(host) !== 0) {
    return !isPrivateIP(host)
  }

  try {
    const addresses = await dns.promises.lookup(host, { all: true })
    if (!addresses || addresses.length === 0) {
      return false
    }
    for (const record of addresses) {
      if (isPrivateIP(record.address)) {
        return false
      }
    }
  } catch {
    return false
  }

  return true
}

async function fetchSafeUrl (targetUrl: string, maxRedirects = 5): Promise<Response> {
  let currentUrl = targetUrl
  for (let i = 0; i <= maxRedirects; i++) {
    if (!await isSafeUrl(currentUrl)) {
      throw new Error('Blocked unsafe URL')
    }
    const response = await fetch(currentUrl, { redirect: 'manual' })
    if (response.status >= 300 && response.status < 400 && response.headers.has('location')) {
      const redirectLocation = response.headers.get('location')
      if (!redirectLocation) {
        throw new Error('Redirect without Location header')
      }
      currentUrl = new URL(redirectLocation, currentUrl).toString()
      continue
    }
    return response
  }
  throw new Error('Too many redirects')
}

export function profileImageUrlUpload () {
  return async (req: Request, res: Response, next: NextFunction) => {
    if (req.body.imageUrl !== undefined) {
      const url = req.body.imageUrl
      if (typeof url !== 'string') {
        res.status(400)
        next(new Error('Blocked illegal activity by ' + req.socket.remoteAddress))
        return
      }
      if (url.match(/(.)*solve\/challenges\/server-side(.)*/) !== null) req.app.locals.abused_ssrf_bug = true
      const loggedInUser = security.authenticatedUsers.get(req.cookies.token)
      if (loggedInUser) {
        if (!await isSafeUrl(url)) {
          res.status(400)
          next(new Error('Blocked illegal activity by ' + req.socket.remoteAddress))
          return
        }
        try {
          const response = await fetchSafeUrl(url)
          if (!response.ok || !response.body) {
            throw new Error('url returned a non-OK status code or an empty body')
          }
          const ext = ['jpg', 'jpeg', 'png', 'svg', 'gif'].includes(url.split('.').slice(-1)[0].toLowerCase()) ? url.split('.').slice(-1)[0].toLowerCase() : 'jpg'
          const fileStream = fs.createWriteStream(`frontend/dist/frontend/assets/public/images/uploads/${loggedInUser.data.id}.${ext}`, { flags: 'w' })
          await finished(Readable.fromWeb(response.body as any).pipe(fileStream))
          const user = await UserModel.findByPk(loggedInUser.data.id)
          await user?.update({ profileImage: `/assets/public/images/uploads/${loggedInUser.data.id}.${ext}` })
        } catch (error) {
          if (utils.getErrorMessage(error).includes('Blocked unsafe URL')) {
            res.status(400)
            next(new Error('Blocked illegal activity by ' + req.socket.remoteAddress))
            return
          }
          try {
            const user = await UserModel.findByPk(loggedInUser.data.id)
            await user?.update({ profileImage: url })
            logger.warn(`Error retrieving user profile image: ${utils.getErrorMessage(error)}; using image link directly`)
          } catch (error) {
            next(error)
            return
          }
        }
      } else {
        next(new Error('Blocked illegal activity by ' + req.socket.remoteAddress))
        return
      }
    }
    res.location(process.env.BASE_PATH + '/profile')
    res.redirect(process.env.BASE_PATH + '/profile')
  }
}
