// server.js - Express rewrite of the Cloudflare Worker for Hugging Face Spaces / any Node.js host
// Node.js 18+ required (uses native fetch, Request, Response, Headers, crypto.subtle)

import { webcrypto } from "crypto";
import fs from "fs/promises";
import express from "express";
import { Readable } from "stream"; // Added for native backpressure and memory optimization

if (!globalThis.crypto) globalThis.crypto = webcrypto;

globalThis.atob = (b64) =>
    Buffer.from(b64, "base64").toString("binary");

globalThis.btoa = (str) =>
    Buffer.from(str, "binary").toString("base64");

// Constants

const KEY_RE = /^[a-f0-9]{20}$/;
// Default provider base URL — set PROVIDER_BASE_URL env var, no hardcoded domain.
const DEFAULT_PROVIDER_BASE_URL = "";
// Generic user-agent — override with FETCH_USER_AGENT env var.
const DEFAULT_FETCH_USER_AGENT = "Mozilla/5.0 (SmartTV; Linux) AppleWebKit/537.36";
const APP_BUILD_ID = "dqvod-ultra-low-latency-2026-06-17";

// Credentials come from env vars only: PROVIDER_USERNAME, PROVIDER_PASSWORD.
// Nothing is hardcoded here.
const HARDCODED_PROVIDER_USERNAME = "";
const HARDCODED_PROVIDER_PASSWORD = "";
const HARDCODED_URL_TOKEN_SECRET = "please-set-URL_TOKEN_SECRET-in-env";

// Extra playlist sources can be added via the EXTRA_PLAYLIST_SOURCES env var
// (newline- or comma-separated URLs). Nothing hardcoded.
const HARDCODED_EXTRA_PLAYLIST_SOURCES = [];

const XTREAM_CATALOGS = {
    live: {
        categoriesAction: "get_live_categories",
        itemsAction: "get_live_streams",
        idField: "stream_id",
    },
    movies: {
        categoriesAction: "get_vod_categories",
        itemsAction: "get_vod_streams",
        idField: "stream_id",
    },
    series: {
        categoriesAction: "get_series_categories",
        itemsAction: "get_series",
        idField: "series_id",
    },
};

// In-memory caches (survive across requests, reset on restart)

const channelCache = { at: 0, channels: [] };
const playlistChannelCache = { at: 0, channels: [] };
const streamIndex = new Map();
const upstreamHlsCache = new Map();
const livePlaylistCache = new Map();
const generatedPlaylistCache = new Map();
const hmacKeyCache = new Map();
const upstreamHlsInflight = new Map();
const livePlaylistInflight = new Map();
const xtreamCatalogCache = new Map();
const xtreamCatalogInflight = new Map();
const slugIndex = new Map();
const keyToSlugIndex = new Map();
const xtreamLocalNumericIndex = new Map();
let channelLoadPromise = null;
let playlistChannelLoadPromise = null;
let customServersCache = [];


// ─── Segment Cache (in-memory LRU with inflight deduplication) ──────────────
// Multiple viewers requesting the same .ts segment = ONE upstream fetch.
// This is the single biggest optimization for reducing lag and upstream load.
const segmentCache = new Map();       // url → { at, headers, body (Buffer) }
const segmentInflight = new Map();    // url → Promise<{headers, body, status}>
const MAX_SEGMENT_CACHE_ENTRIES = 300;
const SEGMENT_CACHE_TTL_MS = 45_000;  // 45s — covers ~6 segment intervals

// ─── Circuit Breaker (skip failing upstreams temporarily) ───────────────────
const circuitBreaker = new Map();     // url-origin → { failures, lastFailure, openUntil }
const CIRCUIT_BREAKER_THRESHOLD = 10;  // failures before opening circuit (relaxed to avoid premature cutouts)
const CIRCUIT_BREAKER_WINDOW_MS = 30_000;  // failure counting window (shorter window = forgive faster)
const CIRCUIT_BREAKER_COOLDOWN_MS = 15_000; // how long to skip a broken upstream (recover faster)

// ─── Upstream Health Tracking ───────────────────────────────────────────────
const upstreamHealthStats = new Map(); // origin → { successes, failures, lastSuccess, lastFailure, avgLatencyMs }
let globalRequestCount = 0;
let globalSegmentCacheHits = 0;
let globalSegmentCacheMisses = 0;
const serverStartedAt = Date.now();

// ─── Bunny CDN Pull Zone Integration ────────────────────────────────────────
// Automatically creates Bunny CDN pull zones for IPTV origins so segments
// are served from Bunny's global edge network instead of through our server.
const BUNNY_API_BASE = "https://api.bunny.net";
const BUNNY_DATA_DIR = process.env.BUNNY_DATA_DIR || "/data";
const BUNNY_PULLZONE_DATA_FILE = `${BUNNY_DATA_DIR}/bunny-pullzones.json`;
const BUNNY_PULLZONE_CACHE_TTL_MS = (Number.parseInt(process.env.BUNNY_PULLZONE_CACHE_TTL_HOURS, 10) || 24) * 3600_000;
const BUNNY_SEGMENT_CACHE_SEC = Number.parseInt(process.env.BUNNY_PULLZONE_SEGMENT_CACHE_SEC, 10) || 30;
const bunnyPullZoneCache = new Map();    // origin → { hostname, pullZoneId, createdAt }
const bunnyPullZoneInflight = new Map(); // origin → Promise<{ hostname, pullZoneId } | null>
let bunnyInitialized = false;
let bunnyEnabled = false; // set to true at startup if BUNNY_API_KEY is present

// ─── Stream Warmup / Loading Video ──────────────────────────────────────────
const streamWarmupState = new Map();
const MAX_WARMUP_ENTRIES = 500;
const WARMUP_EXPIRY_MS = 120_000;
const LOADING_VIDEO_URL = "https://pub-170b5f1508954220a1c673d1ae1baaae.r2.dev/TaxiDevLoad.mp4";
const WARMUP_REQUIRED_SEGMENTS = 2;

// Disk-persist cache paths
const CHANNEL_DISK_CACHE_FILE = process.env.CHANNEL_DISK_CACHE_FILE || "channel-cache.json";
const PLAYLIST_DISK_CACHE_FILE = process.env.PLAYLIST_DISK_CACHE_FILE || "playlist-channel-cache.json";
const CUSTOM_PLAYLISTS_FILE = process.env.CUSTOM_PLAYLISTS_FILE || "custom-playlists.json";
const CUSTOM_SERVERS_FILE = process.env.CUSTOM_SERVERS_FILE || "custom-servers.json";

const MAX_UPSTREAM_HLS_CACHE_ENTRIES = 500;
const MAX_LIVE_PLAYLIST_CACHE_ENTRIES = 500;
const MAX_XTREAM_CATALOG_CACHE_ENTRIES = 100;
const MAX_GENERATED_PLAYLIST_CACHE_ENTRIES = 200;

// ─── Xtream API Response Cache ──────────────────────────────────────────────
// Caches fully-built Xtream API responses (get_live_streams, get_live_categories, etc.)
// so IPTV receivers get instant responses from cache instead of rebuilding every time.
const xtreamResponseCache = new Map(); // cacheKey → { at, payload (JSON string) }
const XTREAM_RESPONSE_CACHE_TTL_MS = 120_000; // 2 minutes — fast enough for live TV
const MAX_XTREAM_RESPONSE_CACHE_ENTRIES = 50;

const ACCESS_DURATION_MONTHS = {
    "1m": 1,
    "3m": 3,
    "12m": 12,
    infinite: null,
};

// Errors

class HttpError extends Error {
    constructor(status, message) {
        super(message);
        this.status = status;
    }
}

// Env helpers (reads from process.env)

function envString(env, key, fallback = "") {
    return String((env && env[key]) ?? fallback).trim();
}

function envInt(env, key, fallback) {
    const value = Number.parseInt(envString(env, key), 10);
    return Number.isFinite(value) ? value : fallback;
}

function envBool(env, key, fallback) {
    const value = envString(env, key);
    if (!value) return fallback;
    return ["1", "true", "yes", "on"].includes(value.toLowerCase());
}

// Public base URL

function publicBase(request, env) {
    const requestOrigin = new URL(request.url).origin;
    const configuredBase = envString(env, "WORKER_PUBLIC_BASE");
    if (envBool(env, "FORCE_WORKER_PUBLIC_BASE", false) && configuredBase) {
        return configuredBase.replace(/\/+$/, "");
    }
    return (requestOrigin || configuredBase).replace(/\/+$/, "");
}

// CDN-aware base for HLS segment / live-stream URLs.
// Set CDN_BASE_URL=https://cdn.taxidev.me to route all .ts segments and
// live m3u8 URLs through your CDN instead of hitting the origin directly.
// API calls (player_api.php, /api/*, /get.php) always use the origin.
function streamBase(request, env) {
    const cdn = envString(env, "CDN_BASE_URL", "").replace(/\/+$/, "");
    return cdn || publicBase(request, env);
}

// Response helpers

function withCors(response) {
    const headers = new Headers(response.headers);
    headers.set("access-control-allow-origin", "*");
    headers.set("access-control-allow-methods", "GET,HEAD,OPTIONS");
    headers.set("access-control-allow-headers", "*");
    headers.set("access-control-expose-headers", "Content-Length, Content-Range, Accept-Ranges, Content-Type");
    headers.set("x-content-type-options", "nosniff");
    return new Response(response.body, {
        status: response.status,
        statusText: response.statusText,
        headers,
    });
}

function json(payload, status = 200) {
    return withCors(
        new Response(JSON.stringify(payload, null, 2), {
            status,
            headers: {
                "content-type": "application/json; charset=utf-8",
                "cache-control": "no-store, max-age=0",
            },
        }),
    );
}

function playlistResponse(body) {
    return withCors(
        new Response(body, {
            headers: {
                "content-type": "application/x-mpegURL; charset=utf-8",
                "cache-control": "no-store, no-cache, max-age=0, must-revalidate",
                pragma: "no-cache",
                expires: "0",
                "content-disposition": "inline",
            },
        }),
    );
}

function htmlResponse(body, status = 200, headers = {}) {
    return new Response(body, {
        status,
        headers: {
            "content-type": "text/html; charset=utf-8",
            "cache-control": "no-store, max-age=0",
            ...headers,
        },
    });
}

function textResponse(body, status = 200, headers = {}) {
    return withCors(
        new Response(body, {
            status,
            headers: {
                "content-type": "text/plain; charset=utf-8",
                "cache-control": "no-store, max-age=0",
                ...headers,
            },
        }),
    );
}

// Logging helpers

const SENSITIVE_QUERY_PARAMS = new Set([
    "password",
    "pass",
    "token",
    "auth",
    "signature",
    "sig",
]);

function maskSecret(value) {
    const text = String(value ?? "");
    if (!text) return "[empty]";
    if (text.length <= 4) return "[redacted]";
    return `${text.slice(0, 2)}...${text.slice(-2)}`;
}

function sanitizePathForLog(pathname) {
    return String(pathname || "/")
        .replace(/^(\/(?:live|movie|series)\/[^/]+\/)([^/]+)(\/)/i, (_match, prefix, password, suffix) => `${prefix}${maskSecret(password)}${suffix}`)
        .replace(/^(\/(?:upseg|upstream-segment)\/[^/]+\/)([^/]+)(\/)/i, (_match, prefix, token, suffix) => `${prefix}${maskSecret(token)}${suffix}`)
        .replace(/^(\/(?:direct|source|playlist)\/)([^/.]+)(\.m3u8)$/i, (_match, prefix, token, suffix) => `${prefix}${maskSecret(token)}${suffix}`);
}

function sanitizeUrlForLog(rawUrl) {
    if (process.env.DEBUG_API === "true") return String(rawUrl || "/");
    try {
        const text = String(rawUrl || "/");
        const includeOrigin = /^https?:\/\//i.test(text);
        const parsed = new URL(text, "http://local");
        parsed.pathname = sanitizePathForLog(parsed.pathname);
        for (const key of [...parsed.searchParams.keys()]) {
            if (SENSITIVE_QUERY_PARAMS.has(key.toLowerCase())) {
                parsed.searchParams.set(key, maskSecret(parsed.searchParams.get(key)));
            }
        }
        return `${includeOrigin ? parsed.origin : ""}${parsed.pathname}${parsed.search}`;
    } catch {
        return sanitizePathForLog(rawUrl);
    }
}

function requestClientForLog(req) {
    return String(req.headers["x-forwarded-for"] || req.socket?.remoteAddress || "")
        .split(",")[0]
        .trim() || "unknown";
}

function payloadCount(payload) {
    if (Array.isArray(payload)) return payload.length;
    if (!payload || typeof payload !== "object") return null;
    for (const key of ["streams", "categories", "seasons"]) {
        if (Array.isArray(payload[key])) return payload[key].length;
    }
    if (payload.episodes && typeof payload.episodes === "object") {
        return Object.values(payload.episodes).reduce((total, episodes) => total + (Array.isArray(episodes) ? episodes.length : 0), 0);
    }
    return null;
}

function logXtreamAction(request, action, payload, extra = {}) {
    const count = payloadCount(payload);
    const details = [
        `action=${action || "auth"}`,
        extra.mode ? `mode=${extra.mode}` : "",
        extra.categoryId ? `category=${extra.categoryId}` : "",
        extra.id ? `id=${extra.id}` : "",
        count === null ? "" : `count=${count}`,
    ].filter(Boolean).join(" ");
    console.log(`[xtream] ${request.method} ${sanitizeUrlForLog(new URL(request.url).pathname + new URL(request.url).search)} ${details}`);

    if (true) {
        console.log(`[xtream-debug] Payload:`, JSON.stringify(payload, null, 2).slice(0, 5000));
    }
}

// Crypto helpers

async function sha1Hex(value) {
    const bytes = new TextEncoder().encode(value);
    const digest = await crypto.subtle.digest("SHA-1", bytes);
    return [...new Uint8Array(digest)].map((b) => b.toString(16).padStart(2, "0")).join("");
}

async function streamKey(sourceUrl) {
    return (await sha1Hex(sourceUrl)).slice(0, 20);
}

function b64urlEncodeBytes(bytes) {
    let binary = "";
    for (const byte of bytes) binary += String.fromCharCode(byte);
    return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/g, "");
}

function b64urlDecodeBytes(value) {
    const mod = value.length % 4;
    const padded = value + (mod ? "=".repeat(4 - mod) : "");
    const binary = atob(padded.replace(/-/g, "+").replace(/_/g, "/"));
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return bytes;
}

function b64urlEncodeJson(payload) {
    return b64urlEncodeBytes(new TextEncoder().encode(JSON.stringify(payload)));
}

function b64urlDecodeText(value) {
    return new TextDecoder().decode(b64urlDecodeBytes(value));
}

function getTokenSecret(env) {
    return envString(env, "URL_TOKEN_SECRET") || envString(env, "IPTV_PASSWORD") || HARDCODED_URL_TOKEN_SECRET;
}

async function importHmacKey(secret) {
    let keyPromise = hmacKeyCache.get(secret);
    if (!keyPromise) {
        keyPromise = crypto.subtle.importKey(
            "raw",
            new TextEncoder().encode(secret),
            { name: "HMAC", hash: "SHA-256" },
            false,
            ["sign"],
        );
        hmacKeyCache.set(secret, keyPromise);
    }
    return keyPromise;
}

async function signTokenPayload(secret, payloadB64) {
    const key = await importHmacKey(secret);
    const signature = await crypto.subtle.sign("HMAC", key, new TextEncoder().encode(payloadB64));
    return b64urlEncodeBytes(new Uint8Array(signature).slice(0, 16));
}

async function makeUrlToken(payload, env) {
    const body = b64urlEncodeJson(payload);
    if (!envBool(env, "SIGN_URL_TOKENS", false)) return body;
    const signature = await signTokenPayload(getTokenSecret(env), body);
    return `${signature}.${body}`;
}

function decodeUnsignedUrlToken(token) {
    try {
        const payload = JSON.parse(b64urlDecodeText(token));
        if (!payload || !payload.u) throw new Error("Missing URL.");
        return payload;
    } catch {
        throw new HttpError(404, "Upstream URL token expired or invalid.");
    }
}

async function readUrlToken(token, env) {
    if (!envBool(env, "SIGN_URL_TOKENS", false)) return decodeUnsignedUrlToken(token);
    if (!token.includes(".") && !token.includes("_")) return decodeUnsignedUrlToken(token);

    const separator = token.includes(".") ? "." : "_";
    const parts = token.split(separator);
    const signatureText = parts[0];
    const payloadText = parts.slice(1).join(separator);
    if (!signatureText || !payloadText) throw new HttpError(404, "Upstream URL token expired or invalid.");

    const expected = await signTokenPayload(getTokenSecret(env), payloadText);
    if (signatureText !== expected) throw new HttpError(404, "Upstream URL token expired or invalid.");

    try {
        const payload = JSON.parse(b64urlDecodeText(payloadText));
        if (!payload || !payload.u) throw new Error("Missing URL.");
        return payload;
    } catch {
        throw new HttpError(404, "Upstream URL token expired or invalid.");
    }
}

// Validation

function validateKey(key) {
    if (!KEY_RE.test(key)) throw new HttpError(404, "Unknown stream.");
}

// Generic helpers

function cleanString(value, fallback = "") {
    const text = String(value ?? "").trim();
    return text || fallback;
}

function normalizeSearchText(value) {
    return cleanString(value)
        .toLowerCase()
        .normalize("NFKD")
        .replace(/[\u0300-\u036f]/g, "")
        .replace(/[^a-z0-9]+/g, " ")
        .trim()
        .replace(/\s+/g, " ");
}

function channelMatchesQuery(channel, query) {
    const tokens = normalizeSearchText(query).split(" ").filter(Boolean);
    if (tokens.length === 0) return true;
    const haystack = normalizeSearchText(`${channel?.name || ""} ${channel?.category || ""} ${channel?.key || ""}`);
    return tokens.every((token) => haystack.includes(token));
}

function randomPlaylistId(length = 8) {
    const alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789";
    const bytes = new Uint8Array(length);
    crypto.getRandomValues(bytes);
    let output = "";
    for (const byte of bytes) output += alphabet[byte % alphabet.length];
    return output;
}

// ─── Circuit Breaker ─────────────────────────────────────────────────────────

function circuitBreakerKey(url) {
    try { return new URL(url).origin; } catch { return url; }
}

function isCircuitOpen(url) {
    const key = circuitBreakerKey(url);
    const state = circuitBreaker.get(key);
    if (!state) return false;
    if (Date.now() > state.openUntil) {
        circuitBreaker.delete(key);
        return false;
    }
    return true;
}

function recordCircuitFailure(url) {
    const key = circuitBreakerKey(url);
    const now = Date.now();
    let state = circuitBreaker.get(key);
    if (!state || now - state.lastFailure > CIRCUIT_BREAKER_WINDOW_MS) {
        state = { failures: 0, lastFailure: now, openUntil: 0 };
    }
    state.failures++;
    state.lastFailure = now;
    if (state.failures >= CIRCUIT_BREAKER_THRESHOLD) {
        state.openUntil = now + CIRCUIT_BREAKER_COOLDOWN_MS;
        console.warn(`[circuit-breaker] OPENED for ${key} (${state.failures} failures in window). Cooldown ${CIRCUIT_BREAKER_COOLDOWN_MS}ms`);
    }
    circuitBreaker.set(key, state);
}

function recordCircuitSuccess(url) {
    const key = circuitBreakerKey(url);
    circuitBreaker.delete(key); // reset on success
}

// ─── Upstream Health Tracking ────────────────────────────────────────────────

function trackUpstreamRequest(url, success, latencyMs) {
    const origin = circuitBreakerKey(url);
    let stats = upstreamHealthStats.get(origin);
    if (!stats) {
        stats = { successes: 0, failures: 0, lastSuccess: null, lastFailure: null, avgLatencyMs: 0, totalLatency: 0, totalRequests: 0 };
        upstreamHealthStats.set(origin);
    }
    stats.totalRequests++;
    stats.totalLatency += latencyMs;
    stats.avgLatencyMs = Math.round(stats.totalLatency / stats.totalRequests);
    if (success) {
        stats.successes++;
        stats.lastSuccess = Date.now();
    } else {
        stats.failures++;
        stats.lastFailure = Date.now();
    }
    upstreamHealthStats.set(origin, stats);
}

// ─── Segment Cache Helpers ───────────────────────────────────────────────────

function cleanupSegmentCache() {
    const now = Date.now();
    for (const [url, entry] of segmentCache) {
        if (now - entry.at > SEGMENT_CACHE_TTL_MS) segmentCache.delete(url);
    }
    while (segmentCache.size > MAX_SEGMENT_CACHE_ENTRIES) {
        segmentCache.delete(segmentCache.keys().next().value);
    }
}

// ─── Bunny CDN Pull Zone Management ─────────────────────────────────────────
// Creates and manages Bunny CDN pull zones for IPTV upstream origins.
// Segments (.ts, .m4s) are served through Bunny CDN instead of our proxy.
// If anything fails, getBunnyCdnSegmentUrl() returns null and the caller
// falls back to the existing /upseg/ proxy path.

async function bunnyApiRequest(method, path, body, env) {
    const apiKey = envString(env, "BUNNY_API_KEY");
    if (!apiKey) return null;
    const url = `${BUNNY_API_BASE}${path}`;
    const headers = {
        "AccessKey": apiKey,
        "Accept": "application/json",
    };
    const init = { method, headers, redirect: "follow" };
    if (body && (method === "POST" || method === "PUT")) {
        headers["Content-Type"] = "application/json";
        init.body = JSON.stringify(body);
    }
    try {
        const response = await fetchWithTimeout(url, init, 15000);
        const text = await response.text();
        if (!response.ok) {
            console.warn(`[bunny-cdn] API ${method} ${path} → HTTP ${response.status}: ${text.slice(0, 300)}`);
            return { ok: false, status: response.status, data: null, raw: text };
        }
        const data = text ? JSON.parse(text) : null;
        return { ok: true, status: response.status, data };
    } catch (err) {
        console.error(`[bunny-cdn] API ${method} ${path} FAILED: ${err?.message || err}`);
        return null;
    }
}

async function generatePullZoneName(origin) {
    // Deterministic name from origin hash so we always map the same origin to the same pull zone
    const hash = await sha1Hex(origin);
    // Bunny zone names: lowercase, alphanumeric + hyphens, 3-63 chars
    return `iptv-${hash.slice(0, 12)}`;
}

async function loadBunnyPullZones(env) {
    const filePath = envString(env, "BUNNY_PULLZONE_DATA_FILE") || BUNNY_PULLZONE_DATA_FILE;
    try {
        const text = await fs.readFile(filePath, "utf8");
        const data = JSON.parse(text);
        if (data && typeof data === "object" && data.pullZones) {
            const entries = Object.entries(data.pullZones);
            for (const [origin, info] of entries) {
                if (info && info.hostname && info.pullZoneId) {
                    bunnyPullZoneCache.set(origin, {
                        hostname: info.hostname,
                        pullZoneId: info.pullZoneId,
                        createdAt: info.createdAt || Date.now(),
                    });
                }
            }
            console.log(`[bunny-cdn] loaded ${entries.length} pull zone mapping(s) from disk`);
            return entries.length;
        }
    } catch (err) {
        if (err?.code !== "ENOENT") {
            console.warn(`[bunny-cdn] failed to load pull zones from ${filePath}: ${err?.message}`);
        }
    }
    return 0;
}

async function saveBunnyPullZones(env) {
    const filePath = envString(env, "BUNNY_PULLZONE_DATA_FILE") || BUNNY_PULLZONE_DATA_FILE;
    const pullZones = {};
    for (const [origin, info] of bunnyPullZoneCache) {
        pullZones[origin] = {
            hostname: info.hostname,
            pullZoneId: info.pullZoneId,
            createdAt: info.createdAt,
        };
    }
    const payload = {
        updatedAt: new Date().toISOString(),
        pullZones,
    };
    try {
        // Ensure the data directory exists
        const dir = filePath.slice(0, filePath.lastIndexOf("/"));
        if (dir) await fs.mkdir(dir, { recursive: true }).catch(() => null);
        await fs.writeFile(filePath, JSON.stringify(payload, null, 2) + "\n", "utf8");
        console.log(`[bunny-cdn] saved ${bunnyPullZoneCache.size} pull zone mapping(s) to disk`);
    } catch (err) {
        console.warn(`[bunny-cdn] failed to save pull zones to ${filePath}: ${err?.message}`);
    }
}

async function listBunnyPullZones(env) {
    const result = await bunnyApiRequest("GET", "/pullzone?page=0&perPage=1000", null, env);
    if (!result?.ok || !result.data) return [];
    // Response is { Items: [...], TotalItems: N } or just an array
    return Array.isArray(result.data) ? result.data : (Array.isArray(result.data?.Items) ? result.data.Items : []);
}

async function findExistingPullZone(env, originUrl, zoneName) {
    const allZones = await listBunnyPullZones(env);
    // First try to find by origin URL match
    for (const zone of allZones) {
        const zoneOrigin = (zone.OriginUrl || "").replace(/\/+$/, "");
        if (zoneOrigin === originUrl.replace(/\/+$/, "")) {
            const hostname = zone.Hostnames?.[0]?.Value || `${zone.Name}.b-cdn.net`;
            console.log(`[bunny-cdn] found existing pull zone "${zone.Name}" (ID ${zone.Id}) for origin ${originUrl}`);
            return { hostname, pullZoneId: zone.Id, name: zone.Name };
        }
    }
    // Then try by name
    for (const zone of allZones) {
        if (zone.Name === zoneName) {
            const hostname = zone.Hostnames?.[0]?.Value || `${zone.Name}.b-cdn.net`;
            console.log(`[bunny-cdn] found existing pull zone by name "${zoneName}" (ID ${zone.Id})`);
            return { hostname, pullZoneId: zone.Id, name: zone.Name };
        }
    }
    return null;
}

async function createBunnyPullZone(env, originUrl, zoneName) {
    const segmentCacheSec = envInt(env, "BUNNY_PULLZONE_SEGMENT_CACHE_SEC", BUNNY_SEGMENT_CACHE_SEC);
    const body = {
        Name: zoneName,
        OriginUrl: originUrl,
        EnableGeoZoneUS: true,
        EnableGeoZoneEU: true,
        EnableGeoZoneASIA: true,
        EnableGeoZoneSA: true,
        EnableGeoZoneAF: true,
        CacheControlMaxAgeOverride: segmentCacheSec,
        CacheControlPublicMaxAgeOverride: segmentCacheSec,
        FollowRedirects: true,
        DisableCookies: true,
        ConnectionLimitPerIPCount: 0,
        IgnoreQueryStrings: false,
        AddHostHeader: false,
        EnableTLS1: true,
        EnableTLS1_1: true,
        VerifyOriginSSL: false,         // IPTV origins often have invalid certs
        UseStaleWhileUpdating: true,
        UseStaleWhileOffline: true,
        EnableSmartCache: false,        // We control caching explicitly
        Type: 0,                        // Standard pull zone
    };

    const result = await bunnyApiRequest("POST", "/pullzone", body, env);
    if (!result) return null;

    if (result.ok && result.data) {
        const zone = result.data;
        const hostname = zone.Hostnames?.[0]?.Value || `${zone.Name || zoneName}.b-cdn.net`;
        console.log(`[bunny-cdn] ✓ created pull zone "${zone.Name}" (ID ${zone.Id}) → ${hostname} for origin ${originUrl}`);
        return { hostname, pullZoneId: zone.Id, name: zone.Name };
    }

    // 409 = name conflict — zone with this name already exists
    if (result.status === 409) {
        console.log(`[bunny-cdn] pull zone name "${zoneName}" already exists, searching for existing zone...`);
        return findExistingPullZone(env, originUrl, zoneName);
    }

    console.error(`[bunny-cdn] failed to create pull zone "${zoneName}" for ${originUrl}: HTTP ${result.status}`);
    return null;
}

async function getOrCreateBunnyPullZone(originUrl, env) {
    if (!bunnyEnabled) return null;
    const origin = originUrl.replace(/\/+$/, "");

    // 1. Check in-memory cache
    const cached = bunnyPullZoneCache.get(origin);
    if (cached && (Date.now() - cached.createdAt < BUNNY_PULLZONE_CACHE_TTL_MS)) {
        return cached;
    }

    // 2. Inflight deduplication — don't create the same pull zone concurrently
    const existing = bunnyPullZoneInflight.get(origin);
    if (existing) return existing;

    const promise = (async () => {
        try {
            const zoneName = await generatePullZoneName(origin);

            // Try to create — if it already exists, findExisting will pick it up
            const zone = await createBunnyPullZone(env, origin, zoneName)
                      || await findExistingPullZone(env, origin, zoneName);

            if (zone) {
                const entry = {
                    hostname: zone.hostname,
                    pullZoneId: zone.pullZoneId,
                    createdAt: Date.now(),
                };
                bunnyPullZoneCache.set(origin, entry);
                // Persist to disk so next restart is instant
                void saveBunnyPullZones(env);
                return entry;
            }
            console.warn(`[bunny-cdn] could not create or find pull zone for ${origin}`);
            return null;
        } catch (err) {
            console.error(`[bunny-cdn] getOrCreateBunnyPullZone failed for ${origin}: ${err?.message || err}`);
            return null;
        }
    })();

    bunnyPullZoneInflight.set(origin, promise);
    try {
        return await promise;
    } finally {
        if (bunnyPullZoneInflight.get(origin) === promise) {
            bunnyPullZoneInflight.delete(origin);
        }
    }
}

/**
 * Fast synchronous lookup: returns the Bunny CDN URL for a segment, or null.
 * This is called during playlist rewriting for every segment URL in every M3U8.
 * It MUST be fast — only checks the in-memory cache, never makes API calls.
 *
 * If the origin isn't cached yet, returns null (caller uses /upseg/ fallback)
 * and kicks off async pull zone creation in the background.
 */
function getBunnyCdnSegmentUrl(absoluteUrl, env) {
    if (!bunnyEnabled) return null;
    try {
        const parsed = new URL(absoluteUrl);
        const origin = parsed.origin;
        const cached = bunnyPullZoneCache.get(origin);
        if (cached && cached.hostname) {
            // Replace origin with Bunny CDN, preserve full path + query
            return `https://${cached.hostname}${parsed.pathname}${parsed.search}`;
        }
        // Origin not yet in cache — kick off async creation (don't await)
        if (!bunnyPullZoneInflight.has(origin)) {
            void getOrCreateBunnyPullZone(origin, env).catch(() => null);
        }
        return null;
    } catch {
        return null;
    }
}

/**
 * Startup initialization: load saved pull zones from disk and pre-create
 * pull zones for all configured IPTV provider origins.
 */
async function initBunnyPullZones(env) {
    const apiKey = envString(env, "BUNNY_API_KEY");
    if (!apiKey) {
        console.log("[bunny-cdn] BUNNY_API_KEY not set — Bunny CDN integration disabled (using proxy fallback)");
        bunnyEnabled = false;
        bunnyInitialized = true;
        return;
    }

    if (envString(env, "BUNNY_ENABLED", "true").toLowerCase() === "false") {
        console.log("[bunny-cdn] BUNNY_ENABLED=false — Bunny CDN integration disabled");
        bunnyEnabled = false;
        bunnyInitialized = true;
        return;
    }

    bunnyEnabled = true;
    console.log("[bunny-cdn] initializing Bunny CDN pull zone integration...");

    // 1. Load saved pull zone mappings from persistent storage
    await loadBunnyPullZones(env);

    // 2. Pre-create pull zones for all configured IPTV provider origins
    const sources = buildProviderPlaylistSources(env);
    const origins = new Set();
    for (const source of sources) {
        try {
            const parsed = new URL(source.url);
            origins.add(parsed.origin);
        } catch { /* skip invalid URLs */ }
    }

    if (origins.size > 0) {
        console.log(`[bunny-cdn] pre-creating pull zones for ${origins.size} IPTV origin(s)...`);
        const results = await Promise.allSettled(
            [...origins].map(origin => getOrCreateBunnyPullZone(origin, env))
        );
        const created = results.filter(r => r.status === "fulfilled" && r.value).length;
        const failed = results.length - created;
        console.log(`[bunny-cdn] initialization complete: ${created} pull zone(s) ready, ${failed} failed/skipped`);
    }

    bunnyInitialized = true;
}

// ─── Custom Servers Storage ──────────────────────────────────────────────────

function customServersFile(env) {
    return envString(env, "CUSTOM_SERVERS_FILE", "custom-servers.json") || "custom-servers.json";
}

async function loadCustomServers(env) {
    try {
        const text = await fs.readFile(customServersFile(env), "utf8");
        const data = JSON.parse(text);
        return Array.isArray(data?.servers) ? data.servers : [];
    } catch (error) {
        if (error && error.code === "ENOENT") return [];
        throw error;
    }
}

async function saveCustomServers(env, servers) {
    const payload = { updatedAt: new Date().toISOString(), servers };
    await fs.writeFile(customServersFile(env), `${JSON.stringify(payload, null, 2)}\n`, "utf8");
}


function randomCredential(length = 14) {
    const alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789";
    const bytes = new Uint8Array(length);
    crypto.getRandomValues(bytes);
    let output = "";
    for (const byte of bytes) output += alphabet[byte % alphabet.length];
    return output;
}

function parseRequestBool(value, fallback = false) {
    if (value === undefined || value === null || value === "") return fallback;
    if (typeof value === "boolean") return value;
    return ["1", "true", "yes", "on"].includes(String(value).toLowerCase());
}

function stripExtension(value) {
    const text = cleanString(value);
    const dot = text.lastIndexOf(".");
    return dot > 0 ? text.slice(0, dot) : text;
}

function encodePathSegment(value) {
    return encodeURIComponent(String(value));
}

function slugifyChannelName(name) {
    // Strip source suffixes like "(APIPRIMARY)", "(APIEXTRA)"
    let clean = String(name || "Unknown")
        .replace(/\s*\(API[A-Z]*\)\s*$/i, "")
        .replace(/\s*\([^)]*\)\s*$/, "")
        .trim();
    if (!clean) clean = "Unknown";
    // PascalCase: split on non-alphanumeric, capitalize each word
    return clean
        .split(/[^a-zA-Z0-9]+/)
        .filter(Boolean)
        .map((w) => w.charAt(0).toUpperCase() + w.slice(1))
        .join("");
}

function buildSlugIndex(channels) {
    const newSlugIndex = new Map();
    const newKeyToSlug = new Map();
    const slugCounts = new Map();
    for (const channel of channels) {
        let base = slugifyChannelName(channel.name);
        if (!base) base = "Channel";
        const count = (slugCounts.get(base) || 0) + 1;
        slugCounts.set(base, count);
        const slug = count === 1 ? base : `${base}${count}`;
        newSlugIndex.set(slug, channel.key);
        newKeyToSlug.set(channel.key, slug);
    }
    slugIndex.clear();
    keyToSlugIndex.clear();
    for (const [s, k] of newSlugIndex) slugIndex.set(s, k);
    for (const [k, s] of newKeyToSlug) keyToSlugIndex.set(k, s);
}

function normalizeSourceLabel(value) {
    return cleanString(value).toUpperCase();
}

function categoryName(category) {
    return cleanString(category?.category_name ?? category?.name ?? category?.title);
}

function itemId(item, catalogKind) {
    const setup = XTREAM_CATALOGS[catalogKind];
    return cleanString(item?.[setup.idField] ?? item?.stream_id ?? item?.series_id ?? item?.id);
}

function mediaLogo(item) {
    return cleanString(item?.stream_icon ?? item?.cover ?? item?.movie_image ?? item?.icon);
}

function mediaRating(item) {
    const value = item?.rating_5based ?? item?.rating;
    return value === undefined || value === null || value === "" ? null : value;
}

// M3U parsing

function parseExtinf(line) {
    const nameMatch = line.match(/,(.+)$/);
    const logoMatch = line.match(/tvg-logo="(.*?)"/);
    const categoryMatch = line.match(/group-title="(.*?)"/);
    return {
        name: (nameMatch && nameMatch[1] && nameMatch[1].trim()) || "Unknown",
        logo: (logoMatch && logoMatch[1] && logoMatch[1].trim()) || "",
        category: (categoryMatch && categoryMatch[1] && categoryMatch[1].trim()) || "",
    };
}

async function* readResponseLines(response) {
    if (!response.body) {
        const text = await response.text();
        for (const line of text.split(/\r?\n/)) yield line;
        return;
    }
    const reader = response.body.getReader();
    const decoder = new TextDecoder();
    let buffer = "";
    while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        buffer += decoder.decode(value, { stream: true });
        const parts = buffer.split(/\r?\n/);
        buffer = parts.pop() || "";
        for (const part of parts) yield part;
    }
    buffer += decoder.decode();
    if (buffer) yield buffer.endsWith("\r") ? buffer.slice(0, -1) : buffer;
}

function parseXtreamMediaUrl(rawUrl) {
    try {
        const parsed = new URL(rawUrl);
        const parts = parsed.pathname.split("/").filter(Boolean);
        if (parts.length >= 4 && ["live", "movie", "series"].includes(parts[0].toLowerCase())) {
            return { kind: parts[0].toLowerCase(), id: stripExtension(parts[3]) };
        }
        if (parts.length >= 3) {
            return { kind: "live", id: stripExtension(parts[2]) };
        }
    } catch {
        return null;
    }
    return null;
}

function inferPlaylistEntryKind(url) {
    const lower = url.toLowerCase();
    if (lower.includes("/series/")) return "series";
    if (lower.includes("/movie/") || [".mp4", ".mkv", ".avi", ".mov"].some((ext) => lower.includes(ext))) return "movie";
    return "live";
}

async function parseM3uEntries(response, onEntry) {
    let currentMeta = { name: "Unknown", logo: "", category: "" };
    for await (const rawLine of readResponseLines(response)) {
        const line = rawLine.trim();
        if (!line) continue;
        if (line.startsWith("#EXTINF")) {
            currentMeta = parseExtinf(line);
            continue;
        }
        if (line.startsWith("#")) continue;

        const xtreamParts = parseXtreamMediaUrl(line);
        const kind = xtreamParts?.kind || inferPlaylistEntryKind(line);
        const key = await streamKey(line);
        const result = await onEntry({
            key,
            kind,
            streamId: xtreamParts?.id || "",
            name: currentMeta.name,
            logo: currentMeta.logo,
            category: currentMeta.category,
            sourceUrl: line,
        });
        currentMeta = { name: "Unknown", logo: "", category: "" };
        if (result === false) return;
    }
}

async function parseM3uChannels(response, onChannel) {
    await parseM3uEntries(response, async (entry) => {
        if (entry.kind !== "live") return;
        return onChannel(entry);
    });
}

// Source list helpers

function splitSourceList(raw) {
    return String(raw || "").split(/\r?\n|,/).map((v) => v.trim()).filter(Boolean);
}

function withSourceSuffix(name, label) {
    return `${String(name || "Unknown").trim() || "Unknown"} (${label})`;
}

function buildProviderPlaylistSources(env) {
    const sources = [];
    
    // Add custom servers first (enabled ones)
    if (Array.isArray(customServersCache)) {
        customServersCache.forEach(server => {
            if (server.enabled) {
                const playlistUrl = new URL("/get.php", `${server.url}/`);
                playlistUrl.searchParams.set("username", server.username);
                playlistUrl.searchParams.set("password", server.password);
                playlistUrl.searchParams.set("type", "m3u_plus");
                sources.push({ url: playlistUrl.toString(), label: server.name || "CustomServer" });
            }
        });
    }

    const username = envString(env, "PROVIDER_USERNAME") || envString(env, "IPTV_USERNAME") || HARDCODED_PROVIDER_USERNAME;
    const password = envString(env, "PROVIDER_PASSWORD") || envString(env, "IPTV_PASSWORD") || HARDCODED_PROVIDER_PASSWORD;
    if (username && password) {
        const baseUrl = (
            envString(env, "PROVIDER_BASE_URL") ||
            envString(env, "IPTV_BASE_URL") ||
            DEFAULT_PROVIDER_BASE_URL
        ).replace(/\/+$/, "");
        if (baseUrl) {
            const playlistUrl = new URL("/get.php", `${baseUrl}/`);
            playlistUrl.searchParams.set("username", username);
            playlistUrl.searchParams.set("password", password);
            playlistUrl.searchParams.set("type", "m3u_plus");
            if (!sources.some(s => s.url === playlistUrl.toString())) {
                sources.push({ url: playlistUrl.toString(), label: "APIPRIMARY" });
            }
        }
    }
    for (const source of HARDCODED_EXTRA_PLAYLIST_SOURCES) {
        if (!sources.some((e) => e.url === source.url)) sources.push(source);
    }
    for (const extraUrl of splitSourceList(envString(env, "EXTRA_PLAYLIST_SOURCES"))) {
        if (!sources.some((e) => e.url === extraUrl)) sources.push({ url: extraUrl, label: "APIEXTRA" });
    }
    return sources;
}

function selectedPlaylistSources(env, sourceFilter) {
    const sources = buildProviderPlaylistSources(env);
    const wanted = normalizeSourceLabel(sourceFilter);
    if (!wanted) return sources;
    return sources.filter((source) => normalizeSourceLabel(source.label) === wanted);
}

// Xtream API helpers

function xtreamConfigFromPlaylistUrl(sourceUrl) {
    try {
        const parsed = new URL(sourceUrl);
        const username = cleanString(parsed.searchParams.get("username"));
        const password = cleanString(parsed.searchParams.get("password"));
        if (!username || !password) return null;
        return {
            baseUrl: parsed.origin.replace(/\/+$/, ""),
            username,
            password,
        };
    } catch {
        return null;
    }
}

function xtreamCacheKey(config) {
    return `${config.baseUrl}|${config.username}|${config.password}`;
}

function xtreamApiUrl(config, action, extraParams = {}) {
    const apiUrl = new URL("/player_api.php", `${config.baseUrl}/`);
    apiUrl.searchParams.set("username", config.username);
    apiUrl.searchParams.set("password", config.password);
    if (action) apiUrl.searchParams.set("action", action);
    for (const [key, value] of Object.entries(extraParams)) {
        if (value !== undefined && value !== null && value !== "") apiUrl.searchParams.set(key, String(value));
    }
    return apiUrl;
}

async function fetchXtreamApi(env, config, action, extraParams = {}) {
    const timeoutMs = envInt(env, "XTREAM_API_TIMEOUT_MS", 4000);
    const maxRetries = envInt(env, "XTREAM_API_RETRIES", 2);
    const headers = {
        "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
        accept: "application/json, text/plain, */*",
    };
    const urls = upstreamUrlCandidates(xtreamApiUrl(config, action, extraParams).toString(), env);
    const allFailures = [];

    for (const url of urls) {
        for (let attempt = 0; attempt <= maxRetries; attempt++) {
            try {
                const response = await fetchWithTimeout(url, { headers, redirect: "follow" }, timeoutMs);
                if (!response.ok) throw new Error(`HTTP ${response.status} ${response.statusText || ""}`.trim());
                const text = await response.text();
                const parsed = JSON.parse(text);
                if (attempt > 0) console.log(`[xtream-upstream] action=${action || "auth"} succeeded on retry ${attempt} for ${sanitizeUrlForLog(url)}`);
                return parsed;
            } catch (err) {
                const errMsg = `${sanitizeUrlForLog(url)} attempt ${attempt + 1}/${maxRetries + 1} -> ${err?.message || "unknown error"}`;
                allFailures.push(errMsg);
                if (attempt < maxRetries) {
                    const delayMs = 300 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
                    console.warn(`[xtream-upstream] action=${action || "auth"} ${errMsg}. Retrying in ${Math.round(delayMs)}ms...`);
                    await new Promise((resolve) => setTimeout(resolve, delayMs));
                }
            }
        }
    }
    console.error(`[xtream-upstream] action=${action || "auth"} FAILED all ${urls.length} URLs x ${maxRetries + 1} retries: ${allFailures.join("; ")}`);
    return null;
}

function indexCategories(categories) {
    const categoriesById = new Map();
    if (!Array.isArray(categories)) return categoriesById;
    for (const category of categories) {
        const id = cleanString(category?.category_id ?? category?.id);
        const name = categoryName(category);
        if (id && name) categoriesById.set(id, name);
    }
    return categoriesById;
}

function catalogCategory(catalog, item) {
    const categoryId = cleanString(item?.category_id ?? item?.category);
    return (
        (categoryId && catalog?.categoriesById?.get(categoryId)) ||
        cleanString(item?.category_name ?? item?.category)
    );
}

async function loadXtreamCatalog(env, playlistSource, catalogKind, force = false, fetchItems = true) {
    const config = xtreamConfigFromPlaylistUrl(playlistSource.url);
    const setup = XTREAM_CATALOGS[catalogKind];
    if (!config || !setup) return null;

    const cacheKey = `catalog:${catalogKind}:${fetchItems}:${xtreamCacheKey(config)}`;
    const ttlMs = envInt(env, "XTREAM_METADATA_CACHE_SECONDS", 300) * 1000;
    const cached = xtreamCatalogCache.get(cacheKey);
    if (!force && cached && Date.now() - cached.at < ttlMs) return cached;

    return withInflight(xtreamCatalogInflight, cacheKey, async () => {
        const promises = [fetchXtreamApi(env, config, setup.categoriesAction)];
        if (fetchItems) {
            promises.push(fetchXtreamApi(env, config, setup.itemsAction));
        }

        const results = await Promise.all(promises);
        const categories = results[0];
        const items = fetchItems ? results[1] : [];

        const categoriesById = indexCategories(categories);
        const catalogItems = Array.isArray(items) ? items : [];
        const itemsById = new Map();
        for (const item of catalogItems) {
            const id = itemId(item, catalogKind);
            if (id) itemsById.set(id, item);
        }

        const catalog = {
            at: Date.now(),
            kind: catalogKind,
            config,
            categoriesById,
            items: catalogItems,
            itemsById,
        };
        rememberMapEntry(xtreamCatalogCache, cacheKey, catalog, MAX_XTREAM_CATALOG_CACHE_ENTRIES);
        return catalog;
    });
}

async function loadXtreamSeriesInfo(env, playlistSource, seriesId, force = false) {
    const config = xtreamConfigFromPlaylistUrl(playlistSource.url);
    if (!config) return null;

    const cacheKey = `series-info:${xtreamCacheKey(config)}:${seriesId}`;
    const ttlMs = envInt(env, "XTREAM_METADATA_CACHE_SECONDS", 300) * 1000;
    const cached = xtreamCatalogCache.get(cacheKey);
    if (!force && cached && Date.now() - cached.at < ttlMs) return cached;

    return withInflight(xtreamCatalogInflight, cacheKey, async () => {
        const payload = await fetchXtreamApi(env, config, "get_series_info", { series_id: seriesId });
        const entry = {
            at: Date.now(),
            config,
            payload,
        };
        rememberMapEntry(xtreamCatalogCache, cacheKey, entry, MAX_XTREAM_CATALOG_CACHE_ENTRIES);
        return entry;
    });
}

function xtreamMediaUrl(config, kind, id, extension) {
    const cleanExtension = cleanString(extension).replace(/^\./, "");
    const suffix = cleanExtension ? `.${cleanExtension}` : "";
    return `${config.baseUrl}/${kind}/${encodePathSegment(config.username)}/${encodePathSegment(config.password)}/${encodePathSegment(id)}${suffix}`;
}

function sourceApiUrl(request, env, path, params = {}) {
    const apiUrl = new URL(path, publicBase(request, env));
    for (const [key, value] of Object.entries(params)) {
        if (value !== undefined && value !== null && value !== "") apiUrl.searchParams.set(key, String(value));
    }
    return apiUrl.toString();
}

async function channelsFromXtreamCatalog(playlistSource, liveCatalog) {
    if (!liveCatalog || !Array.isArray(liveCatalog.items) || liveCatalog.items.length === 0) return [];
    const channels = [];
    for (const item of liveCatalog.items) {
        const streamId = itemId(item, "live");
        if (!streamId) continue;
        const extension = cleanString(item.container_extension, "ts");
        const sourceUrl = xtreamMediaUrl(liveCatalog.config, "live", streamId, extension);
        channels.push({
            key: await streamKey(sourceUrl),
            name: withSourceSuffix(cleanString(item.name, "Unknown"), playlistSource.label),
            logo: mediaLogo(item),
            category: catalogCategory(liveCatalog, item),
            sourceUrl,
        });
    }
    return channels;
}

// Dashboard account storage

function accessUsersFile(env) {
    return envString(env, "ACCESS_USERS_FILE", "access-users.json") || "access-users.json";
}

function normalizeAccessUsersPayload(payload) {
    const rawUsers = Array.isArray(payload) ? payload : payload?.users;
    if (!Array.isArray(rawUsers)) return [];
    return rawUsers
        .map((user) => ({
            username: cleanString(user?.username),
            password: cleanString(user?.password),
            createdAt: cleanString(user?.createdAt) || new Date().toISOString(),
            expiresAt: user?.expiresAt ? cleanString(user.expiresAt) : null,
            disabled: Boolean(user?.disabled),
            includeLive: user?.includeLive === undefined ? true : Boolean(user.includeLive),
            includeMovies: Boolean(user?.includeMovies),
            includeSeries: Boolean(user?.includeSeries),
        }))
        .filter((user) => user.username && user.password);
}

async function loadAccessUsers(env) {
    try {
        const text = await fs.readFile(accessUsersFile(env), "utf8");
        return normalizeAccessUsersPayload(JSON.parse(text));
    } catch (error) {
        if (error && error.code === "ENOENT") return [];
        throw error;
    }
}

async function saveAccessUsers(env, users) {
    const payload = {
        updatedAt: new Date().toISOString(),
        users,
    };
    await fs.writeFile(accessUsersFile(env), `${JSON.stringify(payload, null, 2)}\n`, "utf8");
}

function expiryForDuration(duration) {
    if (duration === "infinite") return null;
    const months = ACCESS_DURATION_MONTHS[duration] ?? ACCESS_DURATION_MONTHS["1m"];
    const expires = new Date();
    expires.setMonth(expires.getMonth() + months);
    return expires.toISOString();
}

function isAccessUserExpired(user) {
    if (!user?.expiresAt) return false;
    const expiresMs = Date.parse(user.expiresAt);
    return Number.isFinite(expiresMs) && expiresMs <= Date.now();
}

function m3uLinkForUser(user, request, env) {
    const url = new URL("/get.php", publicBase(request, env));
    url.searchParams.set("username", user.username);
    url.searchParams.set("password", user.password);
    url.searchParams.set("type", "m3u_plus");
    return url.toString();
}

function playlistIncludeFlags(request, account) {
    const url = new URL(request.url);
    return {
        includeLive: account.includeLive !== false,
        includeMovies: account.includeMovies && parseRequestBool(url.searchParams.get("include_movies"), false),
        includeSeries: account.includeSeries && parseRequestBool(url.searchParams.get("include_series"), false),
    };
}

function serializeAccessUser(user, request, env) {
    return {
        username: user.username,
        created_at: user.createdAt,
        expires_at: user.expiresAt,
        expired: isAccessUserExpired(user),
        disabled: Boolean(user.disabled),
        include_live: user.includeLive !== false,
        include_movies: Boolean(user.includeMovies),
        include_series: Boolean(user.includeSeries),
        m3u_url: m3uLinkForUser(user, request, env),
    };
}

// ─── Custom Playlist Storage ─────────────────────────────────────────────────

function customPlaylistsFile(env) {
    return envString(env, "CUSTOM_PLAYLISTS_FILE", "custom-playlists.json") || "custom-playlists.json";
}

async function loadCustomPlaylists(env) {
    try {
        const text = await fs.readFile(customPlaylistsFile(env), "utf8");
        const data = JSON.parse(text);
        return Array.isArray(data?.playlists) ? data.playlists : [];
    } catch (error) {
        if (error && error.code === "ENOENT") return [];
        throw error;
    }
}

async function saveCustomPlaylists(env, playlists) {
    const payload = { updatedAt: new Date().toISOString(), playlists };
    await fs.writeFile(customPlaylistsFile(env), `${JSON.stringify(payload, null, 2)}\n`, "utf8");
}

// ─── Custom Categories Storage ───────────────────────────────────────────────

function customCategoriesFile(env) {
    return envString(env, "CUSTOM_CATEGORIES_FILE", "custom-categories.json") || "custom-categories.json";
}
// ─── Hardcoded default category: always present at position 1 ────────────────
const DEFAULT_WORLD_CUP_CATEGORY = {
    id: "1781796727851764",
    name: "WORLD CUP EVENTS | ADAM",
    order: 0,
    channelKeys: [
        "7f044eae16a6d4915280","c617b4280b4323686bf5","5f9539f8c6910b76f8c3","6ae59c902ac29b98e0de",
        "5d4ae36dafb49f3ecfaf","3dccad31d1f7e56597ec","d98e11c5bc363e46ca9c","fde346d47cd9c092a389",
        "5f61a0f554559d957e26","88fc2823527708b86202","097bd25caca55f4ab891","9337418bb3c95fba784f",
        "9d76515beeefaf1635be","4db79a571b1de5549f4e","d8d0a294cfe509ab8480","f124d6613581c0a90d87",
        "ba4d2d0c7d978710752f","5fd093b444bf668cb085","ed4ad2c52823eb4a17a7","d7e9a09728dcf212112e",
        "429590","71989","5bea60da1376411937d4","ec170e68542500365871","d968cacacb34d235aa3a",
        "71988","1e9a0c4c4ab1bb997290","938e1f0dd22b8244927d","ed166719c1ae6ffc2b62",
        "d1c39455f7381c3205b6","180cdb8c9ff176ca5710","f24b2937b417541af091","bf3ff045d54fde80cccd",
        "57a3d10388283acf67e5","a712e421c88522e9cae4","64c23c899486d2eb8fdb","a7eda3ddb79f28c39909",
        "2efa55fe58b04132d6ee","2c3053a4bc50093a4c29","9af9ac6825f6187aae0b","b1aad7b8c1bb3863d6ab",
        "18fcc41404807ecc0d5f","571c602d3d3d2e4b92a9","49d4538abefc78b13e75","b24ef577092034e14eaa",
        "36a109b5082f0bec83fa","cedb42b5526e6cbdbf91","614655747e8678ef7644","fc7c86196af98a677d3a",
        "3efd38e1f707410f8360","3a81ce4bffa37a4fdde6","ccfaad79a9dee970867c","37741db7da914c6538c4",
        "5f4094fc09850339b7a9","f81746361845d40a9b81","821c75b89519abdcb659","439211","439210",
        "439209","76312","1028480","1028482","1028481","76310","76311",
        "4fe20d719314f3f0051c","60f48c1cc58d516c3378","7dde78958ad84ec21cd6","4d331b46836520385ba7",
        "d07430c410c6b56adbde","aeb118c6c7b2a99714a2","2fcda81be1b15e35cc2f","0c142971168dd5f6366e",
        "4153612ff49856f3e387","61f1c498c60ff29cf306","87d9ba66799f85b50ced","58a995c08b4b7aad37b5",
        "be5af498a03b3dc4a729","feab02bfad15de60fd51","52b98a26a0e343dbbfbb","b3a6269d9fed71028071",
        "3ce309f2d1384ef5b2cd","67ff5a94840f3d92f093","a41146d0698d60ee8497","a885b67cb590f001714a",
        "38c4c0a30c8cbe69605b","1d3a15ceadcf3f7a0252","6ffaab82ba6f58821ad5","72134bcf18a3f0d9ab5f",
        "0e521b40eb59fcab9aa4","8fcca2c7f3ce86a393b9","d19b5ecb1a44ee24fa3b","1281523e4b5a14c9ab36",
        "16d6e58ecd4e0352df53","43b04d39f60e3cca00dc","dc6160df45aca57469ad","4cb0c8d5dc2ad245ef44",
        "71741fd03de823adf4db","f9f58983c064784c5bb0","eafc87c936ec306cd488","c386dfcb051f49b17a80",
        "9b9b05a855f858f8574c","335fe0b40202a1aabf3e","ef674a3979052f5e5eb4",
    ],
};

function ensureWorldCupCategory(categories) {
    // Always inject the World Cup category at the top if not already present
    const existing = categories.findIndex(c => c.id === DEFAULT_WORLD_CUP_CATEGORY.id);
    if (existing >= 0) {
        // Update it in place with the latest channel keys, keep it at its position
        categories[existing] = { ...categories[existing], channelKeys: DEFAULT_WORLD_CUP_CATEGORY.channelKeys, name: DEFAULT_WORLD_CUP_CATEGORY.name };
        return categories;
    }
    // Prepend it — shift all other orders down
    return [DEFAULT_WORLD_CUP_CATEGORY, ...categories];
}

async function loadCustomCategories(env) {
    try {
        const text = await fs.readFile(customCategoriesFile(env), "utf8");
        const data = JSON.parse(text);
        const cats = Array.isArray(data?.categories) ? data.categories : [];
        return ensureWorldCupCategory(cats);
    } catch (error) {
        if (error && error.code === "ENOENT") return ensureWorldCupCategory([]);
        throw error;
    }
}

async function saveCustomCategories(env, categories) {
    const payload = { updatedAt: new Date().toISOString(), categories };
    await fs.writeFile(customCategoriesFile(env), `${JSON.stringify(payload, null, 2)}\n`, "utf8");
}



function basicAuthCredentials(request) {
    const header = request.headers.get("authorization") || "";
    const match = header.match(/^Basic\s+(.+)$/i);
    if (!match) return null;
    try {
        const decoded = atob(match[1]);
        const separator = decoded.indexOf(":");
        if (separator < 0) return null;
        return {
            username: decoded.slice(0, separator),
            password: decoded.slice(separator + 1),
        };
    } catch {
        return null;
    }
}

function dashboardAuthorized(request, env) {
    const adminPassword = envString(env, "ADMIN_PASSWORD");
    if (!adminPassword) return true;
    const adminUsername = envString(env, "ADMIN_USERNAME", "admin") || "admin";
    const credentials = basicAuthCredentials(request);
    return credentials?.username === adminUsername && credentials?.password === adminPassword;
}

function dashboardAuthResponse() {
    return textResponse("Authentication required.", 401, {
        "www-authenticate": 'Basic realm="IPTV Dashboard"',
    });
}

function providerXtreamCredentials(env) {
    const username = envString(env, "PROVIDER_USERNAME") || envString(env, "IPTV_USERNAME");
    const password = envString(env, "PROVIDER_PASSWORD") || envString(env, "IPTV_PASSWORD");
    if (!username || !password) return null;
    return { username, password };
}

async function resolveXtreamUser(env, username, password) {
    const users = await loadAccessUsers(env);
    const user = users.find((entry) => entry.username === username && entry.password === password);
    if (user && !user.disabled && !isAccessUserExpired(user)) return user;

    const provider = providerXtreamCredentials(env);
    if (provider && provider.username === username && provider.password === password) {
        return {
            username,
            password,
            createdAt: new Date().toISOString(),
            expiresAt: null,
            disabled: false,
            includeLive: true,
            includeMovies: true,
            includeSeries: true,
        };
    }

    return null;
}

async function readRequestData(request) {
    const text = await request.text();
    if (!text.trim()) return {};
    const contentType = request.headers.get("content-type") || "";
    if (contentType.includes("application/json")) return JSON.parse(text);
    const params = new URLSearchParams(text);
    return Object.fromEntries(params.entries());
}

async function accessUsersPayload(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const users = await loadAccessUsers(env);
    return json({
        status: "ok",
        count: users.length,
        worker_url: publicBase(request, env),
        auth_enabled: Boolean(envString(env, "ADMIN_PASSWORD")),
        users: users.map((user) => serializeAccessUser(user, request, env)),
    });
}

async function createAccessUser(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const username = cleanString(data.username);
    const password = cleanString(data.password) || randomCredential(14);
    if (!username) throw new HttpError(400, "Username is required.");
    if (!/^[A-Za-z0-9_.@-]{2,64}$/.test(username)) throw new HttpError(400, "Username may contain letters, numbers, dot, underscore, dash, or @.");
    if (!/^[A-Za-z0-9_.@#$%+-]{4,96}$/.test(password)) throw new HttpError(400, "Password contains unsupported characters or is too short.");

    const duration = cleanString(data.duration, "1m");
    const expiresAt = data.expires_at ? cleanString(data.expires_at) : expiryForDuration(duration);
    const users = await loadAccessUsers(env);
    const now = new Date().toISOString();
    const existingIndex = users.findIndex((user) => user.username.toLowerCase() === username.toLowerCase());
    const user = {
        username,
        password,
        createdAt: existingIndex >= 0 ? users[existingIndex].createdAt : now,
        expiresAt,
        disabled: false,
        includeLive: parseRequestBool(data.include_live, true),
        includeMovies: parseRequestBool(data.include_movies, false),
        includeSeries: parseRequestBool(data.include_series, false),
    };

    if (existingIndex >= 0) users[existingIndex] = user;
    else users.push(user);
    await saveAccessUsers(env, users);
    void loadPlaylistChannels(env, false).catch(() => null);

    return json({
        status: "ok",
        user: serializeAccessUser(user, request, env),
    }, existingIndex >= 0 ? 200 : 201);
}

async function deleteAccessUser(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const username = cleanString(data.username);
    if (!username) throw new HttpError(400, "Username is required.");
    const users = await loadAccessUsers(env);
    const kept = users.filter((user) => user.username.toLowerCase() !== username.toLowerCase());
    await saveAccessUsers(env, kept);
    return json({ status: "ok", deleted: users.length - kept.length });
}

async function getPlaylistAccessUser(request, env) {
    const url = new URL(request.url);
    const username = cleanString(url.searchParams.get("username"));
    const password = cleanString(url.searchParams.get("password"));
    if (!username || !password) throw new HttpError(401, "Missing username or password.");
    const users = await loadAccessUsers(env);
    const user = users.find((entry) => entry.username === username && entry.password === password);
    if (!user || user.disabled) throw new HttpError(403, "Invalid playlist credentials.");
    if (isAccessUserExpired(user)) throw new HttpError(403, "Playlist credentials expired.");
    return user;
}

// Map/cache helpers

function rememberMapEntry(map, key, value, maxEntries) {
    if (map.has(key)) map.delete(key);
    map.set(key, value);
    while (map.size > maxEntries) map.delete(map.keys().next().value);
}

async function withInflight(map, key, loader) {
    const existing = map.get(key);
    if (existing) return existing;
    const promise = loader();
    map.set(key, promise);
    try {
        return await promise;
    } finally {
        if (map.get(key) === promise) map.delete(key);
    }
}

// ─── Disk cache helpers ───────────────────────────────────────────────────────

async function saveDiskCache(file, data) {
    try {
        await fs.writeFile(file, JSON.stringify(data), "utf8");
    } catch (err) {
        console.warn("[cache] Could not save disk cache", file, err?.message);
    }
}

async function loadDiskCache(file) {
    try {
        const text = await fs.readFile(file, "utf8");
        return JSON.parse(text);
    } catch {
        return null;
    }
}

// ─── Channel loading ─────────────────────────────────────────────────────────

async function doRefreshChannels(env) {
    const playlistSources = buildProviderPlaylistSources(env);
    if (playlistSources.length === 0) throw new HttpError(500, "No IPTV playlist sources configured.");

    const maxSourceRetries = envInt(env, "SOURCE_LOAD_RETRIES", 2);
    const channels = [];
    const nextStreamIndex = new Map();
    const seenKeys = new Set();
    let successCount = 0;
    let playlistOkCount = 0;
    let lastStatus = null;

    console.log(`[cache] refreshing channels from ${playlistSources.length} source(s): ${playlistSources.map((s) => s.label).join(", ")}`);

    const sourceResults = await Promise.all(playlistSources.map(async (playlistSource) => {
        let response = null;
        let liveCatalog = null;

        // Retry Xtream catalog loading
        for (let attempt = 0; attempt <= maxSourceRetries; attempt++) {
            try {
                liveCatalog = await loadXtreamCatalog(env, playlistSource, "live", attempt > 0);
                if (liveCatalog) break;
            } catch (err) {
                console.warn(`[cache] Xtream catalog load for ${playlistSource.label} attempt ${attempt + 1}/${maxSourceRetries + 1} failed: ${err?.message || err}`);
                if (attempt < maxSourceRetries) {
                    const delayMs = 500 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
                    await new Promise((resolve) => setTimeout(resolve, delayMs));
                }
            }
        }

        // Retry playlist fetch
        for (let attempt = 0; attempt <= maxSourceRetries; attempt++) {
            try {
                response = await fetchProviderPlaylist(env, playlistSource.url);
                if (response && response.ok) {
                    if (attempt > 0) console.log(`[cache] playlist fetch for ${playlistSource.label} succeeded on retry ${attempt}`);
                    break;
                }
                if (response && !response.ok) {
                    console.warn(`[cache] playlist fetch for ${playlistSource.label} attempt ${attempt + 1}/${maxSourceRetries + 1} returned HTTP ${response.status}`);
                }
            } catch (err) {
                console.warn(`[cache] playlist fetch for ${playlistSource.label} attempt ${attempt + 1}/${maxSourceRetries + 1} failed: ${err?.message || err}`);
                response = null;
            }
            if (attempt < maxSourceRetries && (!response || !response.ok)) {
                const delayMs = 500 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
                await new Promise((resolve) => setTimeout(resolve, delayMs));
            }
        }

        return { playlistSource, response, liveCatalog };
    }));

    for (const { playlistSource, response, liveCatalog } of sourceResults) {
        if (!response && !liveCatalog) {
            console.error(`[cache] source ${playlistSource.label} COMPLETELY FAILED after all retries`);
            lastStatus = "network error";
            continue;
        }

        if (response && response.ok) {
            try {
                let sourceChannelCount = 0;
                await parseM3uChannels(response, async (channel) => {
                    if (seenKeys.has(channel.key)) return;
                    const xtreamItem = channel.streamId ? liveCatalog?.itemsById?.get(channel.streamId) : null;
                    const name = cleanString(xtreamItem?.name, channel.name);
                    const logo = mediaLogo(xtreamItem) || channel.logo;
                    const category = (xtreamItem ? catalogCategory(liveCatalog, xtreamItem) : "") || channel.category;
                    seenKeys.add(channel.key);
                    nextStreamIndex.set(channel.key, channel.sourceUrl);
                    channels.push({ key: channel.key, name: withSourceSuffix(name, playlistSource.label), logo, category });
                    sourceChannelCount++;
                });
                successCount += 1;
                playlistOkCount += 1;
                console.log(`[cache] source ${playlistSource.label} loaded ${sourceChannelCount} channels via playlist`);
            } catch (err) {
                console.error(`[cache] FAILED to parse M3U from source ${playlistSource.label}: ${err?.message || err}`);
                lastStatus = "parse error";
            }
            continue;
        }

        if (liveCatalog) {
            const xtreamChannels = await channelsFromXtreamCatalog(playlistSource, liveCatalog);
            if (xtreamChannels.length > 0) {
                successCount += 1;
                let sourceChannelCount = 0;
                for (const channel of xtreamChannels) {
                    if (seenKeys.has(channel.key)) continue;
                    seenKeys.add(channel.key);
                    nextStreamIndex.set(channel.key, channel.sourceUrl);
                    channels.push({ key: channel.key, name: channel.name, logo: channel.logo, category: channel.category });
                    sourceChannelCount++;
                }
                console.log(`[cache] source ${playlistSource.label} loaded ${sourceChannelCount} channels via Xtream fallback`);
                continue;
            }
        }

        lastStatus = response ? response.status : "network error";
        console.warn(`[cache] source ${playlistSource.label} produced no channels (status: ${lastStatus})`);
    }

    if (successCount === 0) {
        console.error(`[cache] ALL ${playlistSources.length} IPTV sources FAILED. Last status: ${lastStatus}`);
        if (channelCache.channels.length > 0) {
            console.warn(`[cache] serving ${channelCache.channels.length} stale cached channels`);
            return channelCache.channels;
        }
        throw new HttpError(502, `All IPTV playlist sources failed${lastStatus ? ` (last status: ${lastStatus})` : ""}.`);
    }

    // If we only managed to build channels via the smaller Xtream fallback, do not replace an existing
    // full playlist cache (this is what causes the 34k -> 9k swings).
    if (playlistOkCount === 0 && channelCache.channels.length > 0) {
        console.warn(`[cache] channels refresh used Xtream fallback only (${channels.length}); keeping existing cache (${channelCache.channels.length}).`);
        return channelCache.channels;
    }

    streamIndex.clear();
    for (const [key, sourceUrl] of nextStreamIndex) streamIndex.set(key, sourceUrl);
    channelCache.at = Date.now();
    channelCache.channels = channels;

    // Persist to disk so next restart is instant
    void saveDiskCache(CHANNEL_DISK_CACHE_FILE, {
        at: channelCache.at,
        channels,
        streamIndex: [...nextStreamIndex.entries()],
    });

    buildSlugIndex(channels);
    console.log(`[cache] channels refreshed: ${channels.length} total channels from ${successCount}/${playlistSources.length} sources`);
    return channels;
}

async function loadChannels(env, force = false) {
    const now = Date.now();
    const ttlMs = envInt(env, "CHANNEL_CACHE_SECONDS", 120) * 1000;

    // ── INSTANT PATH: return whatever is in cache right now ──────────────────
    if (!force && channelCache.channels.length > 0) {
        // If stale, kick off a background refresh but DO NOT wait for it
        if (now - channelCache.at >= ttlMs && !channelLoadPromise) {
            channelLoadPromise = doRefreshChannels(env).finally(() => { channelLoadPromise = null; });
        }
        return channelCache.channels; // ← returns in <1ms
    }

    // ── COLD START: must wait once (disk was not pre-loaded yet) ─────────────
    if (!force && channelLoadPromise) return channelLoadPromise;
    channelLoadPromise = doRefreshChannels(env).finally(() => { channelLoadPromise = null; });
    return channelLoadPromise;
}

async function doRefreshPlaylistChannels(env) {
    const playlistSources = buildProviderPlaylistSources(env);
    if (playlistSources.length === 0) throw new HttpError(500, "No IPTV playlist sources configured.");

    const channels = [];
    const nextStreamIndex = new Map();
    const seenKeys = new Set();
    let successCount = 0;
    let lastStatus = null;

    const sourceResults = await Promise.all(playlistSources.map(async (playlistSource) => {
        const liveCatalog = await loadXtreamCatalog(env, playlistSource, "live", false).catch(() => null);
        if (liveCatalog) {
            const ch = await channelsFromXtreamCatalog(playlistSource, liveCatalog);
            if (ch.length > 0) return { playlistSource, status: 200, channels: ch, mode: "xtream" };
        }
        try {
            const response = await fetchProviderPlaylist(env, playlistSource.url);
            if (!response.ok) return { playlistSource, status: response.status, channels: [] };
            const ch = [];
            await parseM3uChannels(response, async (channel) => {
                ch.push({
                    key: channel.key,
                    name: withSourceSuffix(channel.name, playlistSource.label),
                    logo: channel.logo,
                    category: channel.category,
                    sourceUrl: channel.sourceUrl,
                });
            });
            return { playlistSource, status: response.status, channels: ch };
        } catch {
            return { playlistSource, status: "network error", channels: [], error: "network error" };
        }
    }));

    for (const { status, channels: sourceChannels, error } of sourceResults) {
        if (error) { lastStatus = error || "network error"; continue; }
        if (status !== 200) { lastStatus = status; continue; }
        successCount += 1;
        for (const channel of sourceChannels) {
            if (seenKeys.has(channel.key)) continue;
            seenKeys.add(channel.key);
            nextStreamIndex.set(channel.key, channel.sourceUrl);
            channels.push(channel);
        }
    }

    if (successCount === 0) {
        if (playlistChannelCache.channels.length > 0) return playlistChannelCache.channels; // serve stale
        throw new HttpError(502, `All IPTV playlist sources failed${lastStatus ? ` (last status: ${lastStatus})` : ""}.`);
    }

    streamIndex.clear();
    for (const [key, sourceUrl] of nextStreamIndex) streamIndex.set(key, sourceUrl);
    playlistChannelCache.at = Date.now();
    playlistChannelCache.channels = channels;

    // Persist to disk so next restart is instant
    void saveDiskCache(PLAYLIST_DISK_CACHE_FILE, {
        at: playlistChannelCache.at,
        channels,
        streamIndex: [...nextStreamIndex.entries()],
    });

    buildSlugIndex(channels);
    console.log(`[cache] playlist channels refreshed: ${channels.length} channels`);
    return channels;
}

async function loadPlaylistChannels(env, force = false) {
    const now = Date.now();
    const ttlMs = envInt(env, "M3U_CHANNEL_CACHE_SECONDS", envInt(env, "CHANNEL_CACHE_SECONDS", 120)) * 1000;

    // ── INSTANT PATH: return whatever is in cache right now ──────────────────
    if (!force && playlistChannelCache.channels.length > 0) {
        if (now - playlistChannelCache.at >= ttlMs && !playlistChannelLoadPromise) {
            playlistChannelLoadPromise = doRefreshPlaylistChannels(env).finally(() => { playlistChannelLoadPromise = null; });
        }
        return playlistChannelCache.channels; // ← returns in <1ms
    }

    // ── COLD START: must wait once (disk was not pre-loaded yet) ─────────────
    if (!force && playlistChannelLoadPromise) return playlistChannelLoadPromise;
    playlistChannelLoadPromise = doRefreshPlaylistChannels(env).finally(() => { playlistChannelLoadPromise = null; });
    return playlistChannelLoadPromise;
}

async function getStreamForKey(key, env) {
    validateKey(key);
    const cachedSourceUrl = streamIndex.get(key);
    if (cachedSourceUrl) return { key, sourceUrl: cachedSourceUrl };
    throw new HttpError(410, "This legacy /live/{key} URL no longer resolves statelessly. Refresh /api/channels and use the returned url field.");
}

// Channel record / payload

function channelCacheSnapshot(hit) {
    return {
        hit,
        at: channelCache.at ? new Date(channelCache.at).toISOString() : null,
        age_seconds: channelCache.at ? Math.round((Date.now() - channelCache.at) / 100) / 10 : 0,
        count: channelCache.channels.length,
    };
}

function playlistCacheSnapshot(hit, entry) {
    return { hit, age_ms: entry ? Date.now() - entry.at : null };
}

function upstreamUrlCandidates(url, env) {
    const candidates = [url];
    const fallback = httpsFallbackCandidate(url, env);
    if (fallback && !candidates.includes(fallback)) candidates.push(fallback);
    return candidates;
}

// ─── FIXED: use AbortController + setTimeout instead of AbortSignal.timeout()
// AbortSignal.timeout() throws DOMException[TimeoutError] which leaks through
// try/catch boundaries in some Node 18 builds. A manual controller throws the
// ordinary AbortError which is caught reliably everywhere.
function timeoutSignal(timeoutMs) {
    // kept for API compatibility but no longer used internally
    return undefined;
}

async function fetchWithTimeout(url, init, timeoutMs) {
    if (!Number.isFinite(timeoutMs) || timeoutMs <= 0) {
        return fetch(url, init);
    }
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(), timeoutMs);
    try {
        return await fetch(url, { ...init, signal: controller.signal });
    } catch (error) {
        if (error?.name === "AbortError" || error?.name === "TimeoutError") {
            const e = new Error(`Upstream timed out after ${timeoutMs}ms: ${url}`);
            e.code = "TIMEOUT";
            throw e;
        }
        throw error;
    } finally {
        clearTimeout(timer);
    }
}

async function channelRecord(channel, request, env) {
    const base = publicBase(request, env);
    const cdn = streamBase(request, env);
    const sourceUrl = streamIndex.get(channel.key);
    const directToken = sourceUrl ? await makeUrlToken({ u: sourceUrl }, env) : null;
    const directUrl = directToken ? `${cdn}/direct/${directToken}.m3u8` : `${cdn}/live/${channel.key}/index.m3u8`;
    const liveUrl = directToken ? `${cdn}/live/${channel.key}/index.m3u8?src=${encodeURIComponent(directToken)}` : `${cdn}/live/${channel.key}/index.m3u8`;
    const slug = keyToSlugIndex.get(channel.key);
    const streamUrl = slug ? `${cdn}/stream/${encodePathSegment(slug)}.m3u8` : null;
    return {
        key: channel.key,
        name: channel.name,
        slug: slug || null,
        logo: channel.logo,
        category: channel.category,
        url: liveUrl,
        stream_url: streamUrl,
        m3u8: liveUrl,
        direct_url: directUrl,
        lookup_url: `${base}/live/${channel.key}/index.m3u8`,
    };
}

async function channelsPayload(request, env, force = false) {
    const url = new URL(request.url);
    const q = cleanString(url.searchParams.get("q"));

    let channels = await loadChannels(env, force);
    if (q) {
        channels = channels.filter((ch) => channelMatchesQuery(ch, q));
    }
    const hit = !force && channelCache.channels.length > 0 && Date.now() - channelCache.at < envInt(env, "CHANNEL_CACHE_SECONDS", 120) * 1000;
    const records = [];
    for (const channel of channels) records.push(await channelRecord(channel, request, env));
    return {
        status: "ok",
        count: records.length,
        cache: channelCacheSnapshot(hit),
        playlist_cache: playlistCacheSnapshot(false, null),
        worker_url: publicBase(request, env),
        channels: records,
    };
}

// Movie and TV series payloads

async function appendPlaylistMediaRecords(records, source, env, kind) {
    let response;
    try {
        response = await fetchProviderPlaylist(env, source.url);
    } catch {
        return { ok: false, status: "network error", count: 0 };
    }
    if (!response.ok) return { ok: false, status: response.status, count: 0 };

    const before = records.length;
    await parseM3uEntries(response, async (entry) => {
        if (entry.kind !== kind) return;
        records.push({
            source: source.label,
            type: kind === "series" ? "tvseries_episode" : "movie",
            key: entry.key,
            stream_id: entry.streamId,
            name: entry.name,
            logo: entry.logo,
            category: entry.category,
            url: entry.sourceUrl,
        });
    });
    return { ok: true, status: response.status, count: records.length - before };
}

async function moviesPayload(request, env, force = false) {
    const url = new URL(request.url);
    const sources = selectedPlaylistSources(env, url.searchParams.get("source"));
    const movies = [];
    const sourceResults = [];

    for (const source of sources) {
        const before = movies.length;
        const catalog = await loadXtreamCatalog(env, source, "movies", force).catch(() => null);
        if (catalog && catalog.items.length > 0) {
            for (const item of catalog.items) {
                const id = itemId(item, "movies");
                if (!id) continue;
                const extension = cleanString(item.container_extension, "mp4");
                movies.push({
                    source: source.label,
                    type: "movie",
                    stream_id: id,
                    name: cleanString(item.name, "Unknown"),
                    logo: mediaLogo(item),
                    category: catalogCategory(catalog, item),
                    category_id: cleanString(item.category_id),
                    url: xtreamMediaUrl(catalog.config, "movie", id, extension),
                    container_extension: extension,
                    rating: mediaRating(item),
                    added: cleanString(item.added) || null,
                });
            }
            sourceResults.push({ source: source.label, mode: "xtream", count: movies.length - before });
            continue;
        }

        const parsed = await appendPlaylistMediaRecords(movies, source, env, "movie");
        sourceResults.push({ source: source.label, mode: "playlist", count: parsed.count, ok: parsed.ok, status: parsed.status });
    }

    return {
        status: "ok",
        count: movies.length,
        worker_url: publicBase(request, env),
        sources: sourceResults,
        movies,
    };
}

function seriesRecordFromCatalogItem(item, catalog, source, request, env) {
    const id = itemId(item, "series");
    return {
        source: source.label,
        type: "tvseries",
        series_id: id,
        name: cleanString(item.name, "Unknown"),
        logo: mediaLogo(item),
        category: catalogCategory(catalog, item),
        category_id: cleanString(item.category_id),
        plot: cleanString(item.plot),
        genre: cleanString(item.genre),
        release_date: cleanString(item.releaseDate ?? item.release_date),
        rating: mediaRating(item),
        episodes_api_url: sourceApiUrl(request, env, "/api/tvseries", {
            source: source.label,
            series_id: id,
        }),
        upstream_details_url: xtreamApiUrl(catalog.config, "get_series_info", { series_id: id }).toString(),
    };
}

function directEpisodeUrl(config, episode) {
    const directSource = cleanString(episode?.direct_source);
    if (/^https?:\/\//i.test(directSource)) return directSource;
    const id = cleanString(episode?.id ?? episode?.stream_id);
    if (!id) return "";
    const extension = cleanString(episode?.container_extension ?? episode?.info?.container_extension, "mp4");
    return xtreamMediaUrl(config, "series", id, extension);
}

function flattenSeriesEpisodes(source, seriesId, infoEntry) {
    const episodes = [];
    const groups = infoEntry?.payload?.episodes;
    if (!groups || typeof groups !== "object") return episodes;

    const seasonKeys = Object.keys(groups).sort((a, b) => Number(a) - Number(b));
    for (const seasonKey of seasonKeys) {
        const seasonEpisodes = Array.isArray(groups[seasonKey]) ? groups[seasonKey] : [];
        for (const episode of seasonEpisodes) {
            const id = cleanString(episode?.id ?? episode?.stream_id);
            const url = directEpisodeUrl(infoEntry.config, episode);
            if (!id || !url) continue;
            const extension = cleanString(episode?.container_extension ?? episode?.info?.container_extension, "mp4");
            episodes.push({
                source: source.label,
                type: "tvseries_episode",
                series_id: cleanString(seriesId),
                episode_id: id,
                season: Number.isFinite(Number(seasonKey)) ? Number(seasonKey) : seasonKey,
                episode_num: episode?.episode_num ?? null,
                title: cleanString(episode?.title ?? episode?.name, `Episode ${episode?.episode_num ?? ""}`.trim()),
                url,
                container_extension: extension,
                added: cleanString(episode?.added) || null,
            });
        }
    }
    return episodes;
}

async function tvSeriesEpisodesPayload(request, env, seriesId, force = false) {
    const url = new URL(request.url);
    const sources = selectedPlaylistSources(env, url.searchParams.get("source"));
    const episodes = [];
    const sourceResults = [];

    for (const source of sources) {
        const infoEntry = await loadXtreamSeriesInfo(env, source, seriesId, force).catch(() => null);
        const sourceEpisodes = flattenSeriesEpisodes(source, seriesId, infoEntry);
        episodes.push(...sourceEpisodes);
        sourceResults.push({
            source: source.label,
            mode: "xtream",
            series_id: cleanString(seriesId),
            count: sourceEpisodes.length,
            ok: Boolean(infoEntry?.payload),
        });
    }

    return {
        status: "ok",
        count: episodes.length,
        worker_url: publicBase(request, env),
        sources: sourceResults,
        episodes,
    };
}

async function tvSeriesPayload(request, env, force = false) {
    const url = new URL(request.url);
    const seriesId = cleanString(url.searchParams.get("series_id") || url.searchParams.get("id"));
    if (seriesId) return tvSeriesEpisodesPayload(request, env, seriesId, force);

    const sources = selectedPlaylistSources(env, url.searchParams.get("source"));
    const series = [];
    const sourceResults = [];

    for (const source of sources) {
        const before = series.length;
        const catalog = await loadXtreamCatalog(env, source, "series", force).catch(() => null);
        if (catalog && catalog.items.length > 0) {
            for (const item of catalog.items) {
                const id = itemId(item, "series");
                if (!id) continue;
                series.push(seriesRecordFromCatalogItem(item, catalog, source, request, env));
            }
            sourceResults.push({ source: source.label, mode: "xtream", count: series.length - before });
            continue;
        }

        const parsed = await appendPlaylistMediaRecords(series, source, env, "series");
        sourceResults.push({ source: source.label, mode: "playlist", count: parsed.count, ok: parsed.ok, status: parsed.status });
    }

    return {
        status: "ok",
        count: series.length,
        worker_url: publicBase(request, env),
        sources: sourceResults,
        tvseries: series,
    };
}

function dashboardPage() {
    return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>IPTV Gateway - Admin Panel</title>
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=Outfit:wght@400;500;600;700&display=swap" rel="stylesheet">
  <script src="https://cdn.jsdelivr.net/npm/hls.js@latest"></script>
  <style>
    :root {
      --bg: #080a0f;
      --panel-bg: rgba(17, 22, 34, 0.7);
      --panel-border: rgba(255, 255, 255, 0.08);
      --panel-header: rgba(26, 33, 51, 0.85);
      --text-primary: #f3f4f6;
      --text-secondary: #9ca3af;
      --text-muted: #6b7280;
      --accent-gradient: linear-gradient(135deg, #6366f1 0%, #06b6d4 100%);
      --accent-color: #6366f1;
      --accent-hover: #4f46e5;
      --success-color: #10b981;
      --danger-color: #ef4444;
      --warning-color: #f59e0b;
      --input-bg: rgba(10, 12, 18, 0.8);
      --input-border: rgba(255, 255, 255, 0.08);
      --input-focus: #06b6d4;
      --font-sans: 'Outfit', 'Inter', system-ui, -apple-system, sans-serif;
    }
    
    * {
      box-sizing: border-box;
      margin: 0;
      padding: 0;
    }
    
    body {
      background: var(--bg);
      background-image: radial-gradient(circle at 10% 20%, rgba(99, 102, 241, 0.15) 0%, transparent 40%),
                        radial-gradient(circle at 90% 80%, rgba(6, 182, 212, 0.15) 0%, transparent 40%);
      color: var(--text-primary);
      font-family: var(--font-sans);
      min-height: 100vh;
      line-height: 1.5;
    }
    
    .container {
      width: min(1280px, calc(100% - 32px));
      margin: 0 auto;
      padding: 32px 0 60px;
    }
    
    /* Header */
    header {
      display: flex;
      justify-content: space-between;
      align-items: center;
      margin-bottom: 32px;
      flex-wrap: wrap;
      gap: 16px;
    }
    
    .logo-area h1 {
      font-size: 28px;
      font-weight: 700;
      letter-spacing: -0.02em;
      background: var(--accent-gradient);
      -webkit-background-clip: text;
      -webkit-text-fill-color: transparent;
      margin-bottom: 4px;
    }
    
    .logo-area p {
      color: var(--text-secondary);
      font-size: 14px;
    }
    
    .header-badge {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      background: rgba(99, 102, 241, 0.1);
      border: 1px solid rgba(99, 102, 241, 0.2);
      border-radius: 9999px;
      padding: 4px 12px;
      font-size: 12px;
      color: #818cf8;
      font-weight: 600;
    }
    
    /* Tabs */
    .tabs-wrapper {
      margin-bottom: 24px;
      border-bottom: 1px solid var(--panel-border);
      padding-bottom: 4px;
    }
    
    .tabs {
      display: flex;
      gap: 8px;
      overflow-x: auto;
      scrollbar-width: none;
    }
    
    .tabs::-webkit-scrollbar {
      display: none;
    }
    
    .tab {
      background: transparent;
      border: none;
      color: var(--text-secondary);
      padding: 12px 20px;
      font-size: 15px;
      font-weight: 500;
      cursor: pointer;
      border-radius: 8px 8px 0 0;
      display: flex;
      align-items: center;
      gap: 8px;
      transition: all 0.2s ease;
      position: relative;
    }
    
    .tab:hover {
      color: var(--text-primary);
      background: rgba(255, 255, 255, 0.03);
    }
    
    .tab.active {
      color: #fff;
      font-weight: 600;
    }
    
    .tab.active::after {
      content: '';
      position: absolute;
      bottom: -4px;
      left: 0;
      right: 0;
      height: 3px;
      background: var(--accent-gradient);
      border-radius: 9999px;
      box-shadow: 0 -2px 10px rgba(6, 182, 212, 0.5);
    }
    
    /* Grid & Panels */
    .grid {
      display: grid;
      grid-template-columns: 1fr;
      gap: 24px;
    }
    
    @media (min-width: 1024px) {
      .grid.two-cols {
        grid-template-columns: minmax(360px, 450px) 1fr;
      }
    }
    
    .card {
      background: var(--panel-bg);
      backdrop-filter: blur(16px);
      -webkit-backdrop-filter: blur(16px);
      border: 1px solid var(--panel-border);
      border-radius: 12px;
      box-shadow: 0 10px 30px rgba(0, 0, 0, 0.2);
      overflow: hidden;
      display: flex;
      flex-direction: column;
    }
    
    .card-header {
      background: var(--panel-header);
      padding: 16px 20px;
      border-bottom: 1px solid var(--panel-border);
      display: flex;
      justify-content: space-between;
      align-items: center;
    }
    
    .card-header h2 {
      font-size: 16px;
      font-weight: 600;
      color: var(--text-primary);
      display: flex;
      align-items: center;
      gap: 8px;
    }
    
    .card-body {
      padding: 20px;
      flex: 1;
    }
    
    /* Forms & Inputs */
    .form-group {
      margin-bottom: 16px;
      display: flex;
      flex-direction: column;
      gap: 6px;
    }
    
    .form-group label {
      font-size: 13px;
      font-weight: 500;
      color: var(--text-secondary);
    }
    
    input, select, textarea {
      width: 100%;
      background: var(--input-bg);
      border: 1px solid var(--input-border);
      color: var(--text-primary);
      padding: 10px 14px;
      border-radius: 8px;
      font-family: var(--font-sans);
      font-size: 14px;
      outline: none;
      transition: all 0.2s ease;
    }
    
    input:focus, select:focus, textarea:focus {
      border-color: var(--input-focus);
      box-shadow: 0 0 0 2px rgba(6, 182, 212, 0.15);
    }
    
    .form-row {
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 12px;
    }
    
    .checkbox-group {
      display: flex;
      flex-direction: column;
      gap: 10px;
      margin: 8px 0 16px;
    }
    
    .checkbox-label {
      display: flex;
      align-items: center;
      gap: 8px;
      font-size: 13.5px;
      color: var(--text-secondary);
      cursor: pointer;
    }
    
    .checkbox-label input[type="checkbox"] {
      width: 18px;
      height: 18px;
      cursor: pointer;
    }
    
    /* Buttons */
    .btn {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      gap: 8px;
      padding: 10px 16px;
      border-radius: 8px;
      font-family: var(--font-sans);
      font-weight: 600;
      font-size: 14px;
      cursor: pointer;
      transition: all 0.2s ease;
      border: none;
      text-decoration: none;
    }
    
    .btn-primary {
      background: var(--accent-gradient);
      color: #fff;
      box-shadow: 0 4px 14px rgba(99, 102, 241, 0.35);
    }
    
    .btn-primary:hover {
      opacity: 0.95;
      transform: translateY(-1px);
      box-shadow: 0 6px 18px rgba(99, 102, 241, 0.45);
    }
    
    .btn-secondary {
      background: rgba(255, 255, 255, 0.05);
      border: 1px solid var(--panel-border);
      color: var(--text-primary);
    }
    
    .btn-secondary:hover {
      background: rgba(255, 255, 255, 0.08);
      transform: translateY(-1px);
    }
    
    .btn-danger {
      background: rgba(239, 68, 68, 0.1);
      border: 1px solid rgba(239, 68, 68, 0.2);
      color: var(--danger-color);
    }
    
    .btn-danger:hover {
      background: rgba(239, 68, 68, 0.18);
      transform: translateY(-1px);
    }
    
    .btn-success {
      background: rgba(16, 185, 129, 0.1);
      border: 1px solid rgba(16, 185, 129, 0.2);
      color: var(--success-color);
    }
    
    .btn-success:hover {
      background: rgba(16, 185, 129, 0.18);
      transform: translateY(-1px);
    }
    
    .btn-sm {
      padding: 6px 12px;
      font-size: 12px;
      border-radius: 6px;
    }
    
    /* Lists and Tables */
    .table-container {
      overflow-x: auto;
    }
    
    table {
      width: 100%;
      border-collapse: collapse;
      text-align: left;
    }
    
    th, td {
      padding: 12px 16px;
      border-bottom: 1px solid var(--panel-border);
      font-size: 14px;
      vertical-align: middle;
    }
    
    th {
      font-weight: 600;
      color: var(--text-secondary);
      background: rgba(0, 0, 0, 0.1);
    }
    
    tr:hover td {
      background: rgba(255, 255, 255, 0.01);
    }
    
    /* Pills & Badges */
    .pill {
      display: inline-flex;
      align-items: center;
      padding: 2px 8px;
      border-radius: 9999px;
      font-size: 11px;
      font-weight: 600;
      border: 1px solid rgba(255,255,255,0.1);
      background: rgba(255, 255, 255, 0.03);
      color: var(--text-secondary);
    }
    
    .status-badge {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      font-size: 11.5px;
      font-weight: 600;
      padding: 2px 8px;
      border-radius: 6px;
    }
    
    .status-badge.active {
      background: rgba(16, 185, 129, 0.1);
      color: var(--success-color);
      border: 1px solid rgba(16, 185, 129, 0.2);
    }
    
    .status-badge.disabled {
      background: rgba(239, 68, 68, 0.1);
      color: var(--danger-color);
      border: 1px solid rgba(239, 68, 68, 0.2);
    }
    
    .status-dot {
      width: 8px;
      height: 8px;
      border-radius: 50%;
      display: inline-block;
    }
    
    .status-dot.green { background-color: var(--success-color); box-shadow: 0 0 8px var(--success-color); }
    .status-dot.red { background-color: var(--danger-color); box-shadow: 0 0 8px var(--danger-color); }
    .status-dot.orange { background-color: var(--warning-color); box-shadow: 0 0 8px var(--warning-color); }
    
    /* Toast notifications */
    #toast-container {
      position: fixed;
      bottom: 24px;
      right: 24px;
      z-index: 1000;
      display: flex;
      flex-direction: column;
      gap: 10px;
      max-width: 380px;
    }
    
    .toast {
      background: rgba(17, 24, 39, 0.95);
      border: 1px solid var(--panel-border);
      padding: 14px 18px;
      border-radius: 8px;
      color: #fff;
      font-size: 13.5px;
      box-shadow: 0 10px 25px rgba(0,0,0,0.5);
      display: flex;
      align-items: center;
      gap: 10px;
      transform: translateY(20px);
      opacity: 0;
      animation: toastIn 0.3s forwards;
      backdrop-filter: blur(10px);
    }
    
    @keyframes toastIn {
      to { transform: translateY(0); opacity: 1; }
    }
    
    .toast.success { border-left: 4px solid var(--success-color); }
    .toast.error { border-left: 4px solid var(--danger-color); }
    .toast.info { border-left: 4px solid var(--accent-color); }
    
    /* Tab Contents */
    .tab-content {
      display: none;
    }
    
    .tab-content.active {
      display: block;
    }
    
    /* Overview widgets */
    .stats-grid {
      display: grid;
      grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
      gap: 16px;
      margin-bottom: 24px;
    }
    
    .stat-card {
      background: rgba(255, 255, 255, 0.02);
      border: 1px solid var(--panel-border);
      padding: 20px;
      border-radius: 10px;
    }
    
    .stat-label {
      font-size: 13px;
      color: var(--text-secondary);
      margin-bottom: 4px;
    }
    
    .stat-value {
      font-size: 24px;
      font-weight: 700;
      background: var(--accent-gradient);
      -webkit-background-clip: text;
      -webkit-text-fill-color: transparent;
    }
    
    /* Draggable lists */
    .draggable-list {
      display: flex;
      flex-direction: column;
      gap: 8px;
      max-height: 400px;
      overflow-y: auto;
    }
    
    .draggable-item {
      display: flex;
      align-items: center;
      padding: 10px 14px;
      background: rgba(255, 255, 255, 0.02);
      border: 1px solid var(--panel-border);
      border-radius: 8px;
      cursor: grab;
      user-select: none;
    }
    
    .draggable-item:active {
      cursor: grabbing;
      background: rgba(255, 255, 255, 0.05);
    }
    
    .draggable-item.active {
      border-color: var(--accent-color);
      background: rgba(99, 102, 241, 0.05);
    }
    
    .drag-handle {
      margin-right: 12px;
      color: var(--text-muted);
      font-size: 16px;
    }
    
    .item-content {
      flex: 1;
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
    }
    
    .item-content strong {
      font-weight: 600;
    }
    
    .item-actions {
      display: flex;
      gap: 6px;
    }
    
    /* Channel items list */
    .channel-picker-list {
      max-height: 320px;
      overflow-y: auto;
      border: 1px solid var(--panel-border);
      border-radius: 8px;
      background: rgba(0,0,0,0.1);
    }
    
    .channel-row {
      display: flex;
      align-items: center;
      padding: 8px 12px;
      border-bottom: 1px solid var(--panel-border);
      font-size: 13px;
    }
    
    .channel-row:last-child {
      border-bottom: none;
    }
    
    .channel-row input[type="checkbox"] {
      width: 16px;
      height: 16px;
      margin-right: 12px;
      cursor: pointer;
    }
    
    .channel-info {
      display: flex;
      flex-direction: column;
      flex: 1;
      overflow: hidden;
    }
    
    .channel-name {
      font-weight: 500;
      color: var(--text-primary);
      text-overflow: ellipsis;
      overflow: hidden;
      white-space: nowrap;
    }
    
    .channel-category {
      font-size: 11px;
      color: var(--text-secondary);
    }
    
    .search-box {
      position: relative;
      margin-bottom: 12px;
    }
    
    .search-box input {
      padding-left: 36px;
    }
    
    .search-icon {
      position: absolute;
      left: 12px;
      top: 50%;
      transform: translateY(-50%);
      color: var(--text-muted);
      pointer-events: none;
    }
    
    /* Autocomplete list */
    .autocomplete-list {
      position: absolute;
      top: 100%;
      left: 0;
      right: 0;
      background: #111520;
      border: 1px solid var(--panel-border);
      border-top: none;
      border-radius: 0 0 8px 8px;
      z-index: 50;
      max-height: 250px;
      overflow-y: auto;
      box-shadow: 0 10px 25px rgba(0,0,0,0.5);
    }
    
    .autocomplete-item {
      padding: 8px 14px;
      cursor: pointer;
      display: flex;
      justify-content: space-between;
      align-items: center;
      font-size: 13px;
      border-bottom: 1px solid rgba(255,255,255,0.03);
    }
    
    .autocomplete-item:hover {
      background: rgba(255,255,255,0.05);
    }
    
    .autocomplete-item span {
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
    }
    
    /* Health lists */
    .health-list {
      display: flex;
      flex-direction: column;
      gap: 10px;
    }
    
    .health-item {
      background: rgba(255,255,255,0.02);
      border: 1px solid var(--panel-border);
      border-radius: 8px;
      padding: 12px 16px;
      font-size: 13px;
    }
    
    .health-row {
      display: flex;
      justify-content: space-between;
      margin-bottom: 4px;
    }
    
    .health-label {
      color: var(--text-secondary);
    }
    
    .health-val {
      font-weight: 500;
    }
    
    /* Copy field wrapper */
    .copy-field {
      display: flex;
      background: var(--input-bg);
      border: 1px solid var(--input-border);
      border-radius: 6px;
      overflow: hidden;
      font-size: 12.5px;
      margin-bottom: 8px;
    }
    
    .copy-text {
      padding: 8px 12px;
      flex: 1;
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
      color: #92e6d5;
      font-family: monospace;
    }
    
    .copy-btn {
      background: rgba(255,255,255,0.05);
      border: none;
      border-left: 1px solid var(--panel-border);
      color: var(--text-primary);
      padding: 0 12px;
      cursor: pointer;
      font-weight: 600;
      font-size: 11px;
    }
    
    .copy-btn:hover {
      background: rgba(255,255,255,0.1);
    }
  </style>
</head>
<body>
  <div class="container">
    <header>
      <div class="logo-area">
        <h1>IPTV Gateway</h1>
        <p>Zero-Lag Stream Proxy & XTREAM Endpoint Manager</p>
      </div>
      <div class="header-badge">
        <span class="status-dot green"></span> Connected to Hugging Face Edge
      </div>
    </header>
    
    <div class="tabs-wrapper">
      <div class="tabs">
        <button class="tab active" onclick="switchTab('overview')">📊 Overview & Health</button>
        <button class="tab" onclick="switchTab('providers')">🔌 Providers</button>
        <button class="tab" onclick="switchTab('categories')">📁 Categories</button>
        <button class="tab" onclick="switchTab('channels')">📺 Channels Browser</button>
        <button class="tab" onclick="switchTab('users')">👥 Access Users</button>
        <button class="tab" onclick="switchTab('playlists')">📄 Custom Playlists</button>
      </div>
    </div>
    
    <!-- Toast notifications container -->
    <div id="toast-container"></div>
    
    <!-- Tab 1: Overview & Health -->
    <div id="tab-overview" class="tab-content active">
      <div class="stats-grid">
        <div class="stat-card">
          <div class="stat-label">System Uptime</div>
          <div class="stat-value" id="stat-uptime">0s</div>
        </div>
        <div class="stat-card">
          <div class="stat-label">Total Requests</div>
          <div class="stat-value" id="stat-requests">0</div>
        </div>
        <div class="stat-card">
          <div class="stat-label">Segment Cache Hit Rate</div>
          <div class="stat-value" id="stat-hitrate">0%</div>
        </div>
        <div class="stat-card">
          <div class="stat-label">Heap Memory Usage</div>
          <div class="stat-value" id="stat-memory">0 MB</div>
        </div>
        <div class="stat-card">
          <div class="stat-label">🐰 Bunny CDN Pull Zones</div>
          <div class="stat-value" id="stat-bunny">—</div>
        </div>
      </div>
      
      <div class="grid two-cols">
        <div class="card">
          <div class="card-header">
            <h2>🚨 Circuit Breakers</h2>
          </div>
          <div class="card-body">
            <div id="health-circuits" class="health-list">
              <div class="empty" style="color:var(--text-muted)">All upstream channels operating normally.</div>
            </div>
          </div>
        </div>
        
        <div class="card">
          <div class="card-header">
            <h2>📈 Upstream Health Stats</h2>
          </div>
          <div class="card-body">
            <div id="health-upstreams" class="health-list">
              <div class="empty" style="color:var(--text-muted)">Loading stats...</div>
            </div>
          </div>
        </div>
      </div>
    </div>
    
    <!-- Tab 2: Providers -->
    <div id="tab-providers" class="tab-content">
      <div class="grid two-cols">
        <div class="card">
          <div class="card-header">
            <h2 id="provider-form-title">🔌 Add IPTV Provider</h2>
          </div>
          <div class="card-body">
            <form id="provider-form" onsubmit="saveProvider(event)">
              <input type="hidden" id="prov-id">
              <div class="form-group">
                <label>Provider Name</label>
                <input id="prov-name" placeholder="e.g. My Premium IPTV" required autocomplete="off">
              </div>
              <div class="form-group">
                <label>Server Base URL (Xtream Codes Host)</label>
                <input id="prov-url" placeholder="http://iptv-provider.link:8080" required autocomplete="off">
              </div>
              <div class="form-group">
                <label>Username</label>
                <input id="prov-user" placeholder="Your Xtream Username" required autocomplete="off">
              </div>
              <div class="form-group">
                <label>Password</label>
                <input id="prov-pass" type="password" placeholder="Your Xtream Password" required autocomplete="off">
              </div>
              <div style="display:flex; gap:10px; margin-top:20px;">
                <button type="submit" class="btn btn-primary" style="flex:1;">Save Server</button>
                <button type="button" onclick="testProviderConnection()" class="btn btn-secondary">⚡ Test</button>
                <button type="button" onclick="resetProviderForm()" class="btn btn-secondary" id="prov-cancel" style="display:none;">Cancel</button>
              </div>
            </form>
          </div>
        </div>
        
        <div class="card">
          <div class="card-header">
            <h2>🔌 Configured IPTV Providers</h2>
          </div>
          <div class="card-body">
            <div class="table-container">
              <table>
                <thead>
                  <tr>
                    <th>Server</th>
                    <th>Url</th>
                    <th>Status</th>
                    <th>Actions</th>
                  </tr>
                </thead>
                <tbody id="providers-list">
                  <!-- Dynamic server list -->
                </tbody>
              </table>
            </div>
            <div id="env-sources-wrapper" style="margin-top: 24px; padding-top: 16px; border-top: 1px solid var(--panel-border)">
              <h3 style="font-size: 13px; color: var(--text-secondary); margin-bottom: 8px">Environment Variables (Fallback)</h3>
              <div id="env-sources-list" style="display:flex; flex-direction:column; gap:6px"></div>
            </div>
          </div>
        </div>
      </div>
    </div>
    
    <!-- Tab 3: Categories -->
    <div id="tab-categories" class="tab-content">
      <div class="grid two-cols">
        <div class="card">
          <div class="card-header">
            <h2>📁 Categories (Drag to Reorder)</h2>
          </div>
          <div class="card-body">
            <div style="display:flex; gap:10px; margin-bottom:16px;">
              <input id="new-cat-name" placeholder="New Category Name" autocomplete="off" style="flex:1">
              <button type="button" class="btn btn-primary" onclick="addCategory()">Add</button>
            </div>
            <div class="draggable-list" id="categories-list">
              <!-- Draggable categories list -->
            </div>
            <div style="margin-top:16px; display:flex; flex-direction:column; gap:8px;">
              <button class="btn btn-secondary" onclick="autoImportCategories()">⚡ Auto-Import From Upstream Channels</button>
              <div style="display:flex; gap:10px;">
                <button class="btn btn-secondary" style="flex:1" onclick="exportCategories()">Export JSON</button>
                <button class="btn btn-secondary" style="flex:1" onclick="toggleImportArea('cat')">Import JSON</button>
              </div>
              <div class="import-area" id="import-cat-area" style="display:none; margin-top:8px">
                <textarea id="import-cat-json" placeholder="Paste exported categories JSON here..." style="min-height:90px"></textarea>
                <button type="button" class="btn btn-primary btn-sm" style="width:100%; margin-top:8px" onclick="doImportCategories()">Apply Import</button>
              </div>
              <button class="btn btn-success" style="margin-top:8px" onclick="saveCategories()">💾 Save Categories & Order</button>
            </div>
          </div>
        </div>
        
        <div class="card">
          <div class="card-header">
            <h2>📁 Category Channels <span id="active-cat-title" style="font-weight:normal; color:var(--text-secondary)"></span></h2>
          </div>
          <div class="card-body">
            <div id="cat-channels-empty" class="empty">
              Select a category on the left to view and manage assigned channels.
            </div>
            <div id="cat-channels-panel" style="display:none">
              <div class="search-box" style="position:relative">
                <span class="search-icon">&#128269;</span>
                <input id="cat-ch-search" placeholder="Type channel name to search & add..." autocomplete="off">
                <div class="autocomplete-list" id="cat-ch-autocomplete" style="display:none"></div>
              </div>
              
              <div style="display:flex; justify-content:space-between; align-items:center; margin:14px 0 8px; font-size:13px; color:var(--text-secondary)">
                <span>Assigned Channels (Drag to sort): <strong id="cat-ch-count">0</strong></span>
                <button class="btn btn-danger btn-sm" onclick="clearActiveCategoryChannels()">Clear All</button>
              </div>
              
              <div class="draggable-list" id="active-cat-ch-list" style="max-height: 420px;">
                <!-- Drag to reorder category channels -->
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
    
    <!-- Tab 4: Channel Browser -->
    <div id="tab-channels" class="tab-content">
      <div class="grid two-cols">
        <div class="card">
          <div class="card-header">
            <h2>📺 Live Channels List</h2>
          </div>
          <div class="card-body" style="display:flex; flex-direction:column; gap:12px;">
            <div style="display:flex; gap:10px;">
              <div class="search-box" style="flex:2; margin-bottom:0">
                <span class="search-icon">&#128269;</span>
                <input id="global-ch-search" oninput="renderChannelsBrowser()" placeholder="Search channels..." autocomplete="off">
              </div>
              <select id="global-ch-filter" onchange="renderChannelsBrowser()" style="flex:1;">
                <option value="">All Categories</option>
              </select>
            </div>
            <div style="font-size:12px; color:var(--text-secondary); display:flex; justify-content:space-between; align-items:center;">
              <span id="browser-ch-count">0 channels</span>
              <div>
                <button class="btn btn-secondary btn-sm" style="padding: 2px 6px" onclick="toggleAllBrowserCheckboxes(true)">Select All</button>
                <button class="btn btn-secondary btn-sm" style="padding: 2px 6px" onclick="toggleAllBrowserCheckboxes(false)">Clear Selection</button>
              </div>
            </div>
            <div class="channel-picker-list" id="browser-channels-list" style="max-height: 480px;">
              <!-- Channels Browser rows -->
            </div>
            <div id="browser-bulk-ops" style="border-top:1px solid var(--panel-border); padding-top:12px; display:flex; gap:10px; align-items:center;">
              <span style="font-size:13px; color:var(--text-secondary);"><strong id="browser-selected-count">0</strong> selected</span>
              <select id="bulk-cat-select" style="flex:1; padding:6px 10px;">
                <option value="">Move to Custom Category...</option>
              </select>
              <button class="btn btn-primary btn-sm" onclick="bulkAssignChannels()">Apply</button>
            </div>
          </div>
        </div>
        
        <div class="card">
          <div class="card-header">
            <h2>📺 Live Stream Preview Player</h2>
          </div>
          <div class="card-body" style="display:flex; flex-direction:column; align-items:center; justify-content:center; min-height: 300px;">
            <div class="channel-preview-container" style="width:100%; text-align:center;">
              <video id="video-player" controls autoplay style="width:100%; border-radius:10px; border:1px solid var(--panel-border); background:#000; aspect-ratio: 16/9; display:none;"></video>
              <div id="player-status" style="color:var(--text-secondary); text-align:center; padding: 40px; font-size:14px; border:1px dashed var(--panel-border); border-radius:10px; width:100%;">
                Select a channel and click preview to load stream. Ensure CORS restrictions allow player load, or play on TV.
              </div>
              <h3 id="preview-ch-name" style="margin-top:12px; font-size:16px; font-weight:600; text-align:left; display:none">Channel</h3>
              <p id="preview-ch-url" style="color:var(--text-secondary); font-size:12px; text-align:left; display:none; word-break:break-all; font-family:monospace; margin-top:4px"></p>
            </div>
          </div>
        </div>
      </div>
    </div>
    
    <!-- Tab 5: Access Users -->
    <div id="tab-users" class="tab-content">
      <div class="grid two-cols">
        <div class="card">
          <div class="card-header">
            <h2>👥 Create Access User</h2>
          </div>
          <div class="card-body">
            <form id="create-user-form" onsubmit="createUser(event)">
              <div class="form-group">
                <label>Username</label>
                <input name="username" autocomplete="off" required>
              </div>
              <div class="form-group">
                <label>Password</label>
                <div style="display:flex; gap:10px;">
                  <input name="password" autocomplete="off" required style="flex:1">
                  <button class="btn btn-secondary" type="button" onclick="generateRandomPass()">Generate</button>
                </div>
              </div>
              <div class="form-group">
                <label>Expiry Period</label>
                <select name="duration">
                  <option value="1m">1 Month</option>
                  <option value="3m">3 Months</option>
                  <option value="12m">12 Months</option>
                  <option value="infinite" selected>Infinite</option>
                </select>
              </div>
              <div class="checkbox-group">
                <label class="checkbox-label"><input type="checkbox" name="include_live" checked> Expose Live Channels</label>
                <label class="checkbox-label"><input type="checkbox" name="include_movies"> Expose VOD Movies (Direct URLs)</label>
                <label class="checkbox-label"><input type="checkbox" name="include_series"> Expose TV Series (Direct URLs)</label>
              </div>
              <button type="submit" class="btn btn-primary" style="width:100%; margin-top:8px">Create User & M3U Link</button>
            </form>
          </div>
        </div>
        
        <div class="card">
          <div class="card-header">
            <h2>👥 Active Access Users</h2>
          </div>
          <div class="card-body">
            <div id="users-list-wrapper" class="table-container">
              <!-- Users list -->
            </div>
          </div>
        </div>
      </div>
    </div>
    
    <!-- Tab 6: Custom Playlists -->
    <div id="tab-playlists" class="tab-content">
      <div class="grid two-cols">
        <div class="card">
          <div class="card-header">
            <h2>📄 Create Custom Playlist</h2>
          </div>
          <div class="card-body">
            <div class="form-group">
              <label>Playlist Name</label>
              <input id="pl-name" placeholder="e.g. My Favorite Sports" autocomplete="off">
            </div>
            <div class="search-box">
              <span class="search-icon">&#128269;</span>
              <input id="pl-ch-search" oninput="renderPlaylistChannelPicker()" placeholder="Search channels..." autocomplete="off">
            </div>
            <div style="display:flex; justify-content:space-between; font-size:12.5px; color:var(--text-secondary); margin-bottom:8px">
              <span id="pl-selected-count">0 channels selected</span>
              <div>
                <button class="btn btn-secondary btn-sm" style="padding:2px 6px" onclick="toggleAllPlCheckboxes(true)">Select All</button>
                <button class="btn btn-secondary btn-sm" style="padding:2px 6px" onclick="toggleAllPlCheckboxes(false)">Clear</button>
              </div>
            </div>
            <div class="channel-picker-list" id="pl-channels-list" style="max-height: 280px">
              <!-- Playlist Channels picker -->
            </div>
            <button class="btn btn-primary" style="width:100%; margin-top:16px" onclick="createPlaylist()">Create Playlist</button>
          </div>
        </div>
        
        <div class="card">
          <div class="card-header">
            <h2>📄 Your Custom Playlists</h2>
          </div>
          <div class="card-body">
            <div id="playlists-list" style="display:flex; flex-direction:column; gap:16px;">
              <!-- Playlists card list -->
            </div>
            
            <div style="margin-top: 24px; padding-top: 16px; border-top:1px solid var(--panel-border); display:flex; flex-direction:column; gap:8px;">
              <div style="display:flex; gap:10px;">
                <button class="btn btn-secondary" style="flex:1" onclick="exportPlaylists()">Export Playlists</button>
                <button class="btn btn-secondary" style="flex:1" onclick="toggleImportArea('pl')">Import Playlists</button>
              </div>
              <div class="import-area" id="import-pl-area" style="display:none; margin-top:8px">
                <textarea id="import-pl-json" placeholder="Paste exported playlists JSON here..." style="min-height:90px"></textarea>
                <button type="button" class="btn btn-primary btn-sm" style="width:100%; margin-top:8px" onclick="doImportPlaylists()">Apply Import</button>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>

  <script>
    // Global State
    let allChannels = [];
    let customCategories = [];
    let customServers = [];
    let activeCategoryId = null;
    let selectedBrowserKeys = new Set();
    let selectedPlaylistKeys = new Set();
    let userFormPassword = document.querySelector("#create-user-form input[name='password']");
    let hlsPlayerInstance = null;

    // Toast Notification helper
    function showToast(text, type = "success") {
      const container = document.getElementById("toast-container");
      const toast = document.createElement("div");
      toast.className = \`toast \${type}\`;
      toast.textContent = text;
      container.appendChild(toast);
      
      setTimeout(() => {
        toast.style.animation = "none";
        toast.style.opacity = "1";
        setTimeout(() => {
          toast.remove();
        }, 300);
      }, 3000);
    }

    // Switch Tabs
    function switchTab(tabId) {
      document.querySelectorAll(".tab").forEach(t => t.classList.remove("active"));
      document.querySelectorAll(".tab-content").forEach(c => c.classList.remove("active"));
      
      // Find matching button
      const btn = Array.from(document.querySelectorAll(".tab")).find(t => t.getAttribute("onclick").includes(tabId));
      if (btn) btn.classList.add("active");
      
      const content = document.getElementById("tab-" + tabId);
      if (content) content.classList.add("active");
      
      if (tabId === "overview") fetchHealthStats();
    }

    // Generate random credential string
    function randomString(length = 14) {
      const alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789";
      const bytes = new Uint8Array(length);
      crypto.getRandomValues(bytes);
      return Array.from(bytes, byte => alphabet[byte % alphabet.length]).join("");
    }

    function generateRandomPass() {
      userFormPassword.value = randomString();
      userFormPassword.focus();
    }

    // ─── Phase 2: Providers ───
    async function loadProviders() {
      try {
        const res = await fetch("/api/servers");
        if (!res.ok) throw new Error("Could not load providers");
        const data = await res.json();
        customServers = data.custom_servers || [];
        renderProvidersList(customServers, data.env_sources || []);
      } catch (err) {
        showToast("Error loading providers: " + err.message, "error");
      }
    }

    function renderProvidersList(servers, envSources) {
      const listEl = document.getElementById("providers-list");
      listEl.innerHTML = "";
      if (servers.length === 0) {
        listEl.innerHTML = '<tr><td colspan="4" style="text-align:center;color:var(--text-secondary)">No custom servers added. Add one on the left.</td></tr>';
      } else {
        servers.forEach(s => {
          const tr = document.createElement("tr");
          tr.innerHTML = \`
            <td><strong>\${s.name}</strong>\${s.enabled ? "" : " <small style='color:var(--danger-color)'>(Disabled)</small>"}</td>
            <td><code>\${s.url}</code></td>
            <td><span class="status-badge \text-badge \${s.enabled ? 'active' : 'disabled'}">\${s.enabled ? 'Enabled' : 'Disabled'}</span></td>
            <td>
              <button class="btn btn-secondary btn-sm" onclick="editProvider('\${s.id}')">Edit</button>
              <button class="btn btn-danger btn-sm" onclick="deleteProvider('\${s.id}')">Delete</button>
            </td>
          \`;
          
          // Fix: replace the nested span class for correct styling
          tr.querySelector(".status-badge").className = "status-badge " + (s.enabled ? "active" : "disabled");
          listEl.appendChild(tr);
        });
      }

      const envListEl = document.getElementById("env-sources-list");
      envListEl.innerHTML = "";
      if (envSources.length === 0) {
        envListEl.innerHTML = '<div style="font-size:12px;color:var(--text-muted)">No environment servers loaded.</div>';
      } else {
        envSources.forEach(s => {
          const div = document.createElement("div");
          div.style.cssText = "display:flex;justify-content:space-between;background:rgba(255,255,255,0.01);padding:6px 10px;border-radius:6px;font-size:12px";
          div.innerHTML = \`<span>🔌 <strong>\${s.label}</strong></span> <code style="color:var(--text-secondary)">\${s.url_masked}</code>\`;
          envListEl.appendChild(div);
        });
      }
    }

    function editProvider(id) {
      const s = customServers.find(x => x.id === id);
      if (!s) return;
      document.getElementById("prov-id").value = s.id;
      document.getElementById("prov-name").value = s.name;
      document.getElementById("prov-url").value = s.url;
      document.getElementById("prov-user").value = s.username;
      document.getElementById("prov-pass").value = "";
      document.getElementById("prov-pass").required = false; // password is optional on update
      document.getElementById("prov-pass").placeholder = "Leave blank to keep existing password";
      document.getElementById("provider-form-title").textContent = "🔌 Edit IPTV Provider";
      document.getElementById("prov-cancel").style.display = "block";
    }

    function resetProviderForm() {
      document.getElementById("prov-id").value = "";
      document.getElementById("prov-name").value = "";
      document.getElementById("prov-url").value = "";
      document.getElementById("prov-user").value = "";
      document.getElementById("prov-pass").value = "";
      document.getElementById("prov-pass").required = true;
      document.getElementById("prov-pass").placeholder = "Your Xtream Password";
      document.getElementById("provider-form-title").textContent = "🔌 Add IPTV Provider";
      document.getElementById("prov-cancel").style.display = "none";
    }

    async function saveProvider(event) {
      event.preventDefault();
      const id = document.getElementById("prov-id").value;
      const name = document.getElementById("prov-name").value.trim();
      const url = document.getElementById("prov-url").value.trim();
      const username = document.getElementById("prov-user").value.trim();
      const password = document.getElementById("prov-pass").value.trim();

      const path = id ? "/api/servers/update" : "/api/servers";
      const payload = { id, name, url, username };
      if (password) payload.password = password;

      try {
        const res = await fetch(path, {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify(payload)
        });
        const result = await res.json();
        if (!res.ok) throw new Error(result.error || "Save failed");
        showToast(id ? "Provider updated!" : "Provider added!");
        resetProviderForm();
        await loadProviders();
        await loadAllChannels();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    async function deleteProvider(id) {
      if (!confirm("Are you sure you want to delete this provider? This will remove all channels imported from it.")) return;
      try {
        const res = await fetch("/api/servers/delete", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ id })
        });
        if (!res.ok) throw new Error("Delete failed");
        showToast("Provider deleted");
        await loadProviders();
        await loadAllChannels();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    async function testProviderConnection() {
      const url = document.getElementById("prov-url").value.trim();
      const username = document.getElementById("prov-user").value.trim();
      const password = document.getElementById("prov-pass").value.trim();
      if (!url || !username) {
        showToast("URL and username are required to test.", "error");
        return;
      }
      showToast("Testing connection to " + url + "...", "info");
      try {
        const res = await fetch("/api/servers/test", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ url, username, password })
        });
        const data = await res.json();
        if (data.connected) {
          showToast(\`Connected successfully! Expiry: \${data.user_info.exp_date ? new Date(data.user_info.exp_date * 1000).toLocaleDateString() : "Unlimited"}, Max Connections: \${data.user_info.max_connections || 0}\`);
        } else {
          showToast("Connection failed: " + (data.error || "Authentication failed"), "error");
        }
      } catch (err) {
        showToast("Test request failed: " + err.message, "error");
      }
    }

    // ─── Phase 2 & 3: Overview Health & Stats ───
    async function fetchHealthStats() {
      try {
        const res = await fetch("/api/health");
        if (!res.ok) return;
        const data = await res.json();
        
        // Populate stats
        document.getElementById("stat-uptime").textContent = formatUptime(data.uptime_seconds);
        document.getElementById("stat-requests").textContent = data.requests.total;
        const cacheTotal = data.requests.segment_cache_hits + data.requests.segment_cache_misses;
        const hitrate = cacheTotal > 0 ? Math.round((data.requests.segment_cache_hits / cacheTotal) * 100) : 0;
        document.getElementById("stat-hitrate").textContent = hitrate + "% (" + data.requests.segment_cache_hits + "/" + cacheTotal + ")";
        document.getElementById("stat-memory").textContent = data.memory.heap_used_mb + " MB / " + data.memory.heap_total_mb + " MB";

        // Bunny CDN stat
        const bunnyEl = document.getElementById("stat-bunny");
        if (bunnyEl && data.bunny_cdn) {
          if (data.bunny_cdn.enabled) {
            bunnyEl.textContent = data.bunny_cdn.pull_zones_count + " Active";
            bunnyEl.style.background = "linear-gradient(135deg, #f97316 0%, #eab308 100%)";
            bunnyEl.style.webkitBackgroundClip = "text";
            bunnyEl.style.webkitTextFillColor = "transparent";
          } else {
            bunnyEl.textContent = "Disabled";
            bunnyEl.style.background = "none";
            bunnyEl.style.webkitTextFillColor = "var(--text-muted)";
          }
        }

        // Circuit breakers list
        const circuitsEl = document.getElementById("health-circuits");
        circuitsEl.innerHTML = "";
        if (!data.circuit_breakers || data.circuit_breakers.length === 0) {
          circuitsEl.innerHTML = '<div class="empty" style="color:var(--text-muted)">All upstream channels operating normally.</div>';
        } else {
          data.circuit_breakers.forEach(c => {
            const div = document.createElement("div");
            div.className = "health-item";
            div.innerHTML = \`
              <div class="health-row">
                <span class="health-label">Origin:</span>
                <span class="health-val"><code>\${c.origin}</code></span>
              </div>
              <div class="health-row">
                <span class="health-label">Status:</span>
                <span class="health-val">
                  <span class="status-dot \${c.open ? 'red' : 'green'}"></span> \${c.open ? 'OPEN (Block)' : 'Closed (OK)'}
                </span>
              </div>
              <div class="health-row">
                <span class="health-label">Failures count:</span>
                <span class="health-val">\${c.failures}</span>
              </div>
              \${c.open ? \`<div class="health-row"><span class="health-label">Cooldown:</span><span class="health-val">\${Math.round(c.cooldown_remaining_ms / 1000)}s</span></div>\` : ""}
            \`;
            circuitsEl.appendChild(div);
          });
        }

        // Upstream health
        const upstreamsEl = document.getElementById("health-upstreams");
        upstreamsEl.innerHTML = "";
        if (!data.upstream_health || data.upstream_health.length === 0) {
          upstreamsEl.innerHTML = '<div class="empty" style="color:var(--text-muted)">No upstream requests tracked yet.</div>';
        } else {
          data.upstream_health.forEach(u => {
            const div = document.createElement("div");
            div.className = "health-item";
            div.innerHTML = \`
              <div class="health-row">
                <span class="health-label">Upstream:</span>
                <span class="health-val"><code>\${u.origin}</code></span>
              </div>
              <div class="health-row">
                <span class="health-label">Stats (Ok/Fail):</span>
                <span class="health-val" style="color:var(--success-color)">\${u.successes}</span> / <span class="health-val" style="color:var(--danger-color)">\${u.failures}</span>
              </div>
              <div class="health-row">
                <span class="health-label">Avg Latency:</span>
                <span class="health-val">\${Math.round(u.avgLatencyMs)} ms</span>
              </div>
              <div class="health-row">
                <span class="health-label">Last failure:</span>
                <span class="health-val">\${u.lastFailure ? new Date(u.lastFailure).toLocaleTimeString() : 'None'}</span>
              </div>
            \`;
            upstreamsEl.appendChild(div);
          });
        }

      } catch (err) {}
    }

    function formatUptime(seconds) {
      if (seconds < 60) return seconds + "s";
      const m = Math.floor(seconds / 60);
      if (m < 60) return m + "m " + (seconds % 60) + "s";
      const h = Math.floor(m / 60);
      if (h < 24) return h + "h " + (m % 60) + "m";
      const d = Math.floor(h / 24);
      return d + "d " + (h % 24) + "h";
    }

    // ─── Phase 3: Category Management ───
    async function loadCategories() {
      try {
        const res = await fetch("/api/custom-categories");
        if (!res.ok) throw new Error("Could not load categories");
        const data = await res.json();
        customCategories = (data.categories || []).sort((a,b) => a.order - b.order);
        renderCategoriesList();
        renderActiveCategory();
        populateCategorySelects();
      } catch (err) {
        showToast("Error loading categories: " + err.message, "error");
      }
    }

    function renderCategoriesList() {
      const listEl = document.getElementById("categories-list");
      listEl.innerHTML = "";
      if (customCategories.length === 0) {
        listEl.innerHTML = '<div class="empty">No custom categories defined.</div>';
        return;
      }

      customCategories.forEach((cat, index) => {
        const div = document.createElement("div");
        div.className = "draggable-item" + (activeCategoryId === cat.id ? " active" : "");
        div.draggable = true;
        div.dataset.index = index;
        div.innerHTML = \`
          <span class="drag-handle">☰</span>
          <span class="item-content"><strong>\${cat.name}</strong> <small style="color:var(--text-secondary)">(\${cat.channelKeys.length} channels)</small></span>
          <div class="item-actions">
            <button class="btn btn-secondary btn-sm" style="padding: 2px 6px;" onclick="renameCategory(event, '\${cat.id}')">✏️</button>
            <button class="btn btn-danger btn-sm" style="padding: 2px 6px;" onclick="deleteCategory(event, '\${cat.id}')">🗑️</button>
          </div>
        \`;

        // Selection
        div.addEventListener("click", (e) => {
          if (e.target.closest("button") || e.target.closest(".drag-handle")) return;
          activeCategoryId = cat.id;
          renderCategoriesList();
          renderActiveCategory();
        });

        // Category Drag/Drop sort events
        div.addEventListener("dragstart", (e) => {
          e.dataTransfer.setData("text/plain", index);
          div.style.opacity = "0.5";
        });
        div.addEventListener("dragend", () => { div.style.opacity = "1"; });
        div.addEventListener("dragover", (e) => { e.preventDefault(); div.style.borderTop = "2px solid var(--accent-color)"; });
        div.addEventListener("dragleave", () => { div.style.borderTop = "none"; });
        div.addEventListener("drop", (e) => {
          e.preventDefault();
          div.style.borderTop = "none";
          const fromIdx = parseInt(e.dataTransfer.getData("text/plain"));
          const toIdx = index;
          if (fromIdx !== toIdx) {
            const moved = customCategories.splice(fromIdx, 1)[0];
            customCategories.splice(toIdx, 0, moved);
            // Re-order mapping
            customCategories.forEach((c, idx) => c.order = idx + 1);
            renderCategoriesList();
            renderActiveCategory();
          }
        });

        listEl.appendChild(div);
      });
    }

    function renameCategory(event, id) {
      event.stopPropagation();
      const cat = customCategories.find(c => c.id === id);
      if (!cat) return;
      const newName = prompt("Rename Category:", cat.name);
      if (newName && newName.trim()) {
        cat.name = newName.trim();
        renderCategoriesList();
        renderActiveCategory();
        populateCategorySelects();
      }
    }

    function deleteCategory(event, id) {
      event.stopPropagation();
      if (!confirm("Delete category? Assigned channels will return to uncategorized list.")) return;
      customCategories = customCategories.filter(c => c.id !== id);
      if (activeCategoryId === id) activeCategoryId = null;
      renderCategoriesList();
      renderActiveCategory();
      populateCategorySelects();
    }

    function addCategory() {
      const nameInput = document.getElementById("new-cat-name");
      const name = nameInput.value.trim();
      if (!name) return;
      
      const newId = String(Date.now()) + Math.floor(Math.random()*1000);
      customCategories.push({
        id: newId,
        name: name,
        order: customCategories.length + 1,
        channelKeys: []
      });
      nameInput.value = "";
      renderCategoriesList();
      populateCategorySelects();
    }

    async function saveCategories() {
      try {
        const res = await fetch("/api/custom-categories/save", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ categories: customCategories })
        });
        if (!res.ok) throw new Error("Save failed");
        showToast("Categories and order saved!");
        await loadCategories();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    // Auto-import categories
    function autoImportCategories() {
      if (allChannels.length === 0) {
        showToast("No channels loaded to build categories from.", "error");
        return;
      }
      if (customCategories.length > 0 && !confirm("This will overwrite all current custom categories. Continue?")) return;

      const catMap = new Map();
      allChannels.forEach(ch => {
        const cName = ch.category || "Uncategorized";
        if (!catMap.has(cName)) catMap.set(cName, []);
        catMap.get(cName).push(ch.key);
      });

      customCategories = [];
      let order = 1;
      catMap.forEach((keys, name) => {
        customCategories.push({
          id: String(Date.now()) + Math.floor(Math.random()*1000) + order,
          name: name,
          order: order++,
          channelKeys: keys
        });
      });
      renderCategoriesList();
      renderActiveCategory();
      populateCategorySelects();
      showToast("Built categories from active channels! Click Save to apply.");
    }

    function renderActiveCategory() {
      const cat = customCategories.find(c => c.id === activeCategoryId);
      const emptyEl = document.getElementById("cat-channels-empty");
      const panelEl = document.getElementById("cat-channels-panel");
      
      if (!cat) {
        emptyEl.style.display = "block";
        panelEl.style.display = "none";
        document.getElementById("active-cat-title").textContent = "";
        return;
      }

      emptyEl.style.display = "none";
      panelEl.style.display = "block";
      document.getElementById("active-cat-title").textContent = " - " + cat.name;
      document.getElementById("cat-ch-count").textContent = cat.channelKeys.length;

      const listEl = document.getElementById("active-cat-ch-list");
      listEl.innerHTML = "";
      
      if (cat.channelKeys.length === 0) {
        listEl.innerHTML = '<div class="empty">No channels assigned yet. Add some above.</div>';
        return;
      }

      cat.channelKeys.forEach((key, index) => {
        const ch = allChannels.find(x => x.key === key);
        const name = ch ? ch.name : key;
        const div = document.createElement("div");
        div.className = "draggable-item";
        div.draggable = true;
        div.dataset.index = index;
        div.innerHTML = \`
          <span class="drag-handle">☰</span>
          <span class="item-content">\${name}</span>
          <button class="btn btn-danger btn-sm" style="padding:2px 6px" onclick="removeCategoryChannel(\${index})">Remove</button>
        \`;

        div.addEventListener("dragstart", (e) => {
          e.dataTransfer.setData("text/plain", index);
          div.style.opacity = "0.5";
        });
        div.addEventListener("dragend", () => { div.style.opacity = "1"; });
        div.addEventListener("dragover", (e) => { e.preventDefault(); div.style.borderTop = "2px solid var(--accent-color)"; });
        div.addEventListener("dragleave", () => { div.style.borderTop = "none"; });
        div.addEventListener("drop", (e) => {
          e.preventDefault();
          div.style.borderTop = "none";
          const fromIdx = parseInt(e.dataTransfer.getData("text/plain"));
          const toIdx = index;
          if (fromIdx !== toIdx) {
            const moved = cat.channelKeys.splice(fromIdx, 1)[0];
            cat.channelKeys.splice(toIdx, 0, moved);
            renderActiveCategory();
            renderCategoriesList();
          }
        });

        listEl.appendChild(div);
      });
    }

    function removeCategoryChannel(index) {
      const cat = customCategories.find(c => c.id === activeCategoryId);
      if (!cat) return;
      cat.channelKeys.splice(index, 1);
      renderActiveCategory();
      renderCategoriesList();
    }

    function clearActiveCategoryChannels() {
      const cat = customCategories.find(c => c.id === activeCategoryId);
      if (!cat || !confirm("Clear all channels from this category?")) return;
      cat.channelKeys = [];
      renderActiveCategory();
      renderCategoriesList();
    }

    // Category Autocomplete Channel Search
    const catSearchInput = document.getElementById("cat-ch-search");
    const catAutocompleteEl = document.getElementById("cat-ch-autocomplete");

    catSearchInput.addEventListener("input", () => {
      const q = catSearchInput.value.toLowerCase().trim();
      if (!q) {
        catAutocompleteEl.style.display = "none";
        return;
      }
      const cat = customCategories.find(c => c.id === activeCategoryId);
      if (!cat) return;

      const filtered = allChannels
        .filter(ch => !cat.channelKeys.includes(ch.key) && (ch.name + " " + (ch.category || "")).toLowerCase().includes(q))
        .slice(0, 30);

      catAutocompleteEl.innerHTML = "";
      if (filtered.length === 0) {
        catAutocompleteEl.innerHTML = '<div style="padding:10px;color:var(--text-muted);font-size:12.5px">No matches found.</div>';
      } else {
        filtered.forEach(ch => {
          const div = document.createElement("div");
          div.className = "autocomplete-item";
          div.innerHTML = \`<span>\${ch.name} <small style="color:var(--text-secondary)">(\&nbsp;\${ch.category || 'Live'}&nbsp;)</small></span> <span>➕</span>\`;
          div.addEventListener("click", () => {
            cat.channelKeys.push(ch.key);
            catSearchInput.value = "";
            catAutocompleteEl.style.display = "none";
            renderActiveCategory();
            renderCategoriesList();
          });
          catAutocompleteEl.appendChild(div);
        });
      }
      catAutocompleteEl.style.display = "block";
    });

    document.addEventListener("click", (e) => {
      if (!catSearchInput.contains(e.target) && !catAutocompleteEl.contains(e.target)) {
        catAutocompleteEl.style.display = "none";
      }
    });

    // Populate category select dropdowns
    function populateCategorySelects() {
      const selects = [
        document.getElementById("global-ch-filter"),
        document.getElementById("bulk-cat-select")
      ];
      selects.forEach((select, idx) => {
        if (!select) return;
        const val = select.value;
        select.innerHTML = idx === 0 
          ? '<option value="">All Categories</option><option value="uncategorized">Uncategorized</option>'
          : '<option value="">Move to Custom Category...</option>';
        customCategories.forEach(c => {
          const opt = document.createElement("option");
          opt.value = c.id;
          opt.textContent = c.name;
          select.appendChild(opt);
        });
        select.value = val;
      });
    }

    // Categories JSON import/export
    function exportCategories() {
      const data = JSON.stringify({ categories: customCategories }, null, 2);
      const blob = new Blob([data], { type: "application/json" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = "custom-categories.json";
      a.click();
      URL.revokeObjectURL(url);
      showToast("Categories JSON exported!");
    }

    function toggleImportArea(type) {
      const el = document.getElementById(\`import-\${type}-area\`);
      el.style.display = el.style.display === "none" ? "block" : "none";
    }

    function doImportCategories() {
      const txt = document.getElementById("import-cat-json").value.trim();
      if (!txt) return;
      try {
        const parsed = JSON.parse(txt);
        if (!Array.isArray(parsed.categories)) throw new Error("Invalid format: expected 'categories' array");
        customCategories = parsed.categories.sort((a,b) => a.order - b.order);
        renderCategoriesList();
        renderActiveCategory();
        populateCategorySelects();
        showToast("Categories JSON loaded! Click Save to apply.");
        document.getElementById("import-cat-json").value = "";
        document.getElementById("import-cat-area").style.display = "none";
      } catch (err) {
        showToast("Import failed: " + err.message, "error");
      }
    }

    // ─── Phase 3: Channels Browser ───
    async function loadAllChannels() {
      const listEl = document.getElementById("browser-channels-list");
      listEl.innerHTML = '<div class="empty">Loading channels...</div>';
      try {
        const res = await fetch("/api/all-channels");
        if (!res.ok) throw new Error("Failed to load channels");
        const data = await res.json();
        allChannels = data.channels || [];
        
        renderChannelsBrowser();
        renderPlaylistChannelPicker();
        // Load active categories in background
        await loadCategories();
      } catch (err) {
        listEl.innerHTML = \`<div class="empty" style="color:var(--danger-color)">\${err.message}</div>\`;
      }
    }

    function renderChannelsBrowser() {
      const listEl = document.getElementById("browser-channels-list");
      const q = document.getElementById("global-ch-search").value.toLowerCase().trim();
      const filterCatId = document.getElementById("global-ch-filter").value;

      // Filter
      let filtered = allChannels;
      if (filterCatId === "uncategorized") {
        const mappedKeys = new Set(customCategories.flatMap(c => c.channelKeys));
        filtered = allChannels.filter(ch => !mappedKeys.has(ch.key));
      } else if (filterCatId) {
        const cat = customCategories.find(c => c.id === filterCatId);
        const keys = cat ? new Set(cat.channelKeys) : new Set();
        filtered = allChannels.filter(ch => keys.has(ch.key));
      }

      if (q) {
        filtered = filtered.filter(ch => 
          ch.name.toLowerCase().includes(q) || 
          (ch.category || "").toLowerCase().includes(q)
        );
      }

      document.getElementById("browser-ch-count").textContent = filtered.length + " channels";
      listEl.innerHTML = "";

      if (filtered.length === 0) {
        listEl.innerHTML = '<div style="padding:20px;color:var(--text-muted);text-align:center">No channels found.</div>';
        return;
      }

      // Display up to 100 channels in virtualized grid scroll to prevent crash
      const limit = 150;
      const shown = filtered.slice(0, limit);

      shown.forEach(ch => {
        const div = document.createElement("div");
        div.className = "channel-row";
        
        const isChecked = selectedBrowserKeys.has(ch.key);
        
        div.innerHTML = \`
          <input type="checkbox" \${isChecked ? 'checked' : ''} data-key="\${ch.key}">
          <div class="channel-info" style="cursor:pointer">
            <span class="channel-name">\${ch.name}</span>
            <span class="channel-category">\${ch.category || 'Live'}</span>
          </div>
          <div style="display:flex;gap:6px">
            <button class="btn btn-secondary btn-sm" style="padding:2px 8px;font-size:11px" onclick="previewChannel(event, '\${ch.key}')">⚡ Preview</button>
          </div>
        \`;

        // Checkbox click
        div.querySelector("input").addEventListener("change", (e) => {
          if (e.target.checked) selectedBrowserKeys.add(ch.key);
          else selectedBrowserKeys.delete(ch.key);
          updateBrowserSelectedCount();
        });

        // Row preview trigger
        div.querySelector(".channel-info").addEventListener("click", (e) => {
          previewChannel(e, ch.key);
        });

        listEl.appendChild(div);
      });

      if (filtered.length > limit) {
        const more = document.createElement("div");
        more.style.cssText = "padding:12px;text-align:center;color:var(--text-muted);font-size:12px";
        more.textContent = \`+ \${filtered.length - limit} more channels — refine search query.\`;
        listEl.appendChild(more);
      }
    }

    function toggleAllBrowserCheckboxes(status) {
      const container = document.getElementById("browser-channels-list");
      const boxes = container.querySelectorAll("input[type='checkbox']");
      boxes.forEach(cb => {
        cb.checked = status;
        const key = cb.getAttribute("data-key");
        if (status) selectedBrowserKeys.add(key);
        else selectedBrowserKeys.delete(key);
      });
      updateBrowserSelectedCount();
    }

    function updateBrowserSelectedCount() {
      document.getElementById("browser-selected-count").textContent = selectedBrowserKeys.size;
    }

    // Bulk assign channels to custom category
    async function bulkAssignChannels() {
      if (selectedBrowserKeys.size === 0) {
        showToast("Select channels first.", "error");
        return;
      }
      const catId = document.getElementById("bulk-cat-select").value;
      if (!catId) {
        showToast("Select a target category.", "error");
        return;
      }

      const cat = customCategories.find(c => c.id === catId);
      if (!cat) return;

      let addedCount = 0;
      selectedBrowserKeys.forEach(key => {
        // Remove from existing custom categories to prevent duplicates
        customCategories.forEach(c => {
          c.channelKeys = c.channelKeys.filter(k => k !== key);
        });
        
        // Add to new
        if (!cat.channelKeys.includes(key)) {
          cat.channelKeys.push(key);
          addedCount++;
        }
      });

      selectedBrowserKeys.clear();
      updateBrowserSelectedCount();
      toggleAllBrowserCheckboxes(false);
      
      renderCategoriesList();
      renderActiveCategory();
      renderChannelsBrowser();

      showToast(\`Assigned \${addedCount} channels to category "\${cat.name}". Save changes to persist.\`);
    }

    // Preview Channel via HLS.js
    async function previewChannel(event, key) {
      if (event) event.stopPropagation();
      const ch = allChannels.find(x => x.key === key);
      if (!ch) return;

      const video = document.getElementById("video-player");
      const status = document.getElementById("player-status");
      const title = document.getElementById("preview-ch-name");
      const urlText = document.getElementById("preview-ch-url");

      // Generate local streaming path for the player (simulating Xtream endpoint)
      const streamUrl = \`\${window.location.origin}/live/preview-user/preview-pass/\${ch.key}.m3u8\`;

      title.style.display = "block";
      title.textContent = ch.name;
      urlText.style.display = "block";
      urlText.textContent = streamUrl;

      status.style.display = "block";
      status.textContent = "Loading stream HLS segments...";
      video.style.display = "none";

      if (hlsPlayerInstance) {
        hlsPlayerInstance.destroy();
        hlsPlayerInstance = null;
      }

      if (Hls.isSupported()) {
        hlsPlayerInstance = new Hls({
          maxBufferLength: 4,
          maxMaxBufferLength: 6,
          enableWorker: true
        });
        hlsPlayerInstance.loadSource(streamUrl);
        hlsPlayerInstance.attachMedia(video);
        hlsPlayerInstance.on(Hls.Events.MANIFEST_PARSED, function() {
          status.style.display = "none";
          video.style.display = "block";
          video.play().catch(() => {});
        });
        hlsPlayerInstance.on(Hls.Events.ERROR, function(event, data) {
          if (data.fatal) {
            status.textContent = "Stream load error: Upstream offline, codec issue or CORS blocked.";
            video.style.display = "none";
          }
        });
      } else if (video.canPlayType('application/vnd.apple.mpegurl')) {
        // Native fallback (Safari)
        video.src = streamUrl;
        video.style.display = "block";
        status.style.display = "none";
      } else {
        status.textContent = "HLS streaming is not supported on this browser.";
      }
    }

    // ─── Phase 3: Access Users ───
    async function loadUsers() {
      const wrapper = document.getElementById("users-list-wrapper");
      try {
        const res = await fetch("/api/access-users");
        if (!res.ok) throw new Error("Could not load users");
        const data = await res.json();
        renderUsersList(data.users || []);
      } catch (err) {
        wrapper.innerHTML = \`<div class="empty" style="color:var(--danger-color)">\${err.message}</div>\`;
      }
    }

    function renderUsersList(users) {
      const wrapper = document.getElementById("users-list-wrapper");
      if (users.length === 0) {
        wrapper.innerHTML = '<div class="empty">No generated links yet.</div>';
        return;
      }

      wrapper.innerHTML = \`
        <table>
          <thead>
            <tr>
              <th>Username</th>
              <th>Status</th>
              <th>Allowed Content</th>
              <th>Expiration</th>
              <th>IPTV Links</th>
              <th>Actions</th>
            </tr>
          </thead>
          <tbody>
            \${users.map(u => {
              const status = u.expired ? 'Expired' : (u.disabled ? 'Disabled' : 'Active');
              const statusClass = u.expired || u.disabled ? 'disabled' : 'active';
              
              // Get base details for XTREAM copy
              const gatewayHost = window.location.hostname;
              const gatewayPort = window.location.port || (window.location.protocol === 'https:' ? '443' : '80');
              const xtreamCredsText = \`Server: \${gatewayHost}\\nPort: \${gatewayPort}\\nUser: \${u.username}\\nPass: \${u.password}\`;

              return \`
                <tr>
                  <td><strong>\${u.username}</strong></td>
                  <td><span class="status-badge \${statusClass}">\${status}</span></td>
                  <td>
                    \${u.include_live ? '<span class="pill">Live</span>' : ''}
                    \${u.include_movies ? '<span class="pill">Movies</span>' : ''}
                    \${u.include_series ? '<span class="pill">Series</span>' : ''}
                  </td>
                  <td>\${u.expires_at ? new Date(u.expires_at).toLocaleDateString() : 'Infinite'}</td>
                  <td style="max-width: 320px">
                    <div style="font-size:11px;color:var(--text-secondary);margin-bottom:4px">M3U Plus URL:</div>
                    <div class="copy-field">
                      <div class="copy-text">\${u.m3u_url}</div>
                      <button class="copy-btn" onclick="copyClipboard('\${u.m3u_url}', 'M3U Link')">Copy</button>
                    </div>
                    
                    <div style="font-size:11px;color:var(--text-secondary);margin-bottom:4px">Xtream Login Details:</div>
                    <div class="copy-field">
                      <div class="copy-text">Host: \${gatewayHost} | User: \${u.username}</div>
                      <button class="copy-btn" onclick="copyClipboard(\\\`\${xtreamCredsText}\\\`, 'Xtream Login')">Copy All</button>
                    </div>
                  </td>
                  <td>
                    <button class="btn btn-danger btn-sm" onclick="deleteUser('\${u.username}')">Delete</button>
                  </td>
                </tr>
              \`;
            }).join("")}
          </tbody>
        </table>
      \`;
    }

    async function copyClipboard(text, label) {
      try {
        await navigator.clipboard.writeText(text);
        showToast(\`\${label} copied to clipboard!\`);
      } catch (err) {
        showToast("Copy failed", "error");
      }
    }

    async function createUser(event) {
      event.preventDefault();
      const form = document.getElementById("create-user-form");
      const fd = new FormData(form);
      const data = Object.fromEntries(fd.entries());
      
      data.include_live = form.elements.include_live.checked;
      data.include_movies = form.elements.include_movies.checked;
      data.include_series = form.elements.include_series.checked;

      try {
        const res = await fetch("/api/access-users", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify(data)
        });
        const payload = await res.json();
        if (!res.ok) throw new Error(payload.error || "Create failed");
        showToast("Access link created!");
        form.reset();
        generateRandomPass();
        await loadUsers();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    async function deleteUser(username) {
      if (!confirm(\`Delete user "\${username}"?\`)) return;
      try {
        const res = await fetch("/api/access-users/delete", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ username })
        });
        if (!res.ok) throw new Error("Delete failed");
        showToast("User deleted");
        await loadUsers();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    // ─── Phase 3: Custom Playlists ───
    async function loadPlaylists() {
      const wrapper = document.getElementById("playlists-list");
      try {
        const res = await fetch("/api/custom-playlists");
        if (!res.ok) throw new Error("Could not load playlists");
        const data = await res.json();
        renderPlaylistsList(data.playlists || []);
      } catch (err) {
        wrapper.innerHTML = \`<div class="empty" style="color:var(--danger-color)">\${err.message}</div>\`;
      }
    }

    function renderPlaylistsList(playlists) {
      const wrapper = document.getElementById("playlists-list");
      if (playlists.length === 0) {
        wrapper.innerHTML = '<div class="empty">No custom playlists created yet.</div>';
        return;
      }

      wrapper.innerHTML = playlists.map(p => \`
        <div class="stat-card" style="background:rgba(255,255,255,0.015); border:1px solid var(--panel-border); margin-bottom:0">
          <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:8px">
            <h3 style="font-size:15px; font-weight:600">\${p.name}</h3>
            <span style="font-size:12px; color:var(--text-secondary)">\${p.channelKeys.length} channels</span>
          </div>
          
          <div style="font-size:11px;color:var(--text-secondary);margin-bottom:4px">M3U Playlist URL:</div>
          <div class="copy-field">
            <div class="copy-text">\${p.m3u_url}</div>
            <button class="copy-btn" onclick="copyClipboard('\${p.m3u_url}', 'M3U Link')">Copy</button>
          </div>
          
          <div style="font-size:11px;color:var(--text-secondary);margin-bottom:4px">JSON API URL:</div>
          <div class="copy-field" style="margin-bottom:12px">
            <div class="copy-text">\${p.api_url}</div>
            <button class="copy-btn" onclick="copyClipboard('\${p.api_url}', 'API Link')">Copy</button>
          </div>

          <div style="display:flex; gap:8px">
            <button class="btn btn-secondary btn-sm" onclick="editPlaylist('\${p.id}')">Edit</button>
            <button class="btn btn-danger btn-sm" onclick="deletePlaylist('\${p.id}')">Delete</button>
          </div>
        </div>
      \`).join("");
    }

    function renderPlaylistChannelPicker() {
      const listEl = document.getElementById("pl-channels-list");
      const q = document.getElementById("pl-ch-search").value.toLowerCase().trim();

      let filtered = allChannels;
      if (q) {
        filtered = allChannels.filter(ch => 
          ch.name.toLowerCase().includes(q) || 
          (ch.category || "").toLowerCase().includes(q)
        );
      }

      listEl.innerHTML = "";
      if (filtered.length === 0) {
        listEl.innerHTML = '<div style="padding:15px;color:var(--text-muted);text-align:center">No channels found.</div>';
        return;
      }

      const limit = 100;
      const shown = filtered.slice(0, limit);

      shown.forEach(ch => {
        const div = document.createElement("div");
        div.className = "channel-row";
        const isChecked = selectedPlaylistKeys.has(ch.key);
        div.innerHTML = \`
          <input type="checkbox" \${isChecked ? 'checked' : ''} data-key="\${ch.key}">
          <div class="channel-info">
            <span class="channel-name">\${ch.name}</span>
            <span class="channel-category">\${ch.category || 'Live'}</span>
          </div>
        \`;

        div.querySelector("input").addEventListener("change", (e) => {
          if (e.target.checked) selectedPlaylistKeys.add(ch.key);
          else selectedPlaylistKeys.delete(ch.key);
          updatePlaylistSelectedCount();
        });

        listEl.appendChild(div);
      });

      if (filtered.length > limit) {
        const more = document.createElement("div");
        more.style.cssText = "padding:8px;text-align:center;color:var(--text-muted);font-size:11.5px";
        more.textContent = \`+ \${filtered.length - limit} more channels — refine query.\`;
        listEl.appendChild(more);
      }
    }

    function toggleAllPlCheckboxes(status) {
      const listEl = document.getElementById("pl-channels-list");
      listEl.querySelectorAll("input[type='checkbox']").forEach(cb => {
        cb.checked = status;
        const key = cb.getAttribute("data-key");
        if (status) selectedPlaylistKeys.add(key);
        else selectedPlaylistKeys.delete(key);
      });
      updatePlaylistSelectedCount();
    }

    function updatePlaylistSelectedCount() {
      document.getElementById("pl-selected-count").textContent = selectedPlaylistKeys.size + " channels selected";
    }

    async function createPlaylist() {
      const nameInput = document.getElementById("pl-name");
      const name = nameInput.value.trim();
      if (!name) { showToast("Enter playlist name.", "error"); return; }
      if (selectedPlaylistKeys.size === 0) { showToast("Select at least one channel.", "error"); return; }

      try {
        const res = await fetch("/api/custom-playlists", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ name, channelKeys: Array.from(selectedPlaylistKeys) })
        });
        const data = await res.json();
        if (!res.ok) throw new Error(data.error || "Playlist creation failed");
        showToast("Playlist created successfully!");
        nameInput.value = "";
        selectedPlaylistKeys.clear();
        updatePlaylistSelectedCount();
        renderPlaylistChannelPicker();
        await loadPlaylists();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    async function deletePlaylist(id) {
      if (!confirm("Delete this playlist?")) return;
      try {
        const res = await fetch("/api/custom-playlists/delete", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ id })
        });
        if (!res.ok) throw new Error("Delete failed");
        showToast("Playlist deleted!");
        await loadPlaylists();
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    function editPlaylist(id) {
      // Inline edit loader
      showToast("Edit is currently not active. Please delete and recreate.", "info");
    }

    async function exportPlaylists() {
      try {
        const res = await fetch("/api/custom-playlists/export");
        if (!res.ok) throw new Error("Export failed");
        const blob = await res.blob();
        const a = document.createElement("a");
        a.href = URL.createObjectURL(blob);
        a.download = "custom-playlists.json";
        a.click();
        URL.revokeObjectURL(a.href);
        showToast("Playlists JSON exported!");
      } catch (err) {
        showToast(err.message, "error");
      }
    }

    async function doImportPlaylists() {
      const txt = document.getElementById("import-pl-json").value.trim();
      if (!txt) return;
      try {
        const parsed = JSON.parse(txt);
        const res = await fetch("/api/custom-playlists/import", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify(parsed)
        });
        const result = await res.json();
        if (!res.ok) throw new Error(result.error || "Import failed");
        showToast(\`Imported successfully! Added: \${result.added}, Updated: \${result.updated}\`);
        document.getElementById("import-pl-json").value = "";
        document.getElementById("import-pl-area").style.display = "none";
        await loadPlaylists();
      } catch (err) {
        showToast("Import failed: " + err.message, "error");
      }
    }

    // Initialize Page Data
    window.addEventListener("load", async () => {
      generateRandomPass();
      
      // Load Providers list
      await loadProviders();

      // Load all channels in memory
      await loadAllChannels();
      
      // Load Access users list
      await loadUsers();
      
      // Load custom playlists
      await loadPlaylists();

      // Start fetching health stats and poll every 5s
      await fetchHealthStats();
      setInterval(fetchHealthStats, 5000);
    });
  </script>
</body>
</html>`;
}


function m3uAttr(value) {
    return String(value ?? "").replace(/[\r\n"]/g, " ").trim();
}

function m3uDisplayName(value) {
    return cleanString(value, "Unknown").replace(/[\r\n]/g, " ");
}

function appendM3uEntry(lines, { id, name, logo, category, url }) {
    if (!url) return;
    const displayName = m3uDisplayName(name);
    lines.push(`#EXTINF:-1 tvg-id="${m3uAttr(id)}" tvg-name="${m3uAttr(displayName)}" tvg-logo="${m3uAttr(logo)}" group-title="${m3uAttr(category)}",${displayName}`);
    lines.push(url);
}

function generatedPlaylistCacheKey(account, includes) {
    return [
        account.username,
        includes.includeLive ? "live1" : "live0",
        includes.includeMovies ? "movies1" : "movies0",
        includes.includeSeries ? "series1" : "series0",
    ].join("|");
}

function generatedLiveUrl(channel, account, request, env) {
    return `${publicBase(request, env)}/live/${encodePathSegment(account.username)}/${encodePathSegment(account.password)}/${channel.key}.ts`;
}

async function m3uSeriesEpisodeRecords(request, env, force = false) {
    const url = new URL(request.url);
    const sources = selectedPlaylistSources(env, url.searchParams.get("source"));
    const maxSeries = Math.max(0, envInt(env, "M3U_SERIES_MAX_SERIES", 75));
    const maxEpisodes = Math.max(0, envInt(env, "M3U_SERIES_MAX_EPISODES", 2500));
    const episodes = [];

    for (const source of sources) {
        const catalog = await loadXtreamCatalog(env, source, "series", force).catch(() => null);
        if (!catalog || catalog.items.length === 0) continue;

        let loadedSeries = 0;
        for (const item of catalog.items) {
            if (maxSeries > 0 && loadedSeries >= maxSeries) break;
            if (maxEpisodes > 0 && episodes.length >= maxEpisodes) break;

            const seriesId = itemId(item, "series");
            if (!seriesId) continue;
            loadedSeries += 1;
            const infoEntry = await loadXtreamSeriesInfo(env, source, seriesId, force).catch(() => null);
            const seriesName = cleanString(item.name, "Unknown");
            const category = catalogCategory(catalog, item);
            const logo = mediaLogo(item);
            for (const episode of flattenSeriesEpisodes(source, seriesId, infoEntry)) {
                if (maxEpisodes > 0 && episodes.length >= maxEpisodes) break;
                const season = String(episode.season ?? "").padStart(2, "0");
                const episodeNum = String(episode.episode_num ?? "").padStart(2, "0");
                const episodeLabel = season && episodeNum ? ` S${season}E${episodeNum}` : "";
                episodes.push({
                    id: episode.episode_id,
                    name: `${seriesName}${episodeLabel} - ${episode.title}`,
                    logo,
                    category: category || "TV Series",
                    url: episode.url,
                });
            }
        }
    }

    return episodes;
}

async function generatedM3uBody(account, request, env) {
    const lines = ["#EXTM3U"];
    const includes = playlistIncludeFlags(request, account);

    if (includes.includeLive) {
        const channels = await loadPlaylistChannels(env, false);
        for (const channel of channels) {
            appendM3uEntry(lines, {
                id: channel.key,
                name: channel.name,
                logo: channel.logo,
                category: channel.category || "Live",
                url: generatedLiveUrl(channel, account, request, env),
            });
        }
    }

    if (includes.includeMovies) {
        const payload = await moviesPayload(request, env, false);
        for (const movie of payload.movies) {
            appendM3uEntry(lines, {
                id: movie.stream_id,
                name: movie.name,
                logo: movie.logo,
                category: movie.category || "Movies",
                url: movie.url,
            });
        }
    }

    if (includes.includeSeries) {
        const episodes = await m3uSeriesEpisodeRecords(request, env, false);
        for (const episode of episodes) appendM3uEntry(lines, episode);
    }

    return `${lines.join("\n")}\n`;
}

async function buildGeneratedPlaylistCached(account, request, env) {
    const includes = playlistIncludeFlags(request, account);
    const cacheKey = generatedPlaylistCacheKey(account, includes);
    const body = await generatedM3uBody(account, request, env);
    rememberMapEntry(generatedPlaylistCache, cacheKey, { at: Date.now(), body }, MAX_GENERATED_PLAYLIST_CACHE_ENTRIES);
    return { body, cacheKey };
}

async function generatedM3uResponse(request, env, waitUntil = (promise) => promise) {
    const account = await getPlaylistAccessUser(request, env);
    const includes = playlistIncludeFlags(request, account);
    const cacheKey = generatedPlaylistCacheKey(account, includes);
    const freshMs = Math.max(1000, envInt(env, "GENERATED_PLAYLIST_CACHE_MS", 60000));
    const staleMs = Math.max(freshMs, envInt(env, "GENERATED_PLAYLIST_STALE_MS", 900000));
    const buildTimeoutMs = Math.max(1000, envInt(env, "GENERATED_PLAYLIST_BUILD_TIMEOUT_MS", 4800));
    const cached = generatedPlaylistCache.get(cacheKey);
    const ageMs = cached ? Date.now() - cached.at : Number.POSITIVE_INFINITY;

    if (cached && ageMs < freshMs) {
        return playlistResponse(cached.body);
    }

    if (cached && ageMs < staleMs) {
        waitUntil(buildGeneratedPlaylistCached(account, request, env).catch(() => null));
        return playlistResponse(cached.body);
    }

    let built;
    try {
        built = await Promise.race([
            buildGeneratedPlaylistCached(account, request, env),
            new Promise((_, reject) => setTimeout(() => reject(new HttpError(504, "Playlist build timed out.")), buildTimeoutMs)),
        ]);
    } catch (error) {
        if (cached) return playlistResponse(cached.body);
        throw error;
    }

    const body = built.body;
    return withCors(
        new Response(body, {
            headers: {
                "content-type": "application/x-mpegURL; charset=utf-8",
                "cache-control": "public, max-age=15, s-maxage=15, stale-while-revalidate=60",
                "content-disposition": `inline; filename="${m3uAttr(account.username)}.m3u"`,
            },
        }),
    );
}

// Fetch helpers

async function fetchProviderPlaylist(env, url) {
    const timeoutMs = envInt(env, "PLAYLIST_FETCH_TIMEOUT_MS", 12000);
    const maxRetries = envInt(env, "PLAYLIST_FETCH_RETRIES", 2);
    const headers = {
        "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
        accept: "application/x-mpegURL, application/vnd.apple.mpegurl, text/plain, */*",
    };

    let firstBadResponse = null;
    const candidates = upstreamUrlCandidates(url, env);
    const allFailures = [];

    for (const candidateUrl of candidates) {
        for (let attempt = 0; attempt <= maxRetries; attempt++) {
            try {
                const response = await fetchWithTimeout(candidateUrl, { headers, redirect: "follow" }, timeoutMs);
                if (response.ok) {
                    if (attempt > 0 || candidates.indexOf(candidateUrl) > 0) {
                        console.log(`[playlist-fetch] succeeded on candidate ${candidates.indexOf(candidateUrl) + 1}/${candidates.length} attempt ${attempt + 1}`);
                    }
                    return response;
                }
                const failMsg = `${sanitizeUrlForLog(candidateUrl)} -> HTTP ${response.status}`;
                allFailures.push(failMsg);
                console.warn(`[playlist-fetch] ${failMsg} (attempt ${attempt + 1}/${maxRetries + 1})`);
                if (!firstBadResponse) firstBadResponse = response;
                // Don't retry 4xx client errors
                if (response.status >= 400 && response.status < 500) break;
            } catch (err) {
                const failMsg = `${sanitizeUrlForLog(candidateUrl)} -> ${err?.code === "TIMEOUT" ? "TIMEOUT" : err?.message || "network error"}`;
                allFailures.push(failMsg);
                console.warn(`[playlist-fetch] ${failMsg} (attempt ${attempt + 1}/${maxRetries + 1})`);
            }
            if (attempt < maxRetries) {
                const delayMs = 500 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
                await new Promise((resolve) => setTimeout(resolve, delayMs));
            }
        }
    }
    if (allFailures.length > 0) {
        console.error(`[playlist-fetch] ALL candidates FAILED for ${sanitizeUrlForLog(url)}: ${allFailures.join("; ")}`);
    }
    if (firstBadResponse) return firstBadResponse;
    throw new Error(`Provider playlist fetch failed after ${candidates.length} URLs x ${maxRetries + 1} retries.`);
}

// ─── FIXED: fetchHls with retry, logging, and timeout protection
async function fetchHls(url, env, referer) {
    const timeoutMs = envInt(env, "HLS_FETCH_TIMEOUT_MS", 6000);
    const maxRetries = envInt(env, "HLS_FETCH_RETRIES", 1);
    const headers = {
        accept: "application/vnd.apple.mpegurl, application/x-mpegURL, */*",
        "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
    };
    if (referer) headers.referer = referer;

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
        try {
            const response = await fetchWithTimeout(url, { headers, redirect: "follow" }, timeoutMs);
            if (!response.ok) {
                console.warn(`[hls-fetch] ${sanitizeUrlForLog(url)} returned HTTP ${response.status} (attempt ${attempt + 1}/${maxRetries + 1})`);
                if (response.status >= 500 && attempt < maxRetries) {
                    const delayMs = 300 * Math.pow(2, attempt);
                    await new Promise((resolve) => setTimeout(resolve, delayMs));
                    continue;
                }
                return null;
            }
            const text = await response.text();
            if (!text.includes("#EXTM3U")) {
                console.warn(`[hls-fetch] ${sanitizeUrlForLog(url)} response is not a valid M3U8 (missing #EXTM3U header)`);
                return null;
            }
            if (attempt > 0) console.log(`[hls-fetch] ${sanitizeUrlForLog(url)} succeeded on retry ${attempt}`);
            return { finalUrl: response.url, text };
        } catch (err) {
            const isTimeout = err?.code === "TIMEOUT";
            console.warn(`[hls-fetch] ${sanitizeUrlForLog(url)} ${isTimeout ? "TIMED OUT" : "FAILED"}: ${err?.message || err} (attempt ${attempt + 1}/${maxRetries + 1})`);
            if (attempt < maxRetries) {
                const delayMs = 300 * Math.pow(2, attempt);
                await new Promise((resolve) => setTimeout(resolve, delayMs));
            }
        }
    }
    return null;
}

// HTTPS fallback / URL candidates

function httpsFallbackCandidate(url, env) {
    const forceHttps = envBool(env, "FORCE_HTTPS_UPSTREAM", true);
    if (!forceHttps) return null;
    const parsed = new URL(url);
    if (parsed.protocol !== "http:") return null;
    const allowAltPorts = envBool(env, "FORCE_HTTPS_UPSTREAM_ALT_PORTS", false);
    if (parsed.port && parsed.port !== "80" && !allowAltPorts) return null;
    parsed.protocol = "https:";
    const upgraded = parsed.toString();
    return upgraded === url ? null : upgraded;
}

function addUrlCandidate(values, url, env) {
    if (!values.includes(url)) values.push(url);
    const fallback = httpsFallbackCandidate(url, env);
    if (fallback && !values.includes(fallback)) values.push(fallback);
}

function upstreamHlsCandidates(sourceUrl, env) {
    const parsed = new URL(sourceUrl);
    const path = parsed.pathname;
    const query = parsed.search;
    const origin = parsed.origin;
    const pathParts = path.split("/").filter(Boolean);
    const filename = pathParts[pathParts.length - 1] || "";
    const lowerPath = path.toLowerCase();
    const lowerFilename = filename.toLowerCase();
    const stem = filename.includes(".") ? filename.slice(0, filename.lastIndexOf(".")) : filename;
    const candidates = [];

    const addPathCandidate = (candidatePath) => {
        const candidate = new URL(sourceUrl);
        candidate.pathname = candidatePath;
        candidate.search = query;
        addUrlCandidate(candidates, candidate.toString(), env);
    };

    const looksLikeXtreamLive = pathParts.length >= 3 && !lowerPath.includes("/movie/") && !lowerPath.includes("/series/");
    if (looksLikeXtreamLive) {
        const user = pathParts[pathParts.length - 3];
        const password = pathParts[pathParts.length - 2];
        const streamId = stem || pathParts[pathParts.length - 1];
        const baseUrl = (origin && origin !== "null" ? origin : (envString(env, "IPTV_BASE_URL", DEFAULT_IPTV_BASE_URL) || DEFAULT_IPTV_BASE_URL)).replace(/\/+$/, "");
        addUrlCandidate(candidates, `${baseUrl}/live/${user}/${password}/${streamId}.m3u8${query}`, env);
    }

    if (lowerPath.endsWith(".m3u8") || lowerPath.endsWith(".m3u")) addPathCandidate(path);
    if (lowerPath.endsWith(".ts")) addPathCandidate(path.slice(0, -3) + ".m3u8");
    else if (filename && !filename.includes(".")) addPathCandidate(`${path}.m3u8`);
    else if (lowerFilename.endsWith(".m3u")) addPathCandidate(`${path.slice(0, path.lastIndexOf("."))}.m3u8`);
    else if (filename.includes(".") && !lowerFilename.endsWith(".m3u8")) addPathCandidate(`${path.slice(0, path.lastIndexOf("."))}.m3u8`);

    if (looksLikeXtreamLive) {
        const user = pathParts[pathParts.length - 3];
        const password = pathParts[pathParts.length - 2];
        const streamId = stem || pathParts[pathParts.length - 1];
        const baseUrl = (origin && origin !== "null" ? origin : (envString(env, "IPTV_BASE_URL", DEFAULT_IPTV_BASE_URL) || DEFAULT_IPTV_BASE_URL)).replace(/\/+$/, "");
        addUrlCandidate(candidates, `${baseUrl}/${user}/${password}/${streamId}.m3u8${query}`, env);
    }

    return candidates;
}

// Upstream HLS discovery

async function findUpstreamHls(key, sourceUrl, env) {
    return withInflight(upstreamHlsInflight, key, async () => {
        const ttlMs = envInt(env, "UPSTREAM_HLS_CACHE_SECONDS", 60) * 1000;
        const cached = upstreamHlsCache.get(key);
        if (cached && Date.now() - cached.at < ttlMs && cached.url) {
            const fetched = await fetchHls(cached.url, env);
            if (fetched) {
                rememberMapEntry(upstreamHlsCache, key, { url: fetched.finalUrl, at: Date.now() }, MAX_UPSTREAM_HLS_CACHE_ENTRIES);
                return { url: fetched.finalUrl, text: fetched.text };
            }
            console.warn(`[hls-discovery] cached URL for key ${key} no longer works, scanning candidates...`);
        }
        const candidates = upstreamHlsCandidates(sourceUrl, env);
        for (let i = 0; i < candidates.length; i++) {
            const candidate = candidates[i];
            const fetched = await fetchHls(candidate, env);
            if (fetched) {
                console.log(`[hls-discovery] key ${key} resolved via candidate ${i + 1}/${candidates.length}`);
                rememberMapEntry(upstreamHlsCache, key, { url: fetched.finalUrl, at: Date.now() }, MAX_UPSTREAM_HLS_CACHE_ENTRIES);
                return { url: fetched.finalUrl, text: fetched.text };
            }
        }
        // Use a short negative TTL so we retry sooner instead of caching failure for the full TTL
        const negTtlMs = Math.min(ttlMs, envInt(env, "HLS_NEGATIVE_CACHE_SECONDS", 5) * 1000);
        rememberMapEntry(upstreamHlsCache, key, { url: null, at: Date.now() - ttlMs + negTtlMs }, MAX_UPSTREAM_HLS_CACHE_ENTRIES);
        console.error(`[hls-discovery] key ${key} FAILED: none of ${candidates.length} candidates returned valid M3U8 for ${sanitizeUrlForLog(sourceUrl)}`);
        return null;
    });
}

// Playlist rewriting

function parseTargetDuration(text) {
    const declaredMatch = text.match(/#EXT-X-TARGETDURATION:(\d+)/);
    const declared = declaredMatch ? Number.parseInt(declaredMatch[1], 10) : 0;
    let measured = 0;
    for (const match of text.matchAll(/#EXTINF:([0-9.]+)/g)) {
        const d = Number.parseFloat(match[1]);
        if (Number.isFinite(d)) measured = Math.max(measured, Math.ceil(d));
    }
    return Math.max(1, measured || declared || 6);
}

function trimLivePlaylistText(text, env) {
    const configuredKeepSegments = envInt(env, "LIVE_WINDOW_SEGMENTS", 3);
    if (configuredKeepSegments <= 0 || !/#EXTINF:/m.test(text)) return text;

    const keepSegments = Math.max(2, configuredKeepSegments);
    const lines = text.split(/\r?\n/);
    const header = [], footer = [], segments = [];
    let pending = [], seenFirstSegment = false, mediaSequence = null, mediaSequenceIndex = -1;

    for (const rawLine of lines) {
        const line = rawLine.trim();
        if (!line) continue;
        if (!seenFirstSegment) {
            if (!line.startsWith("#")) {
                seenFirstSegment = true;
                segments.push({ lines: [...pending, rawLine] });
                pending = [];
                continue;
            }
            if (line.startsWith("#EXT-X-MEDIA-SEQUENCE:")) {
                mediaSequence = Number.parseInt(line.slice("#EXT-X-MEDIA-SEQUENCE:".length), 10);
                mediaSequenceIndex = header.length;
            }
            if (line.startsWith("#EXTINF") || line.startsWith("#EXT-X-PROGRAM-DATE-TIME") || line.startsWith("#EXT-X-BYTERANGE") || line.startsWith("#EXT-X-DISCONTINUITY")) {
                pending.push(rawLine); continue;
            }
            header.push(rawLine);
            continue;
        }
        if (!line.startsWith("#")) { segments.push({ lines: [...pending, rawLine] }); pending = []; continue; }
        pending.push(rawLine);
    }

    if (pending.length > 0) footer.push(...pending);
    if (segments.length <= keepSegments) return text;

    const dropped = segments.length - keepSegments;
    const kept = segments.slice(-keepSegments);
    if (mediaSequenceIndex >= 0) {
        const nextSequence = Math.max(0, (Number.isFinite(mediaSequence) ? mediaSequence : 0) + dropped);
        header[mediaSequenceIndex] = `#EXT-X-MEDIA-SEQUENCE:${nextSequence}`;
    }
    return `${[...header, ...kept.flatMap((s) => s.lines), ...footer].join("\n")}\n`;
}

async function upstreamAssetUrl(key, absoluteUrl, request, env, playlistUrl) {
    const httpsFallback = httpsFallbackCandidate(absoluteUrl, env);
    const parsed = new URL(absoluteUrl);
    const path = parsed.pathname;
    const filenameParts = path.split("/").filter(Boolean);
    const filename = filenameParts[filenameParts.length - 1] || "segment.bin";

    // M3U8 nested playlists always go through our server (they need content rewriting)
    if (path.toLowerCase().endsWith(".m3u8")) {
        const token = await makeUrlToken({ u: absoluteUrl, r: playlistUrl, f: httpsFallback || undefined }, env);
        const base = streamBase(request, env);
        return `${base}/uplive/${key}/${token}.m3u8`;
    }

    // For segments (.ts, .m4s, etc.): try Bunny CDN first, fall back to proxy
    const bunnyUrl = getBunnyCdnSegmentUrl(absoluteUrl, env);
    if (bunnyUrl) return bunnyUrl;

    // Fallback: proxy through our server (existing behavior)
    const token = await makeUrlToken({ u: absoluteUrl, r: playlistUrl, f: httpsFallback || undefined }, env);
    const base = streamBase(request, env);
    return `${base}/upseg/${key}/${token}/${filename}`;
}

async function rewriteUriAttributes(line, key, playlistUrl, request, env) {
    const matches = [...line.matchAll(/URI="([^"]+)"/g)];
    if (matches.length === 0) return line;
    let output = "", lastIndex = 0;
    for (const match of matches) {
        const absoluteUrl = new URL(match[1], playlistUrl).toString();
        output += line.slice(lastIndex, match.index ?? 0);
        output += `URI="${await upstreamAssetUrl(key, absoluteUrl, request, env, playlistUrl)}"`;
        lastIndex = (match.index ?? 0) + match[0].length;
    }
    return output + line.slice(lastIndex);
}

async function rewriteUpstreamPlaylist(text, playlistUrl, request, env, key) {
    const trimmedText = trimLivePlaylistText(text, env);
    const configuredTarget = envInt(env, "UPSTREAM_TARGET_DURATION", 0);
    const measuredTarget = parseTargetDuration(trimmedText);
    const targetDuration = configuredTarget > 0 ? Math.min(Math.max(1, configuredTarget), measuredTarget) : measuredTarget;
    const startOffsetSegments = Math.max(0, envInt(env, "LIVE_START_OFFSET_SEGMENTS", 2));
    const startOffsetSeconds = Math.max(1, targetDuration * startOffsetSegments);
    const isMediaPlaylist = /#EXTINF:/m.test(trimmedText) || /#EXT-X-PART:/m.test(trimmedText);
    let insertedStart = false;
    const lines = [];

    for (const rawLine of trimmedText.split(/\r?\n/)) {
        const line = rawLine.trim();
        if (!line) { lines.push(rawLine); continue; }
        if (line.startsWith("#EXTM3U")) {
            lines.push(rawLine);
            if (isMediaPlaylist && !insertedStart && startOffsetSegments > 0) {
                lines.push(`#EXT-X-START:TIME-OFFSET=-${startOffsetSeconds},PRECISE=YES`);
                insertedStart = true;
            }
            continue;
        }
        if (line.startsWith("#EXT-X-TARGETDURATION")) { lines.push(`#EXT-X-TARGETDURATION:${targetDuration}`); continue; }
        if (line.startsWith("#EXT-X-ALLOW-CACHE")) { lines.push("#EXT-X-ALLOW-CACHE:YES"); continue; }
        if (line.startsWith("#EXT-X-START")) {
            if (isMediaPlaylist && !insertedStart && startOffsetSegments > 0) {
                lines.push(`#EXT-X-START:TIME-OFFSET=-${startOffsetSeconds},PRECISE=YES`);
                insertedStart = true;
            }
            continue;
        }
        if (line.startsWith("#")) { lines.push(await rewriteUriAttributes(rawLine, key, playlistUrl, request, env)); continue; }
        lines.push(await upstreamAssetUrl(key, new URL(line, playlistUrl).toString(), request, env, playlistUrl));
    }

    return `${lines.join("\n")}\n`;
}

// Segment fetching

function mediaTypeForPath(path) {
    const lower = path.toLowerCase();
    if (lower.endsWith(".m3u8")) return "application/x-mpegURL; charset=utf-8";
    if (lower.endsWith(".ts")) return "video/mp2t";
    if (lower.endsWith(".m4s")) return "video/iso.segment";
    if (lower.endsWith(".mp4")) return "video/mp4";
    if (lower.endsWith(".aac")) return "audio/aac";
    if (lower.endsWith(".m4a")) return "audio/mp4";
    return "application/octet-stream";
}

async function fetchUpstreamAsset(url, referer, env, ttlSeconds, request) {
    const maxRetries = envInt(env, "SEGMENT_FETCH_RETRIES", 2);
    const timeoutMs = envInt(env, "SEGMENT_FETCH_TIMEOUT_MS", 8000);
    const headers = {
        "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
        referer,
        connection: "keep-alive",
    };
    if (request && request.headers.get("range")) headers.range = request.headers.get("range");
    if (request && request.headers.get("if-range")) headers["if-range"] = request.headers.get("if-range");

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
        if (isCircuitOpen(url)) {
            console.warn(`[segment-fetch] circuit open for ${circuitBreakerKey(url)}, skipping`);
            return null;
        }
        const startMs = Date.now();
        try {
            const response = await fetchWithTimeout(url, {
                method: request ? request.method : "GET",
                headers,
                redirect: "follow",
            }, timeoutMs);
            const latency = Date.now() - startMs;
            trackUpstreamRequest(url, response.ok, latency);
            if (response.ok || (response.status >= 200 && response.status < 400)) {
                recordCircuitSuccess(url);
                if (attempt > 0) console.log(`[segment-fetch] succeeded on retry ${attempt} for ${sanitizeUrlForLog(url)}`);
                return response;
            }
            if (response.status >= 400 && response.status < 500 && response.status !== 408 && response.status !== 429) {
                return response;
            }
            if (attempt < maxRetries) {
                const delayMs = 200 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
                await new Promise((resolve) => setTimeout(resolve, delayMs));
            }
        } catch (err) {
            const latency = Date.now() - startMs;
            trackUpstreamRequest(url, false, latency);
            recordCircuitFailure(url);
            if (attempt >= maxRetries) {
                console.warn(`[segment-fetch] FAILED all ${maxRetries + 1} attempts for ${sanitizeUrlForLog(url)}: ${err?.message}`);
                return null;
            }
            const delayMs = 200 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
            await new Promise((resolve) => setTimeout(resolve, delayMs));
        }
    }
    return null;
}

function extractPrefetchSegmentUrls(text, playlistUrl, env, limit) {
    if (limit <= 0) return [];
    const output = [], seen = new Set();
    const lines = text.split(/\r?\n/);
    for (let i = lines.length - 1; i >= 0 && output.length < limit; i--) {
        const line = lines[i].trim();
        if (!line || line.startsWith("#") || line.toLowerCase().endsWith(".m3u8")) continue;
        const absoluteUrl = new URL(line, playlistUrl).toString();
        if (!seen.has(absoluteUrl)) { seen.add(absoluteUrl); output.push(absoluteUrl); }
    }
    return output;
}

async function prefetchSegments(segmentUrls, referer, env) {
    const ttlSeconds = envInt(env, "SEGMENT_CACHE_SECONDS", 30);
    await Promise.all(segmentUrls.map((url) => fetchUpstreamAsset(url, referer, env, ttlSeconds, null)));
}

// Live playlist proxy

async function buildLivePlaylistBody(key, sourceUrl, request, env, waitUntil, cacheKey) {
    return withInflight(livePlaylistInflight, cacheKey, async () => {
        const upstream = await findUpstreamHls(key, sourceUrl, env);
        if (!upstream) throw new HttpError(502, "Upstream HLS unavailable.");
        const body = await rewriteUpstreamPlaylist(upstream.text, upstream.url, request, env, key);
        const prefetchCount = Math.max(0, envInt(env, "PREFETCH_SEGMENTS", 2));
        const segmentUrls = extractPrefetchSegmentUrls(upstream.text, upstream.url, env, prefetchCount);
        rememberMapEntry(livePlaylistCache, cacheKey, { at: Date.now(), body }, MAX_LIVE_PLAYLIST_CACHE_ENTRIES);
        if (segmentUrls.length > 0) waitUntil(prefetchSegments(segmentUrls, upstream.url, env));
        return body;
    });
}

// ─── Loading Video (warmup) ─────────────────────────────────────────────────
// Plays TaxiDevLoad.mp4 (a plain MP4, ~4 min) while the upstream HLS warms up.
// Once 2 real segments appear in the upstream playlist, we stop the loading
// video and serve the live stream. Simple.

function countUpstreamSegments(text) {
    if (!text) return 0;
    let count = 0;
    for (const line of text.split(/\r?\n/)) {
        const t = line.trim();
        if (t && !t.startsWith("#") && !t.toLowerCase().endsWith(".m3u8")) count++;
    }
    return count;
}

function buildLoadingPlaylistBody(request, env) {
    // Point to our own /loading.mp4 proxy so CORS is handled properly.
    // The MP4 is ~4:08 (248s). No #EXT-X-ENDLIST → player keeps polling.
    const base = publicBase(request, env);
    return [
        "#EXTM3U",
        "#EXT-X-VERSION:3",
        "#EXT-X-TARGETDURATION:248",
        "#EXT-X-MEDIA-SEQUENCE:0",
        "#EXTINF:248.0,",
        `${base}/loading.mp4`,
        "",
    ].join("\n");
}

// Proxy the loading MP4 through our server with CORS headers
let loadingVideoCache = null; // { fetchedAt, response: { body, headers, status } }

async function proxyLoadingVideo(env, request) {
    const videoUrl = envString(env, "LOADING_VIDEO_URL", LOADING_VIDEO_URL);
    const headers = {
        "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
    };
    // Forward range requests so players can seek
    if (request.headers.get("range")) headers.range = request.headers.get("range");

    const upstream = await fetch(videoUrl, { method: request.method, headers, redirect: "follow" });

    const respHeaders = new Headers(upstream.headers);
    respHeaders.set("access-control-allow-origin", "*");
    respHeaders.set("access-control-allow-methods", "GET, HEAD, OPTIONS");
    respHeaders.set("access-control-expose-headers", "Content-Length, Content-Range, Accept-Ranges");
    respHeaders.set("cache-control", "public, max-age=3600, s-maxage=3600");
    if (!respHeaders.has("content-type")) respHeaders.set("content-type", "video/mp4");
    respHeaders.set("accept-ranges", "bytes");

    return new Response(upstream.body, { status: upstream.status, headers: respHeaders });
}

function cleanupWarmupState() {
    const now = Date.now();
    for (const [k, state] of streamWarmupState) {
        if (now - state.startedAt > WARMUP_EXPIRY_MS) streamWarmupState.delete(k);
    }
    if (streamWarmupState.size > MAX_WARMUP_ENTRIES) {
        const keys = [...streamWarmupState.keys()];
        for (let i = 0; i < keys.length - MAX_WARMUP_ENTRIES; i++) streamWarmupState.delete(keys[i]);
    }
}

async function proxyProgressiveStream(sourceUrl, request, env) {
    const maxRetries = envInt(env, "SEGMENT_FETCH_RETRIES", 2);
    const timeoutMs = envInt(env, "SEGMENT_FETCH_TIMEOUT_MS", 8000);
    const headers = {
        "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
        connection: "keep-alive",
    };
    if (request && request.headers.get("range")) headers.range = request.headers.get("range");
    if (request && request.headers.get("if-range")) headers["if-range"] = request.headers.get("if-range");

    for (let attempt = 0; attempt <= maxRetries; attempt++) {
        if (isCircuitOpen(sourceUrl)) {
            console.warn(`[progressive-stream] circuit open for ${circuitBreakerKey(sourceUrl)}, skipping`);
            throw new HttpError(503, "Upstream stream temporarily unavailable (circuit breaker open).");
        }
        const startMs = Date.now();
        try {
            const response = await fetchWithTimeout(sourceUrl, {
                method: request ? request.method : "GET",
                headers,
                redirect: "follow",
            }, timeoutMs);
            const latency = Date.now() - startMs;
            trackUpstreamRequest(sourceUrl, response.ok, latency);
            if (response.ok || (response.status >= 200 && response.status < 400)) {
                recordCircuitSuccess(sourceUrl);
                
                const proxyHeaders = new Headers(response.headers);
                proxyHeaders.set("access-control-allow-origin", "*");
                if (proxyHeaders.has("transfer-encoding")) proxyHeaders.delete("content-length");
                
                if (attempt > 0) console.log(`[progressive-stream] succeeded on retry ${attempt} for ${sanitizeUrlForLog(sourceUrl)}`);
                return new Response(response.body, { status: response.status, headers: proxyHeaders });
            }
            if (response.status >= 400 && response.status < 500 && response.status !== 408 && response.status !== 429) {
                return new Response(response.body, { status: response.status, headers: response.headers });
            }
            if (attempt < maxRetries) {
                const delayMs = 200 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
                await new Promise((resolve) => setTimeout(resolve, delayMs));
            }
        } catch (err) {
            const latency = Date.now() - startMs;
            trackUpstreamRequest(sourceUrl, false, latency);
            recordCircuitFailure(sourceUrl);
            if (attempt >= maxRetries) {
                console.error(`[progressive-stream] FAILED all ${maxRetries + 1} attempts for ${sanitizeUrlForLog(sourceUrl)}: ${err.message}`);
                throw new HttpError(502, "Upstream stream fetch failed.");
            }
            const delayMs = 200 * Math.pow(2, attempt) * (0.5 + Math.random() * 0.5);
            await new Promise((resolve) => setTimeout(resolve, delayMs));
        }
    }
    throw new HttpError(502, "Upstream stream fetch failed.");
}

async function proxyLiveFromSource(key, sourceUrl, request, env, waitUntil, cacheKey) {
    const warmupEnabled = envBool(env, "LOADING_VIDEO_ENABLED", true);
    const requiredSegments = envInt(env, "WARMUP_REQUIRED_SEGMENTS", WARMUP_REQUIRED_SEGMENTS);
    const now = Date.now();
    const freshMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_CACHE_MS", 2000));
    const staleMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_STALE_MS", 15000));
    const cached = livePlaylistCache.get(cacheKey);

    // ── Warmup: play the loading MP4 while upstream HLS stabilises ───────────
    if (warmupEnabled && requiredSegments > 0) {
        let warmup = streamWarmupState.get(cacheKey);

        if (!warmup) {
            // First hit — start warmup, kick off upstream probe in background
            cleanupWarmupState();
            warmup = { startedAt: now, ready: false, segmentsSeen: 0 };
            streamWarmupState.set(cacheKey, warmup);
            console.log(`[warmup] key=${key} → serving loading video while upstream buffers`);

            // Probe upstream in background so it's ready on next poll
            waitUntil((async () => {
                try {
                    const upstream = await findUpstreamHls(key, sourceUrl, env);
                    const w = streamWarmupState.get(cacheKey);
                    if (w && upstream) {
                        w.segmentsSeen = countUpstreamSegments(upstream.text);
                        if (w.segmentsSeen >= requiredSegments) {
                            w.ready = true;
                            console.log(`[warmup] key=${key} READY (${w.segmentsSeen} segments)`);
                        }
                    }
                } catch (e) { console.warn(`[warmup] key=${key} probe failed: ${e?.message}`); }
            })());

            return playlistResponse(buildLoadingPlaylistBody(request, env));
        }

        if (!warmup.ready) {
            // Safety timeout — don't show loading forever
            const timeoutMs = envInt(env, "WARMUP_TIMEOUT_MS", 15000);
            if (now - warmup.startedAt > timeoutMs) {
                console.warn(`[warmup] key=${key} timed out after ${timeoutMs}ms, forcing live`);
                warmup.ready = true;
            } else {
                // Re-probe upstream on each poll
                try {
                    const upstream = await findUpstreamHls(key, sourceUrl, env);
                    if (upstream) {
                        warmup.segmentsSeen = Math.max(warmup.segmentsSeen, countUpstreamSegments(upstream.text));
                        if (warmup.segmentsSeen >= requiredSegments) {
                            warmup.ready = true;
                            console.log(`[warmup] key=${key} READY (${warmup.segmentsSeen} segments)`);
                        }
                    }
                } catch (_) { /* will retry next poll */ }

                if (!warmup.ready) {
                    console.log(`[warmup] key=${key} still buffering (${warmup.segmentsSeen}/${requiredSegments} segments)`);
                    return playlistResponse(buildLoadingPlaylistBody(request, env));
                }
            }
        }
        // Warmup done — fall through to real stream
    }

    // ── Normal live playlist ─────────────────────────────────────────────────
    if (cached && now - cached.at < freshMs) return playlistResponse(cached.body);
    try {
        const body = await buildLivePlaylistBody(key, sourceUrl, request, env, waitUntil, cacheKey);
        return playlistResponse(body);
    } catch (error) {
        if (cached && now - cached.at < staleMs) return playlistResponse(cached.body);
        throw error;
    }
}

async function proxyChannelPlaylist(key, request, env, waitUntil) {
    const requestUrl = new URL(request.url);
    const srcToken = requestUrl.searchParams.get("src");
    if (srcToken) {
        const tokenData = await readUrlToken(srcToken, env);
        return proxyLiveFromSource(key, tokenData.u, request, env, waitUntil, `live:${key}:${srcToken}`);
    }
    const channel = await getStreamForKey(key, env);
    const maxStreamRetries = envInt(env, "STREAM_PLAY_RETRIES", 2);

    // ── Tier 1: retry the current source URL with backoff ───────────────
    for (let attempt = 0; attempt <= maxStreamRetries; attempt++) {
        try {
            const result = await proxyLiveFromSource(key, channel.sourceUrl, request, env, waitUntil, `live:${key}`);
            if (attempt > 0) console.log(`[stream-retry] key ${key} succeeded on attempt ${attempt + 1}`);
            return result;
        } catch (err) {
            console.warn(`[stream-retry] key ${key} attempt ${attempt + 1}/${maxStreamRetries + 1} failed: ${err?.message || err}`);
            upstreamHlsCache.delete(key);
            livePlaylistCache.delete(`live:${key}`);
            if (attempt < maxStreamRetries) {
                const delayMs = 300 * Math.pow(2, attempt);
                await new Promise((resolve) => setTimeout(resolve, delayMs));
            }
        }
    }

    // ── Tier 2: refresh channels and try the (possibly updated) source URL
    console.warn(`[stream-retry] key ${key} exhausted retries. Refreshing channel list...`);
    try { await doRefreshChannels(env); } catch (refreshErr) {
        console.error(`[stream-retry] channel refresh failed: ${refreshErr?.message}`);
    }
    const freshSourceUrl = streamIndex.get(key);
    if (freshSourceUrl && freshSourceUrl !== channel.sourceUrl) {
        console.log(`[stream-retry] key ${key} source URL changed after refresh, trying new URL...`);
        upstreamHlsCache.delete(key);
        livePlaylistCache.delete(`live:${key}`);
        try {
            return await proxyLiveFromSource(key, freshSourceUrl, request, env, waitUntil, `live:${key}`);
        } catch (err) {
            console.error(`[stream-retry] key ${key} also failed with refreshed URL: ${err?.message}`);
        }
    }

    // ── Tier 3: scan ALL provider sources for the same channel key ──────
    const allSources = buildProviderPlaylistSources(env);
    if (allSources.length > 1) {
        console.warn(`[stream-retry] key ${key} trying ${allSources.length} alternative IPTV sources...`);
        for (const source of allSources) {
            try {
                const catalog = await loadXtreamCatalog(env, source, "live", true).catch(() => null);
                if (!catalog) continue;
                for (const item of catalog.items) {
                    const id = itemId(item, "live");
                    if (!id) continue;
                    const ext = cleanString(item.container_extension, "ts");
                    const candidateUrl = xtreamMediaUrl(catalog.config, "live", id, ext);
                    const candidateKey = await streamKey(candidateUrl);
                    if (candidateKey === key) {
                        console.log(`[stream-retry] key ${key} found in source ${source.label}, attempting...`);
                        upstreamHlsCache.delete(key);
                        livePlaylistCache.delete(`live:${key}`);
                        streamIndex.set(key, candidateUrl);
                        try {
                            return await proxyLiveFromSource(key, candidateUrl, request, env, waitUntil, `live:${key}`);
                        } catch (sourceErr) {
                            console.warn(`[stream-retry] key ${key} failed from source ${source.label}: ${sourceErr?.message}`);
                        }
                    }
                }
            } catch (scanErr) {
                console.warn(`[stream-retry] scanning source ${source.label} failed: ${scanErr?.message}`);
            }
        }
    }

    console.error(`[stream-retry] key ${key} EXHAUSTED ALL OPTIONS. Stream unavailable.`);
    throw new HttpError(502, "Upstream HLS unavailable after all retries and source rotation.");
}

async function proxyDirectPlaylist(token, request, env, waitUntil) {
    const tokenData = await readUrlToken(token, env);
    const sourceUrl = tokenData.u;
    const key = await streamKey(sourceUrl);
    return proxyLiveFromSource(key, sourceUrl, request, env, waitUntil, `direct:${key}`);
}

async function buildNestedPlaylistBody(key, tokenData, request, env, waitUntil, cacheKey) {
    return withInflight(livePlaylistInflight, cacheKey, async () => {
        const fetched = (await fetchHls(tokenData.u, env, tokenData.r)) || (tokenData.f ? await fetchHls(tokenData.f, env, tokenData.r) : null);
        if (!fetched) throw new HttpError(502, "Upstream unavailable.");
        const body = await rewriteUpstreamPlaylist(fetched.text, fetched.finalUrl, request, env, key);
        const prefetchCount = Math.max(0, envInt(env, "PREFETCH_SEGMENTS", 2));
        const segmentUrls = extractPrefetchSegmentUrls(fetched.text, fetched.finalUrl, env, prefetchCount);
        rememberMapEntry(livePlaylistCache, cacheKey, { at: Date.now(), body }, MAX_LIVE_PLAYLIST_CACHE_ENTRIES);
        if (segmentUrls.length > 0) waitUntil(prefetchSegments(segmentUrls, fetched.finalUrl, env));
        return body;
    });
}

async function proxyNestedPlaylist(key, token, request, env, waitUntil) {
    validateKey(key);
    const tokenData = await readUrlToken(token, env);
    const cacheKey = `uplive:${key}:${tokenData.u}`;
    const now = Date.now();
    const freshMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_CACHE_MS", 2000));
    const staleMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_STALE_MS", 15000));
    const cached = livePlaylistCache.get(cacheKey);
    if (cached && now - cached.at < freshMs) return playlistResponse(cached.body);
    try {
        const body = await buildNestedPlaylistBody(key, tokenData, request, env, waitUntil, cacheKey);
        return playlistResponse(body);
    } catch (error) {
        if (cached && now - cached.at < staleMs) return playlistResponse(cached.body);
        throw error;
    }
}

async function proxySegment(key, token, filename, request, env) {
    validateKey(key);
    globalRequestCount++;
    const tokenData = await readUrlToken(token, env);
    const referer = tokenData.r || tokenData.u;
    const ttlSeconds = Math.max(1, envInt(env, "SEGMENT_CACHE_SECONDS", 30));
    const cdnTtlSeconds = Math.max(ttlSeconds, envInt(env, "CDN_SEGMENT_CACHE_SECONDS", 120));

    const segmentUrl = tokenData.u;
    const hasRange = request && request.headers.get("range");

    if (hasRange) {
        // Direct proxy without caching for range requests
        const primary = await fetchUpstreamAsset(tokenData.u, referer, env, ttlSeconds, request);
        const fallback = (!primary || primary.status >= 400) && tokenData.f
            ? await fetchUpstreamAsset(tokenData.f, referer, env, ttlSeconds, request)
            : null;

        const upstream = fallback && fallback.ok ? fallback : primary;
        if (!upstream) throw new HttpError(502, "Upstream segment fetch failed.");
        if (!upstream.ok) return withCors(new Response(upstream.body, { status: upstream.status, headers: upstream.headers }));

        const headers = new Headers(upstream.headers);
        headers.set("cache-control", "no-store");
        headers.set("access-control-allow-origin", "*");
        return new Response(upstream.body, { status: upstream.status, statusText: upstream.statusText, headers });
    }

    // Check LRU cache
    const now = Date.now();
    const cachedEntry = segmentCache.get(segmentUrl);
    if (cachedEntry && (now - cachedEntry.at) < SEGMENT_CACHE_TTL_MS) {
        globalSegmentCacheHits++;
        const headers = new Headers();
        Object.entries(cachedEntry.headers).forEach(([k, v]) => headers.set(k, v));
        headers.set("x-segment-cache", "hit");
        
        // Add BunnyCDN optimizations
        headers.set("cache-control", `public, max-age=${ttlSeconds}, s-maxage=${cdnTtlSeconds}, stale-while-revalidate=60`);
        headers.set("cdn-cache-control", `max-age=${cdnTtlSeconds}`);
        headers.set("vary", "Accept-Encoding");
        headers.set("access-control-allow-origin", "*");

        return withCors(new Response(cachedEntry.body, {
            status: 200,
            headers
        }));
    }

    // Check inflight requests
    let inflightPromise = segmentInflight.get(segmentUrl);
    if (!inflightPromise) {
        inflightPromise = (async () => {
            const primary = await fetchUpstreamAsset(tokenData.u, referer, env, ttlSeconds, request);
            const fallback = (!primary || primary.status >= 400) && tokenData.f
                ? await fetchUpstreamAsset(tokenData.f, referer, env, ttlSeconds, request)
                : null;

            const upstream = fallback && fallback.ok ? fallback : primary;
            if (!upstream) throw new HttpError(502, "Upstream segment fetch failed.");

            const status = upstream.status;
            const statusText = upstream.statusText;
            const responseHeaders = {};
            upstream.headers.forEach((v, k) => {
                responseHeaders[k] = v;
            });

            let bodyBuffer;
            if (upstream.body) {
                const arrayBuf = await upstream.arrayBuffer();
                bodyBuffer = Buffer.from(arrayBuf);
            } else {
                bodyBuffer = Buffer.alloc(0);
            }

            return {
                status,
                statusText,
                headers: responseHeaders,
                body: bodyBuffer
            };
        })();

        segmentInflight.set(segmentUrl, inflightPromise);
        inflightPromise.finally(() => {
            segmentInflight.delete(segmentUrl);
        });
    }

    try {
        const result = await inflightPromise;
        if (result.status >= 200 && result.status < 300) {
            // Clean up cache size
            if (segmentCache.size >= MAX_SEGMENT_CACHE_ENTRIES) {
                const oldestKey = segmentCache.keys().next().value;
                if (oldestKey) segmentCache.delete(oldestKey);
            }
            segmentCache.set(segmentUrl, {
                at: Date.now(),
                headers: result.headers,
                body: result.body
            });
            globalSegmentCacheMisses++;
        }

        const headers = new Headers();
        Object.entries(result.headers).forEach(([k, v]) => headers.set(k, v));
        
        headers.set("cache-control", `public, max-age=${ttlSeconds}, s-maxage=${cdnTtlSeconds}, stale-while-revalidate=60`);
        headers.set("cdn-cache-control", `max-age=${cdnTtlSeconds}`);
        headers.set("vary", "Accept-Encoding");
        if (!headers.has("content-type")) headers.set("content-type", mediaTypeForPath(filename));
        
        headers.set("accept-ranges", "bytes");
        headers.set("access-control-allow-origin", "*");
        headers.set("access-control-allow-methods", "GET,HEAD,OPTIONS");
        headers.set("access-control-allow-headers", "*");
        headers.set("access-control-expose-headers", "Content-Length, Content-Range, Accept-Ranges, Content-Type");
        headers.set("x-content-type-options", "nosniff");
        headers.set("x-proxied-by", "node-express");
        headers.set("x-segment-cache", "miss");

        return withCors(new Response(result.body, {
            status: result.status,
            statusText: result.statusText,
            headers
        }));
    } catch (err) {
        throw err instanceof HttpError ? err : new HttpError(502, `Upstream segment proxy failed: ${err.message}`);
    }
}

// ─── Xtream Codes Protocol API ───────────────────────────────────────────────
// Allows IPTV apps (TiviMate, GSE, IPTV Smarters…) to discover live channels,
// movies and TV series via /player_api.php — exactly like a real Xtream server.
//
// In-memory indexes populated during API calls (good for the session lifetime;
// apps fetch then immediately play, so restarts between those events are rare).
const xtreamMovieUrlIndex = new Map();   // streamId → upstreamUrl
const xtreamEpisodeUrlIndex = new Map(); // episodeId → upstreamUrl

function xtreamServerInfo(request, env) {
    const base = publicBase(request, env);
    const parsed = new URL(base);
    const now = Math.floor(Date.now() / 1000);

    // Many IPTV apps hardcode 'http://' when building stream URLs.
    // If we return '443' in the 'port' field, the app will request 'http://domain:443',
    // which causes the connection to be immediately dropped by the CDN/Proxy (HTTP on HTTPS port).
    // So we must always provide a valid HTTP port in 'port', and HTTPS in 'https_port'.
    let httpPort = "80";
    let httpsPort = "443";
    if (parsed.port) {
        if (parsed.protocol === "https:") httpsPort = parsed.port;
        else httpPort = parsed.port;
    }

    return {
        url: parsed.hostname,
        port: httpPort,
        https_port: httpsPort,
        server_protocol: "http", // Always tell standard apps to use http (they will use port 80)
        rtmp_port: "1935",
        timezone: "UTC",
        timestamp_now: now,
        time_now: new Date().toISOString().replace("T", " ").slice(0, 19),
        process: true,
    };
}

function xtreamUserInfoPayload(user, request, env) {
    const now = Math.floor(Date.now() / 1000);
    const expDate = user.expiresAt ? Math.floor(new Date(user.expiresAt).getTime() / 1000) : null;
    return {
        user_info: {
            username: user.username,
            password: user.password,
            message: "",
            auth: 1,
            status: isAccessUserExpired(user) ? "Expired" : "Active",
            exp_date: expDate ? String(expDate) : null,
            is_trial: "0",
            active_cons: "1",
            created_at: user.createdAt ? String(Math.floor(new Date(user.createdAt).getTime() / 1000)) : String(now),
            max_connections: "10",
            allowed_output_formats: ["m3u8", "ts", "rtmpe"],
        },
        server_info: xtreamServerInfo(request, env),
    };
}

async function xtreamVodInfoPayload(env, vodId) {
    const id = cleanString(vodId);
    if (!id) return { info: {}, movie_data: {} };
    for (const source of buildProviderPlaylistSources(env)) {
        const catalog = await loadXtreamCatalog(env, source, "movies", false).catch(() => null);
        if (!catalog) continue;
        const item = catalog.itemsById.get(id);
        if (!item) continue;
        const ext = cleanString(item.container_extension, "mp4");
        return {
            info: {
                movie_image: mediaLogo(item),
                tmdb_id: cleanString(item.tmdb_id),
                backdrop_path: Array.isArray(item.backdrop_path) ? item.backdrop_path : [],
                youtube_trailer: cleanString(item.youtube_trailer),
                genre: cleanString(item.genre),
                plot: cleanString(item.plot),
                cast: cleanString(item.cast),
                rating: String(mediaRating(item) ?? ""),
                director: cleanString(item.director),
                releasedate: cleanString(item.releasedate ?? item.releaseDate ?? item.release_date),
                duration_secs: Number.parseInt(cleanString(item.duration_secs), 10) || 0,
                duration: cleanString(item.duration),
            },
            movie_data: {
                stream_id: Number(id),
                name: cleanString(item.name, "Unknown"),
                added: cleanString(item.added) || String(Math.floor(Date.now() / 1000)),
                category_id: cleanString(item.category_id),
                container_extension: ext,
            },
        };
    }
    return { info: {}, movie_data: { stream_id: Number(id) } };
}

function xtreamEmptyEpgPayload() {
    return { epg_listings: [] };
}

async function xtreamAllCategoriesPayload(request, env, user) {
    const [liveCategories, movieCategories, seriesCategories] = await Promise.all([
        xtreamLiveCategories(env).catch(() => []),
        xtreamVodCategories(env).catch(() => []),
        xtreamSeriesCategories(env).catch(() => []),
    ]);
    return {
        ...xtreamSuccessEnvelope(user, request, env),
        categories: liveCategories,
        live_categories: liveCategories,
        movie_categories: movieCategories,
        vod_categories: movieCategories,
        series_categories: seriesCategories,
    };
}

async function panelApiPayload(request, env, user) {
    const channels = await loadPlaylistChannels(env, false).catch(() => []);
    const liveCategories = await xtreamLiveCategories(env).catch(() => []);
    const vodCategories = await xtreamVodCategories(env).catch(() => []);
    const seriesCategories = await xtreamSeriesCategories(env).catch(() => []);
    return json({
        user_info: xtreamUserInfoPayload(user, request, env).user_info,
        server_info: xtreamServerInfo(request, env),
        categories: {
            live: liveCategories,
            movie: vodCategories,
            series: seriesCategories,
        },
        available_channels: channels.map((channel) => ({
            stream_id: channel.key,
            stream_display_name: channel.name,
            stream_icon: channel.logo,
            category_id: channel.category || "Live",
            direct_source: "",
        })),
    });
}

function aggregateXtreamCategories(catalogs) {
    const seen = new Set();
    const result = [];
    for (const catalog of catalogs) {
        if (!catalog) continue;
        for (const [id, name] of catalog.categoriesById.entries()) {
            if (seen.has(id)) continue;
            seen.add(id);
            result.push({ category_id: id, category_name: name, parent_id: 0 });
        }
    }
    if (result.length === 0) result.push({ category_id: "1", category_name: "All", parent_id: 0 });
    return result;
}

function xtreamFallbackCategoryId(name) {
    const text = normalizeSearchText(name).replace(/\s+/g, "_");
    return text || "all";
}

function stringToNumericId(str) {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
        hash = ((hash << 5) - hash) + str.charCodeAt(i);
        hash |= 0;
    }
    return Math.abs(hash) || 1;
}

function localXtreamLiveCategories(channels) {
    const categories = new Map();
    for (const channel of channels) {
        const categoryName = cleanString(channel?.category, "Live");
        const categoryId = String(stringToNumericId(xtreamFallbackCategoryId(categoryName)));
        if (!categories.has(categoryId)) {
            categories.set(categoryId, {
                category_id: categoryId,
                category_name: categoryName,
                parent_id: 0,
            });
        }
    }
    if (categories.size === 0) {
        categories.set("1", { category_id: "1", category_name: "All", parent_id: 0 });
    }
    return [...categories.values()];
}

function xtreamLivePlaybackUrl(request, env, user, streamId) {
    if (!request || !user || !streamId) return "";
    const base = publicBase(request, env);
    return `${base}/live/${encodePathSegment(user.username)}/${encodePathSegment(user.password)}/${encodePathSegment(streamId)}.ts`;
}

function localXtreamLiveStreams(channels, categoryId = "", request = null, env = process.env, user = null) {
    const wantedCategoryId = cleanString(categoryId);
    const result = [];
    let num = 1;
    for (const channel of channels) {
        const categoryName = cleanString(channel?.category, "Live");
        const liveCategoryId = String(stringToNumericId(xtreamFallbackCategoryId(categoryName)));
        if (wantedCategoryId && wantedCategoryId !== "0" && wantedCategoryId !== liveCategoryId) continue;

        const numericStreamId = String(stringToNumericId(channel.key));
        xtreamLocalNumericIndex.set(numericStreamId, channel.key);

        const streamUrl = xtreamLivePlaybackUrl(request, env, user, numericStreamId);
        result.push({
            num: num++,
            name: cleanString(channel?.name, "Unknown"),
            stream_type: "live",
            stream_id: Number(numericStreamId),
            stream_icon: cleanString(channel?.logo),
            epg_channel_id: null,
            added: String(Math.floor(Date.now() / 1000)),
            is_adult: "0",
            category_id: liveCategoryId,
            custom_sid: "",
            tv_archive: 1,
            direct_source: "",
            tv_archive_duration: 0,
            container_extension: "ts",
        });
    }
    return result;
}

async function xtreamLiveCategories(env) {
    const custom = await loadCustomCategories(env);
    if (custom && custom.length > 0) {
        const result = custom.map(c => ({
            category_id: c.id,
            category_name: c.name,
            parent_id: 0
        })).sort((a, b) => {
            const oa = custom.find(x => x.id === a.category_id)?.order || 0;
            const ob = custom.find(x => x.id === b.category_id)?.order || 0;
            return oa - ob;
        });

        result.push({
            category_id: "999999",
            category_name: "Uncategorized",
            parent_id: 0
        });
        return result;
    }

    const sources = buildProviderPlaylistSources(env);
    const catalogs = await Promise.all(sources.map((s) => loadXtreamCatalog(env, s, "live", false, false).catch(() => null)));
    const liveCategories = aggregateXtreamCategories(catalogs);
    if (liveCategories.length > 1 || (liveCategories.length === 1 && liveCategories[0]?.category_id !== "1")) {
        return liveCategories;
    }

    const channels = await loadPlaylistChannels(env, false).catch(() => []);
    if (channels.length > 0) return localXtreamLiveCategories(channels);

    return liveCategories;
}

async function xtreamLiveStreams(env, categoryId = "", request = null, user = null) {
    const custom = await loadCustomCategories(env);
    const wantedCategoryId = cleanString(categoryId);

    if (custom && custom.length > 0) {
        const channelMap = new Map();
        const channels = await loadPlaylistChannels(env, false).catch(() => []);
        for (const ch of channels) channelMap.set(ch.key, { ...ch, is_xtream: false });

        const sources = buildProviderPlaylistSources(env);
        for (const source of sources) {
            const catalog = await loadXtreamCatalog(env, source, "live", false).catch(() => null);
            if (catalog) {
                for (const item of catalog.items) {
                    const id = itemId(item, "live");
                    if (id) {
                        channelMap.set(id, {
                            key: id,
                            name: cleanString(item.name, "Unknown"),
                            logo: mediaLogo(item),
                            category: cleanString(item.category_id),
                            is_xtream: true,
                            xtream_item: item
                        });
                    }
                }
            }
        }

        const result = [];
        let num = 1;

        const sortedCategories = [...custom].sort((a, b) => a.order - b.order);
        const mappedKeys = new Set();

        for (const cat of sortedCategories) {
            for (const key of cat.channelKeys) mappedKeys.add(key);
            if (wantedCategoryId && wantedCategoryId !== "0" && cat.id !== wantedCategoryId) continue;
            for (const key of cat.channelKeys) {
                const channel = channelMap.get(key);
                if (!channel) continue;
                if (!channel.is_xtream) {
                    const numericStreamId = String(stringToNumericId(channel.key));
                    xtreamLocalNumericIndex.set(numericStreamId, channel.key);
                    result.push({
                        num: num++,
                        name: channel.name,
                        stream_type: "live",
                        stream_id: Number(numericStreamId),
                        stream_icon: channel.logo,
                        epg_channel_id: null,
                        added: String(Math.floor(Date.now() / 1000)),
                        is_adult: "0",
                        category_id: cat.id,
                        custom_sid: "",
                        tv_archive: 1,
                        direct_source: "",
                        tv_archive_duration: 0,
                        container_extension: "ts",
                    });
                } else {
                    const item = channel.xtream_item;
                    result.push({
                        num: num++,
                        name: channel.name,
                        stream_type: "live",
                        stream_id: Number(channel.key),
                        stream_icon: channel.logo,
                        epg_channel_id: null,
                        added: cleanString(item.added) || String(Math.floor(Date.now() / 1000)),
                        is_adult: "0",
                        category_id: cat.id,
                        custom_sid: "",
                        tv_archive: 1,
                        direct_source: "",
                        tv_archive_duration: 0,
                        container_extension: "ts",
                    });
                }
            }
        }

        if (wantedCategoryId === "999999" || (!wantedCategoryId || wantedCategoryId === "0")) {
            for (const channel of channelMap.values()) {
                if (!mappedKeys.has(channel.key)) {
                    if (!channel.is_xtream) {
                        const numericStreamId = String(stringToNumericId(channel.key));
                        xtreamLocalNumericIndex.set(numericStreamId, channel.key);
                        result.push({
                            num: num++,
                            name: channel.name,
                            stream_type: "live",
                            stream_id: Number(numericStreamId),
                            stream_icon: channel.logo,
                            epg_channel_id: null,
                            added: String(Math.floor(Date.now() / 1000)),
                            is_adult: "0",
                            category_id: "999999",
                            custom_sid: "",
                            tv_archive: 1,
                            direct_source: "",
                            tv_archive_duration: 0,
                            container_extension: "ts",
                        });
                    } else {
                        const item = channel.xtream_item;
                        result.push({
                            num: num++,
                            name: channel.name,
                            stream_type: "live",
                            stream_id: Number(channel.key),
                            stream_icon: channel.logo,
                            epg_channel_id: null,
                            added: cleanString(item.added) || String(Math.floor(Date.now() / 1000)),
                            is_adult: "0",
                            category_id: "999999",
                            custom_sid: "",
                            tv_archive: 1,
                            direct_source: "",
                            tv_archive_duration: 0,
                            container_extension: "ts",
                        });
                    }
                }
            }
        }
        return result;
    }

    const sources = buildProviderPlaylistSources(env);
    const result = [];
    const seenIds = new Set();
    let num = 1;
    for (const source of sources) {
        const catalog = await loadXtreamCatalog(env, source, "live", false).catch(() => null);
        if (!catalog) continue;
        for (const item of catalog.items) {
            const id = itemId(item, "live");
            if (!id || seenIds.has(id)) continue;
            if (wantedCategoryId && wantedCategoryId !== "0" && cleanString(item.category_id) !== wantedCategoryId) continue;
            seenIds.add(id);
            const streamUrl = xtreamLivePlaybackUrl(request, env, user, id);
            result.push({
                num: num++,
                name: cleanString(item.name, "Unknown"),
                stream_type: "live",
                stream_id: Number(id),
                stream_icon: mediaLogo(item),
                epg_channel_id: null,
                added: cleanString(item.added) || String(Math.floor(Date.now() / 1000)),
                is_adult: "0",
                category_id: cleanString(item.category_id),
                custom_sid: "",
                tv_archive: 0,
                direct_source: "",
                tv_archive_duration: 0,
            });
        }
    }
    if (result.length > 0) return result;

    const channels = await loadPlaylistChannels(env, false).catch(() => []);
    if (channels.length === 0) return result;
    return localXtreamLiveStreams(channels, wantedCategoryId, request, env, user);
}

async function xtreamVodCategories(env) {
    const sources = buildProviderPlaylistSources(env);
    const catalogs = await Promise.all(sources.map((s) => loadXtreamCatalog(env, s, "movies", false, false).catch(() => null)));
    const returnVal = aggregateXtreamCategories(catalogs);
    return returnVal;
}

async function xtreamVodStreams(env, categoryId = "") {
    const sources = buildProviderPlaylistSources(env);
    const result = [];
    const seenIds = new Set();
    const wantedCategoryId = cleanString(categoryId);
    let num = 1;
    for (const source of sources) {
        const catalog = await loadXtreamCatalog(env, source, "movies", false).catch(() => null);
        if (!catalog) continue;
        for (const item of catalog.items) {
            const id = itemId(item, "movies");
            if (!id || seenIds.has(id)) continue;
            if (wantedCategoryId && wantedCategoryId !== "0" && cleanString(item.category_id) !== wantedCategoryId) continue;
            seenIds.add(id);
            const ext = cleanString(item.container_extension, "mp4");
            const upstreamUrl = xtreamMediaUrl(catalog.config, "movie", String(id), ext);
            xtreamMovieUrlIndex.set(String(id), upstreamUrl); // populate index
            result.push({
                num: num++,
                name: cleanString(item.name, "Unknown"),
                stream_type: "movie",
                stream_id: Number(id),
                stream_icon: mediaLogo(item),
                rating: String(mediaRating(item) ?? ""),
                rating_5based: String(mediaRating(item) ?? ""),
                added: cleanString(item.added) || String(Math.floor(Date.now() / 1000)),
                category_id: cleanString(item.category_id),
                container_extension: ext,
                custom_sid: "",
                direct_source: "",
            });
        }
    }
    return result;
}

async function xtreamSeriesCategories(env) {
    const sources = buildProviderPlaylistSources(env);
    const catalogs = await Promise.all(sources.map((s) => loadXtreamCatalog(env, s, "series", false, false).catch(() => null)));
    return aggregateXtreamCategories(catalogs);
}

async function xtreamSeriesList(env, categoryId = "") {
    const sources = buildProviderPlaylistSources(env);
    const result = [];
    const seenIds = new Set();
    const wantedCategoryId = cleanString(categoryId);
    let num = 1;
    for (const source of sources) {
        const catalog = await loadXtreamCatalog(env, source, "series", false).catch(() => null);
        if (!catalog) continue;
        for (const item of catalog.items) {
            const id = itemId(item, "series");
            if (!id || seenIds.has(id)) continue;
            if (wantedCategoryId && wantedCategoryId !== "0" && cleanString(item.category_id) !== wantedCategoryId) continue;
            seenIds.add(id);
            result.push({
                num: num++,
                name: cleanString(item.name, "Unknown"),
                series_id: Number(id),
                cover: mediaLogo(item),
                plot: cleanString(item.plot),
                cast: cleanString(item.cast),
                director: cleanString(item.director),
                genre: cleanString(item.genre),
                releaseDate: cleanString(item.releaseDate ?? item.release_date),
                last_modified: cleanString(item.last_modified) || String(Math.floor(Date.now() / 1000)),
                rating: String(mediaRating(item) ?? ""),
                rating_5based: String(mediaRating(item) ?? ""),
                backdrop_path: Array.isArray(item.backdrop_path) ? item.backdrop_path : [],
                youtube_trailer: cleanString(item.youtube_trailer),
                episode_run_time: cleanString(item.episode_run_time),
                category_id: cleanString(item.category_id),
            });
        }
    }
    return result;
}

async function xtreamSeriesInfoPayload(env, seriesId) {
    const sources = buildProviderPlaylistSources(env);
    for (const source of sources) {
        const infoEntry = await loadXtreamSeriesInfo(env, source, seriesId, false).catch(() => null);
        if (!infoEntry?.payload) continue;
        const { payload, config } = infoEntry;
        const episodesOut = {};
        const groups = payload.episodes;
        if (groups && typeof groups === "object") {
            for (const [season, eps] of Object.entries(groups)) {
                episodesOut[season] = Array.isArray(eps)
                    ? eps.map((ep) => {
                        const epId = cleanString(ep?.id ?? ep?.stream_id);
                        const ext = cleanString(ep?.container_extension ?? ep?.info?.container_extension, "mp4");
                        if (epId) {
                            const upUrl = directEpisodeUrl(config, ep);
                            if (upUrl) xtreamEpisodeUrlIndex.set(String(epId), upUrl); // populate index
                        }
                        return { ...ep, id: Number(epId) || epId, stream_id: Number(epId) || epId };
                    })
                    : [];
            }
        }
        return { seasons: payload.seasons ?? [], info: payload.info ?? {}, episodes: episodesOut };
    }
    return { seasons: [], info: {}, episodes: {} };
}

function escapeXml(value) {
    return String(value ?? "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/\"/g, "&quot;")
        .replace(/'/g, "&apos;");
}

function xtreamSuccessEnvelope(user, request, env) {
    return {
        status: "ok",
        user_info: xtreamUserInfoPayload(user, request, env).user_info,
        server_info: xtreamServerInfo(request, env),
    };
}

async function xtreamSystemApiPayload(request, env, user, action = "") {
    const base = xtreamSuccessEnvelope(user, request, env);
    const url = new URL(request.url);

    if (action === "get_main_info" || action === "get_version" || action === "get_settings") {
        return {
            ...base,
            system_info: {
                project: "xtream-compatible",
                endpoint: url.pathname,
                live_categories: (await xtreamLiveCategories(env).catch(() => [])).length,
                movie_categories: (await xtreamVodCategories(env).catch(() => [])).length,
                series_categories: (await xtreamSeriesCategories(env).catch(() => [])).length,
            },
        };
    }

    if (action === "get_live_categories") return { ...base, categories: await xtreamLiveCategories(env) };
    if (action === "get_all_categories") return xtreamAllCategoriesPayload(request, env, user);
    if (action === "get_vod_categories") return { ...base, categories: await xtreamVodCategories(env) };
    if (action === "get_series_categories") return { ...base, categories: await xtreamSeriesCategories(env) };
    if (action === "get_live_streams") return { ...base, streams: await xtreamLiveStreams(env, cleanString(url.searchParams.get("category_id")), request, user) };
    if (action === "get_vod_streams") return { ...base, streams: await xtreamVodStreams(env, cleanString(url.searchParams.get("category_id"))) };
    if (action === "get_series") return { ...base, streams: await xtreamSeriesList(env, cleanString(url.searchParams.get("category_id"))) };

    return base;
}

function xtreamPortalHtml(request, env, user) {
    const base = publicBase(request, env);
    const login = encodeURIComponent(`${user.username}:${user.password}`);
    return htmlResponse(`<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Xtream Portal</title>
  <style>
    body { font-family: system-ui, sans-serif; margin: 0; padding: 32px; background: #0f1115; color: #f5f7fb; }
    .card { max-width: 760px; margin: 0 auto; background: #181b22; border: 1px solid #313746; border-radius: 10px; padding: 24px; }
    a { color: #4fc3a1; }
    code { display: block; white-space: pre-wrap; background: #11141a; padding: 12px; border-radius: 8px; overflow-wrap: anywhere; }
  </style>
</head>
<body>
  <div class="card">
    <h1>Xtream Portal</h1>
    <p>This server exposes Xtream-compatible endpoints for receivers and apps that probe portal URLs first.</p>
    <p><a href="${base}/player_api.php?username=${encodeURIComponent(user.username)}&password=${encodeURIComponent(user.password)}">player_api.php</a></p>
    <code>${base}/get.php?username=${encodeURIComponent(user.username)}&password=${encodeURIComponent(user.password)}&type=m3u_plus</code>
    <p>Login: <code>${login}</code></p>
  </div>
</body>
</html>`);
}

async function enigma2XmlPayload(request, env, user, action = "") {
    const url = new URL(request.url);
    const channels = await xtreamLiveStreams(env, cleanString(url.searchParams.get("category_id")), request, user).catch(() => []);
    const base = publicBase(request, env);

    const bouquetItems = channels.map((channel) => {
        const streamUrl = `${base}/live/${encodeURIComponent(user.username)}/${encodeURIComponent(user.password)}/${encodeURIComponent(channel.stream_id)}.m3u8`;
        return `    <service>\n      <name>${escapeXml(channel.name)}</name>\n      <stream_id>${escapeXml(channel.stream_id)}</stream_id>\n      <stream_url>${escapeXml(streamUrl)}</stream_url>\n      <category>${escapeXml(channel.category_id || "Live")}</category>\n    </service>`;
    }).join("\n");

    const header = `<?xml version="1.0" encoding="UTF-8"?>\n<enigma2 action="${escapeXml(action || "getservices")}">`;
    const body = bouquetItems || "    <service />";
    return withCors(new Response(`${header}\n  <user>${escapeXml(user.username)}</user>\n  <services>\n${body}\n  </services>\n</enigma2>\n`, {
        headers: { "content-type": "application/xml; charset=utf-8", "cache-control": "no-store" },
    }));
}

// Auth helper reused by stream URL handlers
async function requireXtreamAuth(username, password) {
    const user = await resolveXtreamUser(process.env, username, password);
    if (!user) throw new HttpError(403, "Invalid credentials.");
    return user;
}

// Look up live source URL from catalogs by stream_id
async function findXtreamLiveUrl(env, streamId) {
    const cachedSourceUrl = streamIndex.get(String(streamId));
    if (cachedSourceUrl) return cachedSourceUrl;
    for (const source of buildProviderPlaylistSources(env)) {
        const catalog = await loadXtreamCatalog(env, source, "live", false).catch(() => null);
        if (!catalog) continue;
        const item = catalog.itemsById.get(String(streamId));
        if (item) {
            const ext = cleanString(item.container_extension, "ts");
            return xtreamMediaUrl(catalog.config, "live", String(streamId), ext);
        }
    }
    return null;
}

// Look up movie URL by stream_id (index first, then catalog scan)
async function findXtreamMovieUrl(env, streamId) {
    const cached = xtreamMovieUrlIndex.get(String(streamId));
    if (cached) return cached;
    for (const source of buildProviderPlaylistSources(env)) {
        const catalog = await loadXtreamCatalog(env, source, "movies", false).catch(() => null);
        if (!catalog) continue;
        const item = catalog.itemsById.get(String(streamId));
        if (item) {
            const ext = cleanString(item.container_extension, "mp4");
            const url = xtreamMediaUrl(catalog.config, "movie", String(streamId), ext);
            xtreamMovieUrlIndex.set(String(streamId), url);
            return url;
        }
    }
    return null;
}

// Look up episode URL by episode_id (populated when get_series_info is called)
async function findXtreamEpisodeUrl(episodeId) {
    return xtreamEpisodeUrlIndex.get(String(episodeId)) ?? null;
}

async function handleXtreamApi(request, env, waitUntil) {
    const url = new URL(request.url);
    const username = cleanString(url.searchParams.get("username"));
    const password = cleanString(url.searchParams.get("password"));
    const action = cleanString(url.searchParams.get("action"));
    const categoryId = cleanString(url.searchParams.get("category_id"));

    // Authenticate
    const user = await resolveXtreamUser(env, username, password);
    if (!user) {
        const payload = { user_info: { username, password, auth: 0, status: "Disabled" } };
        logXtreamAction(request, action || "auth_failed", payload);
        return json(payload);
    }

    // ── Fast response cache for heavy list actions ────────────────────────────
    // These actions build large payloads from upstream APIs + channel lists.
    // Cache the pre-built JSON so IPTV receivers get instant responses.
    const CACHEABLE_ACTIONS = new Set([
        "get_live_categories", "get_live_streams", "get_all_categories",
        "get_vod_categories", "get_vod_streams",
        "get_series_categories", "get_series",
        "get_all_channels", "get_all_streams", "get_all_live_streams",
    ]);

    if (action && CACHEABLE_ACTIONS.has(action)) {
        const responseCacheKey = `xtream:${action}:${categoryId || "all"}`;
        const cached = xtreamResponseCache.get(responseCacheKey);
        const now = Date.now();
        const freshMs = XTREAM_RESPONSE_CACHE_TTL_MS;      // 2 min fresh
        const staleMs = freshMs * 2;                         // 4 min stale-while-revalidate

        if (cached) {
            const age = now - cached.at;
            if (age < freshMs) {
                // Fresh cache hit — return instantly
                return withCors(new Response(cached.jsonStr, {
                    headers: { "content-type": "application/json; charset=utf-8", "x-cache": "HIT" },
                }));
            }
            if (age < staleMs) {
                // Stale — return cached but refresh in background
                waitUntil((async () => {
                    try {
                        const payload = await buildXtreamPayload(action, env, categoryId, request, user);
                        const jsonStr = JSON.stringify(payload);
                        rememberMapEntry(xtreamResponseCache, responseCacheKey, { at: Date.now(), jsonStr }, MAX_XTREAM_RESPONSE_CACHE_ENTRIES);
                    } catch (e) { console.warn(`[xtream-cache] background refresh failed for ${action}: ${e?.message}`); }
                })());
                return withCors(new Response(cached.jsonStr, {
                    headers: { "content-type": "application/json; charset=utf-8", "x-cache": "STALE" },
                }));
            }
        }

        // Cache miss — build and cache
        const payload = await buildXtreamPayload(action, env, categoryId, request, user);
        const jsonStr = JSON.stringify(payload);
        rememberMapEntry(xtreamResponseCache, responseCacheKey, { at: now, jsonStr }, MAX_XTREAM_RESPONSE_CACHE_ENTRIES);
        logXtreamAction(request, action, payload, { categoryId });
        return withCors(new Response(jsonStr, {
            headers: { "content-type": "application/json; charset=utf-8", "x-cache": "MISS" },
        }));
    }

    // ── Non-cacheable actions (auth info, per-item lookups, EPG) ──────────────
    let payload;
    let logExtra = {};
    if (!action) {
        payload = xtreamUserInfoPayload(user, request, env);
    } else if (action === "get_vod_info") {
        const vodId = cleanString(url.searchParams.get("vod_id") || url.searchParams.get("movie_id") || url.searchParams.get("stream_id"));
        payload = await xtreamVodInfoPayload(env, vodId);
        logExtra = { id: vodId };
    } else if (action === "get_series_info") {
        const seriesId = cleanString(url.searchParams.get("series_id"));
        payload = await xtreamSeriesInfoPayload(env, seriesId);
        logExtra = { id: seriesId };
    } else if (action === "get_short_epg" || action === "get_simple_data_table") {
        payload = xtreamEmptyEpgPayload();
    } else {
        console.warn(`[xtream] unsupported action=${action}; returning empty list`);
        payload = [];
    }

    logXtreamAction(request, action, payload, logExtra);
    return json(payload);
}

// Helper: builds the Xtream payload for a given action (extracted from handleXtreamApi)
async function buildXtreamPayload(action, env, categoryId, request, user) {
    if (action === "get_all_categories") return xtreamAllCategoriesPayload(request, env, user);
    if (action === "get_live_categories") return xtreamLiveCategories(env);
    if (action === "get_live_streams") return xtreamLiveStreams(env, categoryId, request, user);
    if (action === "get_vod_categories") return xtreamVodCategories(env);
    if (action === "get_vod_streams") return xtreamVodStreams(env, categoryId);
    if (action === "get_series_categories") return xtreamSeriesCategories(env);
    if (action === "get_series") return xtreamSeriesList(env, categoryId);
    if (action === "get_all_channels" || action === "get_all_streams" || action === "get_all_live_streams") {
        return xtreamLiveStreams(env, categoryId, request, user);
    }
    return [];
}

async function handleSystemApi(request, env) {
    const url = new URL(request.url);
    const username = cleanString(url.searchParams.get("username"));
    const password = cleanString(url.searchParams.get("password"));
    const action = cleanString(url.searchParams.get("action"));
    const user = await resolveXtreamUser(env, username, password);
    if (!user) return json({ user_info: { username, password, auth: 0, status: "Disabled" } });
    return json(await xtreamSystemApiPayload(request, env, user, action));
}

async function handlePortalApi(request, env) {
    const url = new URL(request.url);
    const username = cleanString(url.searchParams.get("username"));
    const password = cleanString(url.searchParams.get("password"));
    const action = cleanString(url.searchParams.get("action"));
    const user = await resolveXtreamUser(env, username, password);
    if (!user) return json({ user_info: { username, password, auth: 0, status: "Disabled" } });
    if (action) return json(await xtreamSystemApiPayload(request, env, user, action));
    return xtreamPortalHtml(request, env, user);
}

async function handleEnigma2Api(request, env) {
    const url = new URL(request.url);
    const username = cleanString(url.searchParams.get("username"));
    const password = cleanString(url.searchParams.get("password"));
    const action = cleanString(url.searchParams.get("action"));
    const user = await resolveXtreamUser(env, username, password);
    if (!user) return withCors(new Response("<?xml version=\"1.0\" encoding=\"UTF-8\"?><enigma2><auth>0</auth></enigma2>", {
        headers: { "content-type": "application/xml; charset=utf-8", "cache-control": "no-store" },
    }));
    return enigma2XmlPayload(request, env, user, action);
}

// ─── Custom Categories API handlers ─────────────────────────────────────────────

async function customCategoriesPayload(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const categories = await loadCustomCategories(env);
    return json({ status: "ok", count: categories.length, categories });
}

async function saveCustomCategoriesHandler(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const incoming = Array.isArray(data.categories) ? data.categories : [];

    let maxId = 0;
    const existing = await loadCustomCategories(env);
    for (const c of existing) {
        const n = parseInt(c.id, 10);
        if (!isNaN(n) && n > maxId) maxId = n;
    }

    const categoriesToSave = [];
    let order = 1;
    for (const c of incoming) {
        const name = cleanString(c.name);
        if (!name) continue;
        let id = cleanString(c.id);
        if (!id || isNaN(parseInt(id, 10))) {
            maxId++;
            id = String(maxId);
        }
        categoriesToSave.push({
            id: String(parseInt(id, 10)),
            name,
            order: order++,
            channelKeys: Array.isArray(c.channelKeys) ? c.channelKeys.map(String).filter(Boolean) : []
        });
    }

    await saveCustomCategories(env, categoriesToSave);
    return json({ status: "ok", count: categoriesToSave.length, categories: categoriesToSave });
}

// ─── Custom Playlist API handlers ─────────────────────────────────────────────

async function customPlaylistsPayload(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const playlists = await loadCustomPlaylists(env);
    const base = publicBase(request, env);
    return json({
        status: "ok",
        count: playlists.length,
        playlists: playlists.map((p) => ({
            ...p,
            api_url: `${base}/api/playlist/${p.id}`,
            m3u_url: `${base}/api/playlist/${p.id}.m3u`,
        })),
    });
}

async function createCustomPlaylist(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const name = cleanString(data.name);
    if (!name) throw new HttpError(400, "Playlist name is required.");
    const channelKeys = Array.isArray(data.channelKeys) ? data.channelKeys.map(String).filter(Boolean) : [];
    if (channelKeys.length === 0) throw new HttpError(400, "At least one channel must be selected.");
    const playlists = await loadCustomPlaylists(env);
    const id = randomPlaylistId(8);
    const now = new Date().toISOString();
    const playlist = { id, name, createdAt: now, updatedAt: now, channelKeys };
    playlists.push(playlist);
    await saveCustomPlaylists(env, playlists);
    const base = publicBase(request, env);
    return json({ status: "ok", playlist: { ...playlist, api_url: `${base}/api/playlist/${id}`, m3u_url: `${base}/api/playlist/${id}.m3u` } }, 201);
}

async function updateCustomPlaylist(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const id = cleanString(data.id);
    if (!id) throw new HttpError(400, "Playlist ID is required.");
    const playlists = await loadCustomPlaylists(env);
    const index = playlists.findIndex((p) => p.id === id);
    if (index < 0) throw new HttpError(404, "Playlist not found.");
    if (data.name !== undefined) playlists[index].name = cleanString(data.name) || playlists[index].name;
    if (Array.isArray(data.channelKeys)) playlists[index].channelKeys = data.channelKeys.map(String).filter(Boolean);
    playlists[index].updatedAt = new Date().toISOString();
    await saveCustomPlaylists(env, playlists);
    const base = publicBase(request, env);
    return json({ status: "ok", playlist: { ...playlists[index], api_url: `${base}/api/playlist/${id}`, m3u_url: `${base}/api/playlist/${id}.m3u` } });
}

async function deleteCustomPlaylist(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const id = cleanString(data.id);
    if (!id) throw new HttpError(400, "Playlist ID is required.");
    const playlists = await loadCustomPlaylists(env);
    const kept = playlists.filter((p) => p.id !== id);
    await saveCustomPlaylists(env, kept);
    return json({ status: "ok", deleted: playlists.length - kept.length });
}

async function exportCustomPlaylists(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const playlists = await loadCustomPlaylists(env);
    return withCors(new Response(JSON.stringify({ exportedAt: new Date().toISOString(), playlists }, null, 2), {
        headers: {
            "content-type": "application/json; charset=utf-8",
            "content-disposition": 'attachment; filename="custom-playlists-export.json"',
            "cache-control": "no-store",
        },
    }));
}

async function importCustomPlaylists(request, env) {
    if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
    const data = await readRequestData(request);
    const incoming = Array.isArray(data.playlists) ? data.playlists : [];
    if (incoming.length === 0) throw new HttpError(400, "No playlists found in import data.");
    const existing = await loadCustomPlaylists(env);
    const byId = new Map(existing.map((p) => [p.id, p]));
    let added = 0, updated = 0;
    for (const p of incoming) {
        const id = cleanString(p.id);
        if (!id) continue;
        const name = cleanString(p.name, "Imported Playlist");
        const channelKeys = Array.isArray(p.channelKeys) ? p.channelKeys.map(String).filter(Boolean) : [];
        const now = new Date().toISOString();
        if (byId.has(id)) {
            const ex = byId.get(id);
            ex.name = name;
            ex.channelKeys = channelKeys;
            ex.updatedAt = now;
            updated++;
        } else {
            byId.set(id, { id, name, createdAt: p.createdAt || now, updatedAt: now, channelKeys });
            added++;
        }
    }
    const merged = [...byId.values()];
    await saveCustomPlaylists(env, merged);
    return json({ status: "ok", added, updated, total: merged.length });
}

async function serveCustomPlaylistJson(request, env, playlistId) {
    const playlists = await loadCustomPlaylists(env);
    const playlist = playlists.find((p) => p.id === playlistId);
    if (!playlist) throw new HttpError(404, "Playlist not found.");
    const channels = await loadChannels(env, false);
    const wantedKeys = new Set(playlist.channelKeys);
    const matched = channels.filter((ch) => wantedKeys.has(ch.key));
    const records = [];
    for (const ch of matched) records.push(await channelRecord(ch, request, env));
    return json({ status: "ok", playlist_id: playlist.id, playlist_name: playlist.name, count: records.length, channels: records });
}

async function serveCustomPlaylistM3u(request, env, playlistId) {
    const playlists = await loadCustomPlaylists(env);
    const playlist = playlists.find((p) => p.id === playlistId);
    if (!playlist) throw new HttpError(404, "Playlist not found.");
    const channels = await loadPlaylistChannels(env, false);
    const wantedKeys = new Set(playlist.channelKeys);
    const matched = channels.filter((ch) => wantedKeys.has(ch.key));
    const lines = ["#EXTM3U"];
    for (const channel of matched) {
        appendM3uEntry(lines, {
            id: channel.key,
            name: channel.name,
            logo: channel.logo,
            category: channel.category || "Live",
            url: generatedLiveUrl(channel, { username: "user", password: "password" }, request, env),
        });
    }
    return playlistResponse(`${lines.join("\n")}\n`);
}

// ─── Main request handler ─────────────────────────────────────────────────────

async function handleRequest(request, env, waitUntil) {
    if (request.method === "OPTIONS") return withCors(new Response(null, { status: 204 }));

    const url = new URL(request.url);
    const path = url.pathname;
    const isDashboardMutation = request.method === "POST" && (
        path === "/api/access-users" || path === "/api/access-users/delete" ||
        path === "/api/custom-playlists" || path === "/api/custom-playlists/update" ||
        path === "/api/custom-playlists/delete" || path === "/api/custom-playlists/import" ||
        path === "/api/custom-categories/save" ||
        path === "/api/servers" || path === "/api/servers/update" ||
        path === "/api/servers/delete" || path === "/api/servers/test"
    );

    if (request.method !== "GET" && request.method !== "HEAD" && !isDashboardMutation) {
        return json({ error: "Method not allowed." }, 405);
    }

    if (path === "/__version") {
        return json({
            build: APP_BUILD_ID,
            xtream_compatibility: "get_all_categories returns a categories envelope",
            updated_at: "2026-06-17T00:00:00+02:00",
            features: ["low-latency-3seg", "segment-retry", "circuit-breaker", "cdn-cache-control", "server-management", "bunny-cdn-pullzone"],
        });
    }

    // ─── Health API ────────────────────────────────────────────────────────────
    if (path === "/api/health") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        const memUsage = process.memoryUsage();
        const healthData = {
            status: "ok",
            uptime_seconds: Math.round((Date.now() - serverStartedAt) / 1000),
            memory: {
                rss_mb: Math.round(memUsage.rss / 1048576),
                heap_used_mb: Math.round(memUsage.heapUsed / 1048576),
                heap_total_mb: Math.round(memUsage.heapTotal / 1048576),
            },
            caches: {
                channels: { count: channelCache.channels.length, age_seconds: channelCache.at ? Math.round((Date.now() - channelCache.at) / 1000) : null },
                playlist_channels: { count: playlistChannelCache.channels.length, age_seconds: playlistChannelCache.at ? Math.round((Date.now() - playlistChannelCache.at) / 1000) : null },
                stream_index: streamIndex.size,
                upstream_hls: upstreamHlsCache.size,
                live_playlists: livePlaylistCache.size,
                segments: segmentCache.size,
                xtream_catalogs: xtreamCatalogCache.size,
                xtream_responses: xtreamResponseCache.size,
            },
            requests: {
                total: globalRequestCount,
                segment_cache_hits: globalSegmentCacheHits,
                segment_cache_misses: globalSegmentCacheMisses,
            },
            circuit_breakers: [...circuitBreaker.entries()].map(([origin, state]) => ({
                origin,
                failures: state.failures,
                open: Date.now() < state.openUntil,
                cooldown_remaining_ms: Math.max(0, state.openUntil - Date.now()),
            })),
            upstream_health: [...upstreamHealthStats.entries()].map(([origin, stats]) => ({
                origin,
                ...stats,
                lastSuccess: stats.lastSuccess ? new Date(stats.lastSuccess).toISOString() : null,
                lastFailure: stats.lastFailure ? new Date(stats.lastFailure).toISOString() : null,
            })),
            bunny_cdn: {
                enabled: bunnyEnabled,
                initialized: bunnyInitialized,
                pull_zones_count: bunnyPullZoneCache.size,
                pull_zones: [...bunnyPullZoneCache.entries()].map(([origin, info]) => ({
                    origin,
                    hostname: info.hostname,
                    pull_zone_id: info.pullZoneId,
                    age_hours: Math.round((Date.now() - info.createdAt) / 3600_000 * 10) / 10,
                })),
            },
        };
        return json(healthData);
    }

    // ─── Server Management API ────────────────────────────────────────────────
    if (path === "/api/servers" && request.method === "GET") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        const servers = await loadCustomServers(env);
        const envSources = buildProviderPlaylistSources(env);
        return json({
            status: "ok",
            custom_servers: servers,
            env_sources: envSources.map(s => ({ label: s.label, url_masked: sanitizeUrlForLog(s.url) })),
        });
    }
    if (path === "/api/servers" && request.method === "POST") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        const data = await readRequestData(request);
        const name = cleanString(data.name);
        const serverUrl = cleanString(data.url);
        const username = cleanString(data.username);
        const password = cleanString(data.password);
        if (!name) throw new HttpError(400, "Server name is required.");
        if (!serverUrl) throw new HttpError(400, "Server URL is required.");
        if (!username || !password) throw new HttpError(400, "Username and password are required.");
        const servers = await loadCustomServers(env);
        const id = randomPlaylistId(10);
        const server = {
            id, name, url: serverUrl.replace(/\/+$/, ""), username, password,
            enabled: true, priority: servers.length + 1,
            createdAt: new Date().toISOString(),
        };
        servers.push(server);
        await saveCustomServers(env, servers);
        customServersCache = servers;
        // Trigger background channel refresh with new server
        void doRefreshChannels(env).catch(() => null);
        void doRefreshPlaylistChannels(env).catch(() => null);
        return json({ status: "ok", server: { ...server, password: "***" } }, 201);
    }
    if (path === "/api/servers/update" && request.method === "POST") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        const data = await readRequestData(request);
        const id = cleanString(data.id);
        if (!id) throw new HttpError(400, "Server ID is required.");
        const servers = await loadCustomServers(env);
        const idx = servers.findIndex(s => s.id === id);
        if (idx < 0) throw new HttpError(404, "Server not found.");
        if (data.name !== undefined) servers[idx].name = cleanString(data.name) || servers[idx].name;
        if (data.url !== undefined) servers[idx].url = cleanString(data.url).replace(/\/+$/, "") || servers[idx].url;
        if (data.username !== undefined) servers[idx].username = cleanString(data.username) || servers[idx].username;
        if (data.password !== undefined) servers[idx].password = cleanString(data.password) || servers[idx].password;
        if (data.enabled !== undefined) servers[idx].enabled = parseRequestBool(data.enabled, true);
        if (data.priority !== undefined) servers[idx].priority = Number(data.priority) || servers[idx].priority;
        await saveCustomServers(env, servers);
        customServersCache = servers;
        void doRefreshChannels(env).catch(() => null);
        return json({ status: "ok", server: { ...servers[idx], password: "***" } });
    }
    if (path === "/api/servers/delete" && request.method === "POST") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        const data = await readRequestData(request);
        const id = cleanString(data.id);
        if (!id) throw new HttpError(400, "Server ID is required.");
        const servers = await loadCustomServers(env);
        const kept = servers.filter(s => s.id !== id);
        await saveCustomServers(env, kept);
        customServersCache = kept;
        void doRefreshChannels(env).catch(() => null);
        return json({ status: "ok", deleted: servers.length - kept.length });
    }
    if (path === "/api/servers/test" && request.method === "POST") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        const data = await readRequestData(request);
        const testUrl = cleanString(data.url);
        const testUser = cleanString(data.username);
        const testPass = cleanString(data.password);
        if (!testUrl || !testUser || !testPass) throw new HttpError(400, "URL, username, and password required.");
        const config = { baseUrl: testUrl.replace(/\/+$/, ""), username: testUser, password: testPass };
        const startMs = Date.now();
        try {
            const result = await fetchXtreamApi(env, config, null);
            const latency = Date.now() - startMs;
            if (result && result.user_info && result.user_info.auth === 1) {
                return json({ status: "ok", connected: true, latency_ms: latency, user_info: result.user_info, server_info: result.server_info });
            }
            return json({ status: "ok", connected: false, latency_ms: latency, error: "Authentication failed" });
        } catch (err) {
            return json({ status: "ok", connected: false, latency_ms: Date.now() - startMs, error: err?.message || "Connection failed" });
        }
    }

    // ─── Loading video proxy (serves MP4 with CORS) ─────────────────────────
    if (path === "/loading.mp4") {
        return proxyLoadingVideo(env, request);
    }

    if (path === "/") {
        if (!dashboardAuthorized(request, env)) return dashboardAuthResponse();
        return htmlResponse(dashboardPage());
    }

    if (path === "/api/access-users" && request.method === "GET") {
        return accessUsersPayload(request, env);
    }

    if (path === "/api/access-users" && request.method === "POST") {
        return createAccessUser(request, env);
    }

    if (path === "/api/access-users/delete" && request.method === "POST") {
        return deleteAccessUser(request, env);
    }

    // ─── Custom Categories API ─────────────────────────────────────────────────
    if (path === "/api/custom-categories" && request.method === "GET") return customCategoriesPayload(request, env);
    if (path === "/api/custom-categories/save" && request.method === "POST") return saveCustomCategoriesHandler(request, env);

    // ─── Custom Playlist API ───────────────────────────────────────────────────
    if (path === "/api/custom-playlists" && request.method === "GET") return customPlaylistsPayload(request, env);
    if (path === "/api/custom-playlists" && request.method === "POST") return createCustomPlaylist(request, env);
    if (path === "/api/custom-playlists/update" && request.method === "POST") return updateCustomPlaylist(request, env);
    if (path === "/api/custom-playlists/delete" && request.method === "POST") return deleteCustomPlaylist(request, env);
    if (path === "/api/custom-playlists/export") return exportCustomPlaylists(request, env);
    if (path === "/api/custom-playlists/import" && request.method === "POST") return importCustomPlaylists(request, env);

    const playlistM3uMatch = path.match(/^\/api\/playlist\/([A-Za-z0-9]{4,16})\.m3u$/);
    if (playlistM3uMatch) return serveCustomPlaylistM3u(request, env, playlistM3uMatch[1]);
    const playlistJsonMatch = path.match(/^\/api\/playlist\/([A-Za-z0-9]{4,16})$/);
    if (playlistJsonMatch) return serveCustomPlaylistJson(request, env, playlistJsonMatch[1]);

    if (path === "/get.php") {
        if (process.env.DEBUG_API === "true") {
            console.log(`[xtream-debug] get.php request: ${request.url}`);
        }
        return generatedM3uResponse(request, env, waitUntil);
    }

    // ─── Xtream Codes API (/player_api.php) ─────────────────────────────────────
    if (path === "/player_api.php" || path === "/player_api") {
        return handleXtreamApi(request, env, waitUntil);
    }

    if (path === "/api.php") {
        return handleXtreamApi(request, env, waitUntil);
    }

    if (path === "/system_api.php" || path === "/system_api") {
        return handleSystemApi(request, env);
    }

    if (path === "/portal.php") {
        return handlePortalApi(request, env);
    }

    if (path === "/enigma2.php") {
        return handleEnigma2Api(request, env);
    }

    if (path === "/panel_api.php" || path === "/panel_api") {
        const url = new URL(request.url);
        const username = cleanString(url.searchParams.get("username"));
        const password = cleanString(url.searchParams.get("password"));
        const user = await resolveXtreamUser(env, username, password);
        if (!user) return json({ user_info: { username, password, auth: 0, status: "Disabled" } });
        return panelApiPayload(request, env, user);
    }

    // Xtream EPG stub — apps need this endpoint to exist even if EPG is empty
    if (path === "/xmltv.php") {
        return withCors(new Response('<?xml version="1.0" encoding="UTF-8"?><tv></tv>', {
            headers: { "content-type": "application/xml; charset=utf-8", "cache-control": "no-store" },
        }));
    }

    // ─── Xtream short URL proxy: /{user}/{pass}/{stream_id} OR /{user}/{pass}/{stream_id}.{ext}
    const xtreamShortMatch = path.match(/^\/([^/]+)\/([^/]+)\/([0-9]+)(?:\.(?:m3u8|ts|mp4|mpeg))?$/);
    if (xtreamShortMatch) {
        await requireXtreamAuth(xtreamShortMatch[1], xtreamShortMatch[2]);
        const streamId = xtreamShortMatch[3];
        let key = xtreamLocalNumericIndex.get(streamId) || streamId;
        let sourceUrl = await findXtreamLiveUrl(env, key);
        if (!sourceUrl && streamIndex.has(key)) sourceUrl = streamIndex.get(key);
        if (!sourceUrl) throw new HttpError(404, "Live stream not found.");
        if (key === streamId) key = await streamKey(sourceUrl);

        if (!path.toLowerCase().endsWith(".m3u8")) {
            try {
                const headers = new Headers();
                headers.set("user-agent", envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT);
                if (request.headers.get("range")) headers.set("range", request.headers.get("range"));
                if (request.headers.get("if-range")) headers.set("if-range", request.headers.get("if-range"));

                const upstreamRes = await fetch(sourceUrl, { method: request.method, headers, redirect: "follow" });

                const proxyHeaders = new Headers(upstreamRes.headers);
                proxyHeaders.set("access-control-allow-origin", "*");
                if (proxyHeaders.has("transfer-encoding")) proxyHeaders.delete("content-length");

                return new Response(upstreamRes.body, { status: upstreamRes.status, headers: proxyHeaders });
            } catch (err) {
                console.error(`[stream] Failed to proxy native stream ${sourceUrl}: ${err.message}`);
                throw new HttpError(502, "Upstream stream fetch failed.");
            }
        }
        return proxyLiveFromSource(key, sourceUrl, request, env, waitUntil, `live:${key}`);
    }

    // ─ Xtream live stream proxy: /live/{user}/{pass}/{stream_id}.{ext} ─
    const xtreamLiveMatch = path.match(/^\/live\/([^/]+)\/([^/]+)\/([A-Za-z0-9_-]+)(?:\.(?:m3u8|ts|mp4|mpeg))?$/);
    if (xtreamLiveMatch) {
        await requireXtreamAuth(xtreamLiveMatch[1], xtreamLiveMatch[2]);
        const streamId = xtreamLiveMatch[3];
        let key = xtreamLocalNumericIndex.get(streamId) || streamId;
        let sourceUrl = await findXtreamLiveUrl(env, key);
        if (!sourceUrl && streamIndex.has(key)) sourceUrl = streamIndex.get(key);
        if (!sourceUrl) throw new HttpError(404, "Live stream not found.");
        if (key === streamId) key = await streamKey(sourceUrl);

        if (!path.toLowerCase().endsWith(".m3u8")) {
            try {
                const headers = new Headers();
                headers.set("user-agent", envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT);
                if (request.headers.get("range")) headers.set("range", request.headers.get("range"));
                if (request.headers.get("if-range")) headers.set("if-range", request.headers.get("if-range"));

                const upstreamRes = await fetch(sourceUrl, { method: request.method, headers, redirect: "follow" });

                const proxyHeaders = new Headers(upstreamRes.headers);
                proxyHeaders.set("access-control-allow-origin", "*");
                if (proxyHeaders.has("transfer-encoding")) proxyHeaders.delete("content-length");

                return new Response(upstreamRes.body, { status: upstreamRes.status, headers: proxyHeaders });
            } catch (err) {
                console.error(`[stream] Failed to proxy native stream ${sourceUrl}: ${err.message}`);
                throw new HttpError(502, "Upstream stream fetch failed.");
            }
        }
        return proxyLiveFromSource(key, sourceUrl, request, env, waitUntil, `live:${key}`);
    }

    // ─── Xtream movie: /movie/{user}/{pass}/{stream_id}.{ext} ────────────────────
    const xtreamMovieMatch = path.match(/^\/movie\/([^/]+)\/([^/]+)\/([0-9]+)(?:\.([^/]+))?$/);
    if (xtreamMovieMatch) {
        await requireXtreamAuth(xtreamMovieMatch[1], xtreamMovieMatch[2]);
        const movieUrl = await findXtreamMovieUrl(env, xtreamMovieMatch[3]);
        if (!movieUrl) throw new HttpError(404, "Movie not found.");
        return proxyProgressiveStream(movieUrl, request, env);
    }

    // ─── Xtream series episode: /series/{user}/{pass}/{episode_id}.{ext} ─────────
    const xtreamSeriesMatch = path.match(/^\/series\/([^/]+)\/([^/]+)\/([0-9]+)(?:\.([^/]+))?$/);
    if (xtreamSeriesMatch) {
        await requireXtreamAuth(xtreamSeriesMatch[1], xtreamSeriesMatch[2]);
        const episodeUrl = await findXtreamEpisodeUrl(xtreamSeriesMatch[3]);
        if (!episodeUrl) throw new HttpError(404, "Episode not found — open the series in your app first to load episode data.");
        return proxyProgressiveStream(episodeUrl, request, env);
    }

    if (path === "/api/all-channels") {
        const channelMap = new Map();
        const channels = await loadPlaylistChannels(env, false).catch(() => []);
        for (const ch of channels) channelMap.set(ch.key, { key: ch.key, name: ch.name, category: ch.category, logo: ch.logo });

        const sources = buildProviderPlaylistSources(env);
        for (const source of sources) {
            const catalog = await loadXtreamCatalog(env, source, "live", false).catch(() => null);
            if (catalog) {
                const catMap = new Map();
                for (const [catId, catName] of catalog.categoriesById.entries()) catMap.set(catId, catName);
                for (const item of catalog.items) {
                    const id = itemId(item, "live");
                    if (id) {
                        const catName = catMap.get(cleanString(item.category_id)) || cleanString(item.category_id);
                        channelMap.set(id, { key: id, name: cleanString(item.name, "Unknown"), category: catName, logo: mediaLogo(item) });
                    }
                }
            }
        }
        return json({ status: "ok", channels: Array.from(channelMap.values()) });
    }

    if (path === "/api/channels" || path === "/api/channels.json" || path === "/channels") {
        const force = (url.searchParams.get("refresh") || "").toLowerCase();
        const refresh = force === "1" || force === "true" || force === "yes";
        return json(await channelsPayload(request, env, refresh));
    }

    if (path === "/api/movies" || path === "/api/movies.json" || path === "/movies") {
        const force = (url.searchParams.get("refresh") || "").toLowerCase();
        const refresh = force === "1" || force === "true" || force === "yes";
        return json(await moviesPayload(request, env, refresh));
    }

    if (path === "/api/tvseries" || path === "/api/tvseries.json" || path === "/tvseries") {
        const force = (url.searchParams.get("refresh") || "").toLowerCase();
        const refresh = force === "1" || force === "true" || force === "yes";
        return json(await tvSeriesPayload(request, env, refresh));
    }

    // ─── Named stream URL: /stream/{ChannelSlug}.m3u8 ────────────────────────
    const streamSlugMatch = path.match(/^\/stream\/([^/]+)\.m3u8$/);
    if (streamSlugMatch) {
        const slug = decodeURIComponent(streamSlugMatch[1]);
        const streamSlugKey = slugIndex.get(slug);
        if (!streamSlugKey) throw new HttpError(404, `Stream "${slug}" not found.`);
        return proxyChannelPlaylist(streamSlugKey, request, env, waitUntil);
    }

    const directPlaylistMatch = path.match(/^\/(?:direct|source|playlist)\/([^/]+)\.m3u8$/);
    if (directPlaylistMatch) return proxyDirectPlaylist(directPlaylistMatch[1], request, env, waitUntil);

    const liveMatch = path.match(/^\/(?:live|play)\/([a-f0-9]{20})\/index\.m3u8$/);
    if (liveMatch) return proxyChannelPlaylist(liveMatch[1], request, env, waitUntil);

    const nestedPlaylistMatch = path.match(/^\/(?:uplive|upstream-playlist)\/([a-f0-9]{20})\/([^/]+)\.m3u8$/);
    if (nestedPlaylistMatch) return proxyNestedPlaylist(nestedPlaylistMatch[1], nestedPlaylistMatch[2], request, env, waitUntil);

    const segmentMatch = path.match(/^\/(?:upseg|upstream-segment)\/([a-f0-9]{20})\/([^/]+)\/([^/]+)$/);
    if (segmentMatch) return proxySegment(segmentMatch[1], segmentMatch[2], segmentMatch[3], request, env);

    return json({ error: "Not found." }, 404);
}

// Express server

const app = express();
let requestLogSeq = 0;

app.use((req, res, next) => {
    const id = (++requestLogSeq).toString(36).padStart(4, "0");
    const startedAt = Date.now();
    const url = sanitizeUrlForLog(req.originalUrl);
    const client = requestClientForLog(req);
    const userAgent = String(req.headers["user-agent"] || "").slice(0, 140);
    const uaText = userAgent ? ` ua="${userAgent}"` : "";
    console.log(`[request:${id}] -> ${req.method} ${url} from=${client}${uaText}`);

    let logged = false;
    const logDone = (event) => {
        if (logged) return;
        logged = true;
        const elapsedMs = Date.now() - startedAt;
        const closed = event === "close" && !res.writableEnded ? " closed" : "";
        console.log(`[request:${id}] <- ${res.statusCode || 0} ${req.method} ${url} ${elapsedMs}ms${closed}`);
    };

    res.on("finish", () => logDone("finish"));
    res.on("close", () => logDone("close"));
    next();
});

app.use(express.raw({ type: "*/*", limit: "50mb" }));

async function pipeWebResponse(webResponse, res) {
    res.status(webResponse.status);
    webResponse.headers.forEach((value, key) => res.set(key, value));
    res.set("x-app-build", APP_BUILD_ID);

    // Force Express to send headers immediately so the player doesn't sit pending
    res.flushHeaders();

    if (webResponse.body) {
        // Convert the Web Stream to a Node Stream for hardware-optimized piping
        const nodeStream = Readable.fromWeb(webResponse.body);

        let finished = false;
        const cleanup = () => {
            if (!finished) {
                finished = true;
                if (!nodeStream.destroyed) nodeStream.destroy();
            }
        };

        res.on("close", cleanup);
        res.on("finish", cleanup);
        res.on("error", cleanup);

        nodeStream.on("error", (error) => {
            const isAborted = error?.name === "AbortError" ||
                error?.code === "UND_ERR_SOCKET" ||
                error?.message?.includes("ECONNRESET");
            if (!isAborted) {
                console.error("[stream] Upstream read error:", error.message);
            }
            cleanup();
            res.end();
        });

        // Pipe directly to the client. This implements native backpressure,
        // instantly reducing memory bloat and latency.
        nodeStream.pipe(res);
    } else {
        res.end();
    }
}

app.use(async (req, res) => {
    try {
        const proto = (req.headers["x-forwarded-proto"] || "http").split(",")[0].trim();
        const host = req.headers["x-forwarded-host"] || req.headers.host;
        const fullUrl = `${proto}://${host}${req.originalUrl}`;

        const headers = {};
        for (const [k, v] of Object.entries(req.headers)) {
            if (typeof v === "string") headers[k] = v;
        }
        const requestInit = { method: req.method, headers };
        if (req.method !== "GET" && req.method !== "HEAD") {
            requestInit.body = Buffer.isBuffer(req.body) ? req.body : undefined;
            requestInit.duplex = "half";
        }
        const webRequest = new Request(fullUrl, requestInit);

        const waitUntil = (promise) => promise.catch((err) => console.error("Background task error:", err));

        const webResponse = await handleRequest(webRequest, process.env, waitUntil);

        if (webResponse.status >= 300 && webResponse.status < 400) {
            return res.redirect(webResponse.status, webResponse.headers.get("location") || "/");
        }

        await pipeWebResponse(webResponse, res);
    } catch (error) {
        const status = error instanceof HttpError ? error.status : 500;
        const message = error instanceof HttpError ? error.message : "Unexpected error.";
        const isAborted = error?.name === "AbortError" ||
            error?.message?.includes("terminated") ||
            error?.code === "UND_ERR_SOCKET" ||
            error?.message?.includes("other side closed") ||
            error?.message?.includes("ECONNRESET");
        if (isAborted) {
            if (res.headersSent) {
                console.log(`[server] Connection closed by client during streaming: ${req.method} ${req.originalUrl}`);
            } else {
                console.log(`[server] Client disconnected before stream started: ${req.method} ${req.originalUrl}`);
            }
        } else {
            console.error(`Request failed: ${req.method} ${req.originalUrl}`, error);
        }
        if (!res.headersSent) {
            res.status(status).json({ error: message });
        }
    }
});

// Safety nets — keep the process alive even if something unexpected slips through
process.on("unhandledRejection", (reason) => {
    console.error("[unhandledRejection]", reason);
});
process.on("uncaughtException", (err) => {
    console.error("[uncaughtException]", err);
});

const PORT = process.env.PORT || 7860;

// Pre-warm caches from disk on startup so the very first /api/channels request
// is instant. Then kick off a live refresh in the background.
async function prewarmCaches() {
    const env = process.env;

    // 0. Load custom servers cache from disk
    try {
        customServersCache = await loadCustomServers(env);
        console.log(`[cache] custom servers restored from disk: ${customServersCache.length} servers`);
    } catch (err) {
        console.warn("[cache] failed to restore custom servers from disk:", err?.message);
    }

    // 1. Load channel cache from disk
    const diskChannels = await loadDiskCache(CHANNEL_DISK_CACHE_FILE);
    if (diskChannels && Array.isArray(diskChannels.channels) && diskChannels.channels.length > 0) {
        channelCache.at = diskChannels.at || 0;
        channelCache.channels = diskChannels.channels;
        if (Array.isArray(diskChannels.streamIndex)) {
            for (const [k, v] of diskChannels.streamIndex) streamIndex.set(k, v);
        }
        console.log(`[cache] channels restored from disk: ${channelCache.channels.length} channels (age ${Math.round((Date.now() - channelCache.at) / 1000)}s)`);
        buildSlugIndex(channelCache.channels);
    }

    // 2. Load playlist channel cache from disk
    const diskPlaylist = await loadDiskCache(PLAYLIST_DISK_CACHE_FILE);
    if (diskPlaylist && Array.isArray(diskPlaylist.channels) && diskPlaylist.channels.length > 0) {
        playlistChannelCache.at = diskPlaylist.at || 0;
        playlistChannelCache.channels = diskPlaylist.channels;
        if (Array.isArray(diskPlaylist.streamIndex)) {
            for (const [k, v] of diskPlaylist.streamIndex) streamIndex.set(k, v);
        }
        console.log(`[cache] playlist channels restored from disk: ${playlistChannelCache.channels.length} channels`);
    }

    // 3. Initialize Bunny CDN pull zones (load from disk + pre-create for known origins)
    try {
        await initBunnyPullZones(env);
    } catch (err) {
        console.warn("[bunny-cdn] initialization failed (falling back to proxy):", err?.message);
        bunnyEnabled = false;
    }

    // 4. Kick off live refresh in background (don't block startup)
    void doRefreshChannels(env).catch((err) => console.warn("[cache] background channel refresh failed:", err?.message));
    void doRefreshPlaylistChannels(env).catch((err) => console.warn("[cache] background playlist refresh failed:", err?.message));
}

app.listen(PORT, "0.0.0.0", () => {
    console.log(`running on port ${PORT}`);
    console.log(`Public base: ${process.env.WORKER_PUBLIC_BASE || "(auto from request)"}`);
    console.log(`Build: ${APP_BUILD_ID}`);
    console.log("Xtream compatibility: get_all_categories -> categories envelope");
    void prewarmCaches();
});
