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
const APP_BUILD_ID = "dqvod-live-stream-url-fields-2026-06-14";

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

// ─── Stream Warmup / Loading Video ──────────────────────────────────────────
// Tracks per-stream warmup state: once 2+ upstream segments are confirmed in
// the HLS playlist, the loading video stops and the real stream is served.
const streamWarmupState = new Map();  // cacheKey → { startedAt, ready, segmentsSeen, warmupPromise }
const MAX_WARMUP_ENTRIES = 500;
const WARMUP_EXPIRY_MS = 120_000;     // forget warmup state after 2 minutes
const LOADING_VIDEO_URL = "https://pub-170b5f1508954220a1c673d1ae1baaae.r2.dev/TaxiDevLoad.mp4";
const WARMUP_REQUIRED_SEGMENTS = 2;   // how many segments must appear before switching to live

// Disk-persist cache paths (loaded on startup so first request is always instant)
const CHANNEL_DISK_CACHE_FILE = process.env.CHANNEL_DISK_CACHE_FILE || "channel-cache.json";
const PLAYLIST_DISK_CACHE_FILE = process.env.PLAYLIST_DISK_CACHE_FILE || "playlist-channel-cache.json";
const CUSTOM_PLAYLISTS_FILE = process.env.CUSTOM_PLAYLISTS_FILE || "custom-playlists.json";

const MAX_UPSTREAM_HLS_CACHE_ENTRIES = 500;
const MAX_LIVE_PLAYLIST_CACHE_ENTRIES = 500;
const MAX_XTREAM_CATALOG_CACHE_ENTRIES = 100;
const MAX_GENERATED_PLAYLIST_CACHE_ENTRIES = 200;

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
            sources.push({ url: playlistUrl.toString(), label: "APIPRIMARY" });
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

async function loadCustomCategories(env) {
    try {
        const text = await fs.readFile(customCategoriesFile(env), "utf8");
        const data = JSON.parse(text);
        return Array.isArray(data?.categories) ? data.categories : [];
    } catch (error) {
        if (error && error.code === "ENOENT") return [];
        throw error;
    }
}

async function saveCustomCategories(env, categories) {
    const payload = { updatedAt: new Date().toISOString(), categories };
    await fs.writeFile(customCategoriesFile(env), `${JSON.stringify(payload, null, 2)}\n`, "utf8");
}

function randomPlaylistId(length = 8) {
    const alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789";
    const bytes = new Uint8Array(length);
    crypto.getRandomValues(bytes);
    let output = "";
    for (const byte of bytes) output += alphabet[byte % alphabet.length];
    return output;
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

// Dashboard and generated M3U playlists

function dashboardPage() {
    return `<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>IPTV Access Dashboard</title>
  <style>
    :root {
      color-scheme: dark;
      --bg: #0f1115;
      --panel: #181b22;
      --panel-2: #20242d;
      --text: #f5f7fb;
      --muted: #a6adbb;
      --line: #313746;
      --accent: #4fc3a1;
      --danger: #ff6b6b;
      --input: #11141a;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      min-height: 100vh;
      font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      background: var(--bg);
      color: var(--text);
    }
    .shell {
      width: min(1180px, calc(100% - 32px));
      margin: 0 auto;
      padding: 28px 0 40px;
    }
    header {
      display: flex;
      justify-content: space-between;
      gap: 18px;
      align-items: flex-end;
      margin-bottom: 22px;
    }
    h1 {
      margin: 0;
      font-size: clamp(28px, 4vw, 44px);
      line-height: 1;
      letter-spacing: 0;
    }
    .subtle { color: var(--muted); }
    .grid {
      display: grid;
      grid-template-columns: minmax(320px, 420px) 1fr;
      gap: 18px;
      align-items: start;
    }
    .panel {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 8px;
      overflow: hidden;
    }
    .panel h2 {
      margin: 0;
      padding: 16px 18px;
      font-size: 16px;
      background: var(--panel-2);
      border-bottom: 1px solid var(--line);
      letter-spacing: 0;
    }
    form, .panel-body { padding: 18px; }
    label {
      display: grid;
      gap: 7px;
      font-size: 13px;
      color: var(--muted);
      margin-bottom: 14px;
    }
    input, select {
      width: 100%;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--input);
      color: var(--text);
      padding: 11px 12px;
      font: inherit;
      outline: none;
    }
    input:focus, select:focus { border-color: var(--accent); }
    .checks {
      display: grid;
      gap: 10px;
      margin: 6px 0 18px;
    }
    .check {
      display: flex;
      align-items: center;
      gap: 10px;
      color: var(--text);
      margin: 0;
    }
    .check input { width: 18px; height: 18px; }
    button, .button {
      border: 0;
      border-radius: 6px;
      background: var(--accent);
      color: #04110d;
      padding: 11px 14px;
      font: inherit;
      font-weight: 700;
      cursor: pointer;
      text-decoration: none;
      display: inline-flex;
      justify-content: center;
      align-items: center;
      min-height: 42px;
    }
    button.secondary {
      background: #2b313d;
      color: var(--text);
      border: 1px solid var(--line);
    }
    button.danger {
      background: transparent;
      color: var(--danger);
      border: 1px solid color-mix(in srgb, var(--danger), transparent 55%);
    }
    .actions {
      display: grid;
      grid-template-columns: 1fr 1fr;
      gap: 10px;
    }
    .message {
      min-height: 22px;
      margin-top: 14px;
      font-size: 13px;
      color: var(--muted);
      overflow-wrap: anywhere;
    }
    table {
      width: 100%;
      border-collapse: collapse;
    }
    th, td {
      padding: 13px 14px;
      border-bottom: 1px solid var(--line);
      text-align: left;
      vertical-align: top;
      font-size: 14px;
    }
    th {
      color: var(--muted);
      font-size: 12px;
      text-transform: uppercase;
      letter-spacing: .08em;
      background: var(--panel-2);
    }
    tr:last-child td { border-bottom: 0; }
    code {
      display: block;
      max-width: 520px;
      color: #d8fff4;
      white-space: nowrap;
      overflow: hidden;
      text-overflow: ellipsis;
    }
    .row-actions {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
    }
    .pill {
      display: inline-flex;
      align-items: center;
      min-height: 24px;
      border: 1px solid var(--line);
      border-radius: 999px;
      padding: 2px 8px;
      color: var(--muted);
      font-size: 12px;
      margin: 0 5px 5px 0;
    }
    .empty {
      padding: 28px 18px;
      color: var(--muted);
    }
    /* Custom Playlists */
    .section-divider {
      border: 0;
      border-top: 1px solid var(--line);
      margin: 32px 0 24px;
    }
    .section-title {
      font-size: 22px;
      margin: 0 0 18px;
      font-weight: 700;
    }
    .search-box {
      position: relative;
      margin-bottom: 14px;
    }
    .search-box input {
      padding-left: 36px;
    }
    .search-icon {
      position: absolute;
      left: 12px;
      top: 50%;
      transform: translateY(-50%);
      font-size: 14px;
      opacity: .5;
      pointer-events: none;
    }
    .channel-list {
      max-height: 400px;
      overflow-y: auto;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--input);
    }
    .channel-item {
      display: flex;
      align-items: center;
      gap: 10px;
      padding: 9px 12px;
      border-bottom: 1px solid var(--line);
      font-size: 13px;
      cursor: pointer;
      transition: background .15s;
    }
    .channel-item:hover {
      background: var(--panel-2);
    }
    .channel-item:last-child { border-bottom: 0; }
    .channel-item input[type="checkbox"] { width: 16px; height: 16px; flex-shrink: 0; }
    .channel-item .ch-name { flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
    .channel-item .ch-cat { color: var(--muted); font-size: 11px; flex-shrink: 0; }
    .selected-count {
      font-size: 13px;
      color: var(--muted);
      margin: 10px 0;
    }
    .playlist-card {
      padding: 16px 18px;
      border-bottom: 1px solid var(--line);
    }
    .playlist-card:last-child { border-bottom: 0; }
    .playlist-card h3 {
      margin: 0 0 6px;
      font-size: 15px;
      font-weight: 600;
    }
    .playlist-card .meta {
      font-size: 12px;
      color: var(--muted);
      margin-bottom: 10px;
    }
    .playlist-card code {
      font-size: 12px;
      margin-bottom: 4px;
    }
    .playlist-actions {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
      margin-top: 8px;
    }
    .playlist-actions button {
      min-height: 32px;
      padding: 6px 12px;
      font-size: 12px;
    }
    .import-area {
      margin-top: 14px;
    }
    .import-area textarea {
      width: 100%;
      min-height: 80px;
      border: 1px solid var(--line);
      border-radius: 6px;
      background: var(--input);
      color: var(--text);
      padding: 10px;
      font: inherit;
      font-size: 12px;
      resize: vertical;
      outline: none;
    }
    .import-area textarea:focus { border-color: var(--accent); }
    
    /* IPTV Categories */
    .draggable { cursor: grab; }
    .draggable:active { cursor: grabbing; }
    .drag-over { border: 2px dashed var(--accent); }
    .cat-list, .cat-ch-list { max-height: 350px; overflow-y: auto; border: 1px solid var(--line); border-radius: 6px; background: var(--input); margin-bottom: 14px; }
    .cat-item, .cat-ch-item { display: flex; align-items: center; gap: 10px; padding: 9px 12px; border-bottom: 1px solid var(--line); font-size: 13px; background: var(--input); }
    .cat-item:last-child, .cat-ch-item:last-child { border-bottom: 0; }
    .cat-item.active { background: var(--panel-2); border-left: 3px solid var(--accent); }
    .cat-item { cursor: pointer; }
    .cat-actions { margin-left: auto; display: flex; gap: 8px; }
    .drag-handle { color: var(--muted); cursor: grab; padding: 0 5px; user-select: none; }

    @media (max-width: 860px) {
      header, .grid { display: block; }
      header > * + *, .grid > * + * { margin-top: 18px; }
      table, thead, tbody, tr, th, td { display: block; }
      thead { display: none; }
      td { border-bottom: 0; padding: 8px 14px; }
      tr { border-bottom: 1px solid var(--line); padding: 8px 0; }
      code { max-width: 100%; }
    }
  </style>
</head>
<body>
  <main class="shell">
    <header>
      <div>
        <h1>IPTV Access</h1>
        <div class="subtle">Create expiring M3U Plus links for TV apps. Base links stay live-only for faster loading.</div>
      </div>
      <a class="button" href="/api/channels">Channels JSON</a>
    </header>

    <section class="grid">
      <div class="panel">
        <h2>Create access</h2>
        <form id="create-form">
          <label>Username
            <input name="username" autocomplete="off" required>
          </label>
          <label>Password
            <input name="password" autocomplete="off" required>
          </label>
          <label>Expiry
            <select name="duration">
              <option value="1m">1 month</option>
              <option value="3m">3 months</option>
              <option value="12m">12 months</option>
              <option value="infinite">Infinite</option>
            </select>
          </label>
          <div class="checks">
            <label class="check"><input type="checkbox" name="include_live" checked> Live channels</label>
            <label class="check"><input type="checkbox" name="include_movies"> Movies direct URLs (optional, slower)</label>
            <label class="check"><input type="checkbox" name="include_series"> TV series direct episode URLs (optional, slower)</label>
          </div>
          <div class="actions">
            <button type="submit">Create link</button>
            <button class="secondary" type="button" id="random-password">Password</button>
          </div>
          <div class="message" id="message"></div>
        </form>
      </div>

      <div class="panel">
        <h2>Active links</h2>
        <div id="users"></div>
      </div>
    </section>

    <hr class="section-divider">
    <h2 class="section-title">Custom Playlists</h2>
    <section class="grid">
      <div class="panel">
        <h2>Create playlist</h2>
        <div class="panel-body">
          <label>Playlist name
            <input id="pl-name" autocomplete="off" placeholder="e.g. My Sports Channels">
          </label>
          <div class="search-box">
            <span class="search-icon">&#128269;</span>
            <input id="ch-search" placeholder="Search channels..." autocomplete="off">
          </div>
          <div class="selected-count" id="sel-count">0 channels selected</div>
          <div class="channel-list" id="ch-list"></div>
          <div style="margin-top:14px;display:flex;gap:10px">
            <button type="button" id="create-pl-btn">Create playlist</button>
            <button class="secondary" type="button" id="clear-sel-btn">Clear</button>
          </div>
          <div class="message" id="pl-message"></div>
        </div>
      </div>
      <div class="panel">
        <h2>Your playlists</h2>
        <div id="pl-list"></div>
        <div class="panel-body" style="border-top:1px solid var(--line)">
          <div style="display:flex;gap:10px;flex-wrap:wrap">
            <button class="secondary" type="button" id="export-pl-btn">Export all</button>
            <button class="secondary" type="button" id="show-import-btn">Import</button>
          </div>
          <div class="import-area" id="import-area" style="display:none">
            <textarea id="import-json" placeholder="Paste exported JSON here..."></textarea>
            <button type="button" id="do-import-btn" style="margin-top:8px">Import playlists</button>
          </div>
          <div class="message" id="pl-import-message"></div>
        </div>
      </div>
    </section>

    <hr class="section-divider">
    <h2 class="section-title">IPTV Categories Manager</h2>
    <p class="subtle" style="margin-bottom:18px">Create custom categories and arrange them to completely override the default IPTV provider layout.</p>
    <section class="grid">
      <div class="panel">
        <h2>Categories (Drag to reorder)</h2>
        <div class="panel-body">
          <div style="display:flex;gap:10px;margin-bottom:14px">
            <input id="new-cat-name" placeholder="New Category Name" autocomplete="off" style="flex:1">
            <button type="button" id="add-cat-btn">Add</button>
          </div>
          <div class="cat-list" id="cat-list"></div>
          <button class="secondary" type="button" id="auto-cat-btn" style="width:100%;margin-bottom:8px">Auto-Import from Channels</button>
          <div style="display:flex;gap:10px;margin-bottom:8px">
            <button class="secondary" type="button" id="export-cat-btn" style="flex:1">Export</button>
            <button class="secondary" type="button" id="show-import-cat-btn" style="flex:1">Import</button>
          </div>
          <div class="import-area" id="import-cat-area" style="display:none;margin-bottom:8px">
            <textarea id="import-cat-json" placeholder="Paste exported JSON here..."></textarea>
            <button type="button" id="do-import-cat-btn" style="margin-top:8px;width:100%">Import Categories JSON</button>
          </div>
          <button type="button" id="save-categories-btn" style="width:100%">Save Categories & Order</button>
          <div class="message" id="cat-message"></div>
        </div>
      </div>
      
      <div class="panel">
        <h2>Category Channels <span id="active-cat-name" style="font-weight:normal;color:var(--muted)"></span></h2>
        <div class="panel-body" id="cat-channels-panel" style="display:none">
          <div class="search-box">
            <span class="search-icon">&#128269;</span>
            <input id="cat-ch-search" placeholder="Search to add channels..." autocomplete="off">
          </div>
          <div class="channel-list" id="cat-ch-search-list" style="display:none; position:absolute; z-index:10; max-height:250px; overflow-y:auto; background:var(--panel-2); width:calc(100% - 36px); box-shadow:0 4px 12px rgba(0,0,0,0.5)"></div>
          
          <div style="margin-top:14px; margin-bottom:8px; font-size:13px; color:var(--muted)">Assigned Channels (Drag to reorder): <span id="cat-ch-count">0</span></div>
          <div class="cat-ch-list" id="active-cat-ch-list"></div>
        </div>
        <div class="panel-body" id="cat-channels-empty">
          <div class="empty">Select a category to manage its channels.</div>
        </div>
      </div>
    </section>

  </main>

  <script>
    const form = document.querySelector("#create-form");
    const message = document.querySelector("#message");
    const usersEl = document.querySelector("#users");
    const passwordInput = form.elements.password;

    function setMessage(text, isError = false) {
      message.textContent = text;
      message.style.color = isError ? "var(--danger)" : "var(--muted)";
    }

    function randomPassword(length = 14) {
      const alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789";
      const bytes = new Uint8Array(length);
      crypto.getRandomValues(bytes);
      return Array.from(bytes, (byte) => alphabet[byte % alphabet.length]).join("");
    }

    function expiryText(value) {
      if (!value) return "Infinite";
      const date = new Date(value);
      return Number.isNaN(date.getTime()) ? value : date.toLocaleDateString();
    }

    function contentPills(user) {
      const values = [];
      if (user.include_live) values.push("Live");
      if (user.include_movies) values.push("Movies");
      if (user.include_series) values.push("Series");
      return values.map((value) => "<span class=\\"pill\\">" + value + "</span>").join("");
    }

    async function copyText(text) {
      await navigator.clipboard.writeText(text);
      setMessage("Copied M3U link.");
    }

    async function deleteUser(username) {
      const response = await fetch("/api/access-users/delete", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ username })
      });
      if (!response.ok) throw new Error("Delete failed");
      await loadUsers();
      setMessage("Deleted " + username + ".");
    }

    function renderUsers(users) {
      if (!users.length) {
        usersEl.innerHTML = '<div class="empty">No generated links yet.</div>';
        return;
      }
      usersEl.innerHTML = '<table><thead><tr><th>User</th><th>Expiry</th><th>Content</th><th>M3U Link</th><th></th></tr></thead><tbody></tbody></table>';
      const tbody = usersEl.querySelector("tbody");
      for (const user of users) {
        const tr = document.createElement("tr");
        const status = user.expired ? "Expired" : (user.disabled ? "Disabled" : "Active");
        tr.innerHTML =
          "<td><strong></strong><div class=\\"subtle\\"></div></td>" +
          "<td></td>" +
          "<td></td>" +
          "<td><code></code></td>" +
          "<td><div class=\\"row-actions\\"><button class=\\"secondary\\" type=\\"button\\">Copy</button><button class=\\"danger\\" type=\\"button\\">Delete</button></div></td>";
        tr.querySelector("strong").textContent = user.username;
        tr.querySelector(".subtle").textContent = status;
        tr.children[1].textContent = expiryText(user.expires_at);
        tr.children[2].innerHTML = contentPills(user);
        tr.querySelector("code").textContent = user.m3u_url;
        const buttons = tr.querySelectorAll("button");
        buttons[0].addEventListener("click", () => copyText(user.m3u_url).catch((error) => setMessage(error.message, true)));
        buttons[1].addEventListener("click", () => deleteUser(user.username).catch((error) => setMessage(error.message, true)));
        tbody.appendChild(tr);
      }
    }

    async function loadUsers() {
      const response = await fetch("/api/access-users");
      if (!response.ok) throw new Error("Could not load access users");
      const payload = await response.json();
      renderUsers(payload.users || []);
    }

    document.querySelector("#random-password").addEventListener("click", () => {
      passwordInput.value = randomPassword();
      passwordInput.focus();
    });

    form.addEventListener("submit", async (event) => {
      event.preventDefault();
      setMessage("Creating link...");
      const data = Object.fromEntries(new FormData(form).entries());
      data.include_live = form.elements.include_live.checked;
      data.include_movies = form.elements.include_movies.checked;
      data.include_series = form.elements.include_series.checked;
      const response = await fetch("/api/access-users", {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(data)
      });
      const payload = await response.json();
      if (!response.ok) throw new Error(payload.error || "Create failed");
      setMessage(payload.user.m3u_url);
      await loadUsers();
    });

    passwordInput.value = randomPassword();
    loadUsers().catch((error) => setMessage(error.message, true));

    // ─── Custom Playlists ─────────────────────────────────────────────────
    const plNameInput = document.querySelector("#pl-name");
    const chSearchInput = document.querySelector("#ch-search");
    const chList = document.querySelector("#ch-list");
    const selCountEl = document.querySelector("#sel-count");
    const plMessage = document.querySelector("#pl-message");
    const plListEl = document.querySelector("#pl-list");
    const plImportMsg = document.querySelector("#pl-import-message");

    let allChannels = [];
    const selectedKeys = new Set();
    let lastCheckedIndex = null;

    function setPlMessage(text, isError) {
      plMessage.textContent = text;
      plMessage.style.color = isError ? "var(--danger)" : "var(--muted)";
    }

    function updateSelectedCount() {
      selCountEl.textContent = selectedKeys.size + " channel" + (selectedKeys.size !== 1 ? "s" : "") + " selected";
    }

    function renderChannelList(filter) {
      const q = (filter || "").toLowerCase().trim();
      const filtered = q
        ? allChannels.filter(function(ch) { return (ch.name + " " + ch.category).toLowerCase().indexOf(q) >= 0; })
        : allChannels;
      const max = 200;
      const shown = filtered.slice(0, max);
      chList.innerHTML = "";
      if (shown.length === 0) {
        chList.innerHTML = '<div style="padding:14px;color:var(--muted);font-size:13px">No channels found.</div>';
        return;
      }
      for (let i = 0; i < shown.length; i++) {
        var ch = shown[i];
        var div = document.createElement("div");
        div.className = "channel-item";
        var cb = document.createElement("input");
        cb.type = "checkbox";
        cb.checked = selectedKeys.has(ch.key);
        cb.setAttribute("data-key", ch.key);
        cb.addEventListener("click", function(e) {
          if (e.shiftKey && lastCheckedIndex !== null) {
            let start = Math.min(i, lastCheckedIndex);
            let end = Math.max(i, lastCheckedIndex);
            for (let j = start; j <= end; j++) {
              const rowCb = chList.children[j].querySelector("input[type='checkbox']");
              if (rowCb) {
                rowCb.checked = cb.checked;
                const k = rowCb.getAttribute("data-key");
                if (cb.checked) selectedKeys.add(k);
                else selectedKeys.delete(k);
              }
            }
          } else {
            var k = e.target.getAttribute("data-key");
            if (e.target.checked) selectedKeys.add(k);
            else selectedKeys.delete(k);
          }
          lastCheckedIndex = i;
          updateSelectedCount();
        });
        var nameSpan = document.createElement("span");
        nameSpan.className = "ch-name";
        nameSpan.textContent = ch.name;
        var catSpan = document.createElement("span");
        catSpan.className = "ch-cat";
        catSpan.textContent = ch.category || "";
        div.appendChild(cb);
        div.appendChild(nameSpan);
        div.appendChild(catSpan);
        (function(checkbox) {
          div.addEventListener("click", function(e) {
            if (e.target === checkbox) return;
            checkbox.checked = !checkbox.checked;
            checkbox.dispatchEvent(new Event("change"));
          });
        })(cb);
        chList.appendChild(div);
      }
      if (filtered.length > max) {
        var more = document.createElement("div");
        more.style.cssText = "padding:10px;text-align:center;color:var(--muted);font-size:12px";
        more.textContent = "+" + (filtered.length - max) + " more — refine your search";
        chList.appendChild(more);
      }
    }

    async function loadAllChannels() {
      try {
        var res = await fetch("/api/all-channels");
        if (!res.ok) throw new Error("Failed to load channels");
        var data = await res.json();
        allChannels = data.channels || [];
        renderChannelList();
      } catch (err) {
        chList.innerHTML = '<div style="padding:14px;color:var(--danger);font-size:13px">' + err.message + '</div>';
      }
    }

    chSearchInput.addEventListener("input", function() { renderChannelList(chSearchInput.value); });

    document.querySelector("#clear-sel-btn").addEventListener("click", function() {
      selectedKeys.clear();
      updateSelectedCount();
      renderChannelList(chSearchInput.value);
    });

    document.querySelector("#create-pl-btn").addEventListener("click", async function() {
      var name = plNameInput.value.trim();
      if (!name) { setPlMessage("Enter a playlist name.", true); return; }
      if (selectedKeys.size === 0) { setPlMessage("Select at least one channel.", true); return; }
      setPlMessage("Creating...");
      try {
        var res = await fetch("/api/custom-playlists", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ name: name, channelKeys: Array.from(selectedKeys) }),
        });
        var data = await res.json();
        if (!res.ok) throw new Error(data.error || "Create failed");
        setPlMessage("Playlist created! API: " + data.playlist.api_url);
        plNameInput.value = "";
        selectedKeys.clear();
        updateSelectedCount();
        renderChannelList(chSearchInput.value);
        await loadPlaylists();
      } catch (err) {
        setPlMessage(err.message, true);
      }
    });

    function renderPlaylists(playlists) {
      if (!playlists.length) {
        plListEl.innerHTML = '<div class="empty">No custom playlists yet.</div>';
        return;
      }
      plListEl.innerHTML = "";
      for (var i = 0; i < playlists.length; i++) {
        var pl = playlists[i];
        var card = document.createElement("div");
        card.className = "playlist-card";
        var h3 = document.createElement("h3");
        h3.textContent = pl.name;
        var meta = document.createElement("div");
        meta.className = "meta";
        meta.textContent = pl.channelKeys.length + " channels · ID: " + pl.id;
        var apiCode = document.createElement("code");
        apiCode.textContent = pl.api_url;
        var m3uCode = document.createElement("code");
        m3uCode.textContent = pl.m3u_url;
        m3uCode.style.marginTop = "4px";
        var actions = document.createElement("div");
        actions.className = "playlist-actions";
        var copyApiBtn = document.createElement("button");
        copyApiBtn.className = "secondary";
        copyApiBtn.textContent = "Copy API";
        var copyM3uBtn = document.createElement("button");
        copyM3uBtn.className = "secondary";
        copyM3uBtn.textContent = "Copy M3U";
        var delBtn = document.createElement("button");
        delBtn.className = "danger";
        delBtn.textContent = "Delete";
        actions.appendChild(copyApiBtn);
        actions.appendChild(copyM3uBtn);
        actions.appendChild(delBtn);
        card.appendChild(h3);
        card.appendChild(meta);
        card.appendChild(apiCode);
        card.appendChild(m3uCode);
        card.appendChild(actions);
        (function(p) {
          copyApiBtn.addEventListener("click", function() {
            navigator.clipboard.writeText(p.api_url).then(function() { setPlMessage("Copied API link."); });
          });
          copyM3uBtn.addEventListener("click", function() {
            navigator.clipboard.writeText(p.m3u_url).then(function() { setPlMessage("Copied M3U link."); });
          });
          delBtn.addEventListener("click", async function() {
            try {
              var res = await fetch("/api/custom-playlists/delete", {
                method: "POST",
                headers: { "content-type": "application/json" },
                body: JSON.stringify({ id: p.id }),
              });
              if (!res.ok) throw new Error("Delete failed");
              await loadPlaylists();
              setPlMessage("Playlist deleted.");
            } catch (err) { setPlMessage(err.message, true); }
          });
        })(pl);
        plListEl.appendChild(card);
      }
    }

    async function loadPlaylists() {
      try {
        var res = await fetch("/api/custom-playlists");
        if (!res.ok) throw new Error("Could not load playlists");
        var data = await res.json();
        renderPlaylists(data.playlists || []);
      } catch (err) {
        plListEl.innerHTML = '<div class="empty" style="color:var(--danger)">' + err.message + '</div>';
      }
    }

    document.querySelector("#export-pl-btn").addEventListener("click", async function() {
      try {
        var res = await fetch("/api/custom-playlists/export");
        if (!res.ok) throw new Error("Export failed");
        var blob = await res.blob();
        var a = document.createElement("a");
        a.href = URL.createObjectURL(blob);
        a.download = "custom-playlists-export.json";
        a.click();
        URL.revokeObjectURL(a.href);
      } catch (err) { setPlMessage(err.message, true); }
    });

    document.querySelector("#show-import-btn").addEventListener("click", function() {
      var area = document.querySelector("#import-area");
      area.style.display = area.style.display === "none" ? "block" : "none";
    });

    document.querySelector("#do-import-btn").addEventListener("click", async function() {
      var raw = document.querySelector("#import-json").value.trim();
      if (!raw) { plImportMsg.textContent = "Paste JSON first."; plImportMsg.style.color = "var(--danger)"; return; }
      try {
        var parsed = JSON.parse(raw);
        var res = await fetch("/api/custom-playlists/import", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify(parsed),
        });
        var result = await res.json();
        if (!res.ok) throw new Error(result.error || "Import failed");
        plImportMsg.textContent = "Imported! Added: " + result.added + ", Updated: " + result.updated;
        plImportMsg.style.color = "var(--muted)";
        document.querySelector("#import-json").value = "";
        await loadPlaylists();
      } catch (err) {
        plImportMsg.textContent = err.message;
        plImportMsg.style.color = "var(--danger)";
      }
    });

    // ─── IPTV Categories ─────────────────────────────────────────────────
    let customCategories = [];
    let activeCategoryId = null;

    const catListEl = document.getElementById("cat-list");
    const activeCatChListEl = document.getElementById("active-cat-ch-list");
    const catChSearchListEl = document.getElementById("cat-ch-search-list");
    const catChSearchInput = document.getElementById("cat-ch-search");

    function renderCategories() {
      catListEl.innerHTML = "";
      if (customCategories.length === 0) {
          catListEl.innerHTML = '<div class="empty">No custom categories defined.</div>';
      }
      customCategories.forEach((cat, index) => {
        const div = document.createElement("div");
        div.className = "cat-item draggable" + (activeCategoryId === cat.id ? " active" : "");
        div.draggable = true;
        div.dataset.index = index;
        div.innerHTML = '<span class="drag-handle">☰</span>' +
          '<span style="flex:1;overflow:hidden;text-overflow:ellipsis">' + cat.name + ' <small style="color:var(--muted)">(' + cat.channelKeys.length + ')</small></span>' +
          '<div class="cat-actions">' +
            '<button type="button" class="secondary to-top-btn" style="padding:2px 6px;min-height:0;font-size:11px">Top</button>' +
            '<button type="button" class="secondary rename-btn" style="padding:2px 6px;min-height:0;font-size:11px">Rename</button>' +
            '<button type="button" class="danger delete-btn" style="padding:2px 6px;min-height:0;font-size:11px">Delete</button>' +
          '</div>';
        
        div.addEventListener("click", (e) => {
          if (e.target.tagName === "BUTTON") return;
          activeCategoryId = cat.id;
          renderCategories();
          renderActiveCategory();
        });
        
        div.querySelector(".delete-btn").addEventListener("click", (e) => {
          e.stopPropagation();
          customCategories = customCategories.filter(c => c.id !== cat.id);
          if (activeCategoryId === cat.id) activeCategoryId = null;
          renderCategories();
          renderActiveCategory();
        });

        div.querySelector(".to-top-btn").addEventListener("click", (e) => {
          e.stopPropagation();
          const moved = customCategories.splice(index, 1)[0];
          customCategories.unshift(moved);
          renderCategories();
        });
        
        div.querySelector(".rename-btn").addEventListener("click", (e) => {
          e.stopPropagation();
          const newName = prompt("Rename category:", cat.name);
          if (newName && newName.trim()) {
            cat.name = newName.trim();
            renderCategories();
            renderActiveCategory();
          }
        });
        
        // Drag events for category
        div.addEventListener("dragstart", (e) => { e.dataTransfer.setData("text/plain", index); div.style.opacity = "0.5"; });
        div.addEventListener("dragend", () => { div.style.opacity = "1"; });
        div.addEventListener("dragover", (e) => { e.preventDefault(); div.classList.add("drag-over"); });
        div.addEventListener("dragleave", () => { div.classList.remove("drag-over"); });
        div.addEventListener("drop", (e) => {
          e.preventDefault();
          div.classList.remove("drag-over");
          const fromIndex = parseInt(e.dataTransfer.getData("text/plain"));
          const toIndex = index;
          if (fromIndex !== toIndex) {
            const moved = customCategories.splice(fromIndex, 1)[0];
            customCategories.splice(toIndex, 0, moved);
            renderCategories();
          }
        });
        
        catListEl.appendChild(div);
      });
    }

    function renderActiveCategory() {
      const cat = customCategories.find(c => c.id === activeCategoryId);
      if (!cat) {
        document.getElementById("cat-channels-panel").style.display = "none";
        document.getElementById("cat-channels-empty").style.display = "block";
        document.getElementById("active-cat-name").textContent = "";
        return;
      }
      
      document.getElementById("cat-channels-panel").style.display = "block";
      document.getElementById("cat-channels-empty").style.display = "none";
      document.getElementById("active-cat-name").textContent = " - " + cat.name;
      document.getElementById("cat-ch-count").textContent = cat.channelKeys.length;
      
      activeCatChListEl.innerHTML = "";
      if (cat.channelKeys.length === 0) {
          activeCatChListEl.innerHTML = '<div class="empty">No channels assigned.</div>';
      }
      cat.channelKeys.forEach((key, index) => {
        const ch = allChannels.find(c => c.key === key);
        if (!ch) return;
        const div = document.createElement("div");
        div.className = "cat-ch-item draggable";
        div.draggable = true;
        div.dataset.index = index;
        div.innerHTML = '<span class="drag-handle">☰</span>' +
          '<span style="flex:1;overflow:hidden;text-overflow:ellipsis">' + ch.name + '</span>' +
          '<button type="button" class="danger" style="padding:2px 6px;min-height:0;font-size:11px">Remove</button>';
        
        div.querySelector("button").addEventListener("click", () => {
          cat.channelKeys.splice(index, 1);
          renderCategories();
          renderActiveCategory();
        });
        
        div.addEventListener("dragstart", (e) => { e.dataTransfer.setData("text/plain", index); div.style.opacity = "0.5"; });
        div.addEventListener("dragend", () => { div.style.opacity = "1"; });
        div.addEventListener("dragover", (e) => { e.preventDefault(); div.classList.add("drag-over"); });
        div.addEventListener("dragleave", () => { div.classList.remove("drag-over"); });
        div.addEventListener("drop", (e) => {
          e.preventDefault();
          div.classList.remove("drag-over");
          const fromIndex = parseInt(e.dataTransfer.getData("text/plain"));
          const toIndex = index;
          if (fromIndex !== toIndex) {
            const moved = cat.channelKeys.splice(fromIndex, 1)[0];
            cat.channelKeys.splice(toIndex, 0, moved);
            renderActiveCategory();
          }
        });
        
        activeCatChListEl.appendChild(div);
      });
    }

    document.getElementById("add-cat-btn").addEventListener("click", () => {
      const name = document.getElementById("new-cat-name").value.trim();
      if (!name) return;
      const newId = String(Date.now()) + Math.floor(Math.random()*1000);
      customCategories.unshift({ id: newId, name, order: 0, channelKeys: [] });
      document.getElementById("new-cat-name").value = "";
      renderCategories();
    });

    document.getElementById("auto-cat-btn").addEventListener("click", () => {
      if (allChannels.length === 0) {
        document.getElementById("cat-message").textContent = "Wait for channels to load first.";
        return;
      }
      if (customCategories.length > 0 && !confirm("This will clear your current custom categories and rebuild them. Continue?")) return;
      
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
      renderCategories();
      renderActiveCategory();
      document.getElementById("cat-message").textContent = "Imported! Don't forget to Save.";
      document.getElementById("cat-message").style.color = "var(--muted)";
    });

    document.getElementById("export-cat-btn").addEventListener("click", () => {
      const data = JSON.stringify({ categories: customCategories }, null, 2);
      const blob = new Blob([data], { type: "application/json" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = "custom-categories-export.json";
      a.click();
      URL.revokeObjectURL(url);
    });

    document.getElementById("show-import-cat-btn").addEventListener("click", () => {
      const area = document.getElementById("import-cat-area");
      area.style.display = area.style.display === "none" ? "block" : "none";
    });

    document.getElementById("do-import-cat-btn").addEventListener("click", () => {
      const raw = document.getElementById("import-cat-json").value.trim();
      if (!raw) {
        document.getElementById("cat-message").textContent = "Paste JSON first.";
        document.getElementById("cat-message").style.color = "var(--danger)";
        return;
      }
      try {
        const parsed = JSON.parse(raw);
        if (!Array.isArray(parsed.categories)) throw new Error("Invalid format: expected 'categories' array");
        customCategories = parsed.categories;
        document.getElementById("import-cat-json").value = "";
        document.getElementById("import-cat-area").style.display = "none";
        renderCategories();
        renderActiveCategory();
        document.getElementById("cat-message").textContent = "Imported successfully! Please click Save to apply.";
        document.getElementById("cat-message").style.color = "var(--muted)";
      } catch (err) {
        document.getElementById("cat-message").textContent = "Error parsing JSON: " + err.message;
        document.getElementById("cat-message").style.color = "var(--danger)";
      }
    });

    document.getElementById("save-categories-btn").addEventListener("click", async () => {
      document.getElementById("cat-message").textContent = "Saving...";
      try {
        const res = await fetch("/api/custom-categories/save", {
          method: "POST",
          headers: { "content-type": "application/json" },
          body: JSON.stringify({ categories: customCategories })
        });
        if (!res.ok) throw new Error("Save failed");
        document.getElementById("cat-message").textContent = "Saved successfully!";
        document.getElementById("cat-message").style.color = "var(--muted)";
        setTimeout(() => document.getElementById("cat-message").textContent = "", 3000);
        await loadCategories();
      } catch(err) {
        document.getElementById("cat-message").textContent = err.message;
        document.getElementById("cat-message").style.color = "var(--danger)";
      }
    });

    catChSearchInput.addEventListener("input", () => {
      const q = catChSearchInput.value.toLowerCase().trim();
      if (!q) {
        catChSearchListEl.style.display = "none";
        return;
      }
      const filtered = allChannels.filter(ch => (ch.name + " " + ch.category).toLowerCase().indexOf(q) >= 0).slice(0, 50);
      catChSearchListEl.innerHTML = "";
      if (filtered.length === 0) {
        catChSearchListEl.innerHTML = '<div style="padding:10px;font-size:13px;color:var(--muted)">No channels found.</div>';
      } else {
        const addAllBtn = document.createElement("button");
        addAllBtn.type = "button";
        addAllBtn.className = "secondary";
        addAllBtn.style.cssText = "width:100%; padding:6px; margin-bottom:4px; font-weight:bold";
        addAllBtn.textContent = "Add All " + filtered.length + " Channels";
        addAllBtn.addEventListener("click", () => {
          const cat = customCategories.find(c => c.id === activeCategoryId);
          if (cat) {
            filtered.forEach(ch => {
              if (!cat.channelKeys.includes(ch.key)) cat.channelKeys.push(ch.key);
            });
            renderCategories();
            renderActiveCategory();
          }
          catChSearchInput.value = "";
          catChSearchListEl.style.display = "none";
        });
        catChSearchListEl.appendChild(addAllBtn);

        filtered.forEach(ch => {
          const div = document.createElement("div");
          div.className = "channel-item";
          div.style.cursor = "pointer";
          div.innerHTML = '<span style="flex:1">' + ch.name + '</span> <span class="ch-cat">' + (ch.category||"") + '</span> <button class="secondary" type="button" style="padding:2px 6px;min-height:0;font-size:11px">Add</button>';
          div.addEventListener("click", () => {
            const cat = customCategories.find(c => c.id === activeCategoryId);
            if (cat && !cat.channelKeys.includes(ch.key)) {
              cat.channelKeys.push(ch.key);
              renderCategories();
              renderActiveCategory();
            }
          });
          catChSearchListEl.appendChild(div);
        });
      }
      catChSearchListEl.style.display = "block";
    });

    document.addEventListener("click", (e) => {
      if (!catChSearchInput.contains(e.target) && !catChSearchListEl.contains(e.target)) {
        catChSearchListEl.style.display = "none";
      }
    });

    async function loadCategories() {
      try {
        const res = await fetch("/api/custom-categories");
        if (!res.ok) throw new Error("Could not load categories");
        const data = await res.json();
        customCategories = (data.categories || []).sort((a,b) => a.order - b.order);
        renderCategories();
        renderActiveCategory();
      } catch (err) {
        document.getElementById("cat-message").textContent = err.message;
        document.getElementById("cat-message").style.color = "var(--danger)";
      }
    }

    loadAllChannels();
    loadPlaylists();
    loadCategories();
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
    const configuredKeepSegments = envInt(env, "LIVE_WINDOW_SEGMENTS", 0);
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
    const path = new URL(absoluteUrl).pathname;
    const filenameParts = path.split("/").filter(Boolean);
    const filename = filenameParts[filenameParts.length - 1] || "segment.bin";
    const token = await makeUrlToken({ u: absoluteUrl, r: playlistUrl, f: httpsFallback || undefined }, env);
    // Use CDN base for segments so .ts files are served/cached through the CDN
    const base = streamBase(request, env);
    if (path.toLowerCase().endsWith(".m3u8")) return `${base}/uplive/${key}/${token}.m3u8`;
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
    const startOffsetSegments = Math.max(0, envInt(env, "LIVE_START_OFFSET_SEGMENTS", 0));
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
        if (line.startsWith("#EXT-X-ALLOW-CACHE")) { lines.push("#EXT-X-ALLOW-CACHE:NO"); continue; }
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
    try {
        const headers = {
            "user-agent": envString(env, "FETCH_USER_AGENT", DEFAULT_FETCH_USER_AGENT) || DEFAULT_FETCH_USER_AGENT,
            referer,
        };
        if (request && request.headers.get("range")) headers.range = request.headers.get("range");
        if (request && request.headers.get("if-range")) headers["if-range"] = request.headers.get("if-range");
        return await fetch(url, { method: request ? request.method : "GET", headers, redirect: "follow" });
    } catch {
        return null;
    }
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
        const prefetchCount = Math.max(0, envInt(env, "PREFETCH_SEGMENTS", 0));
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

async function proxyLiveFromSource(key, sourceUrl, request, env, waitUntil, cacheKey) {
    const warmupEnabled = envBool(env, "LOADING_VIDEO_ENABLED", true);
    const requiredSegments = envInt(env, "WARMUP_REQUIRED_SEGMENTS", WARMUP_REQUIRED_SEGMENTS);
    const now = Date.now();
    const freshMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_CACHE_MS", 2000));
    const staleMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_STALE_MS", 0));
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
        const prefetchCount = Math.max(0, envInt(env, "PREFETCH_SEGMENTS", 0));
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
    const staleMs = Math.max(0, envInt(env, "LIVE_PLAYLIST_STALE_MS", 0));
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
    const tokenData = await readUrlToken(token, env);
    const referer = tokenData.r || tokenData.u;
    const ttlSeconds = Math.max(1, envInt(env, "SEGMENT_CACHE_SECONDS", 30));

    const primary = await fetchUpstreamAsset(tokenData.u, referer, env, ttlSeconds, request);
    const fallback = (!primary || primary.status >= 400) && tokenData.f
        ? await fetchUpstreamAsset(tokenData.f, referer, env, ttlSeconds, request)
        : null;

    const upstream = fallback && fallback.ok ? fallback : primary;
    if (!upstream) throw new HttpError(502, "Upstream segment fetch failed.");
    if (!upstream.ok) return withCors(new Response(upstream.body, { status: upstream.status, headers: upstream.headers }));

    const headers = new Headers(upstream.headers);
    headers.set("cache-control", `public, max-age=${ttlSeconds}, s-maxage=${ttlSeconds}, stale-while-revalidate=15`);
    if (!headers.has("content-type")) headers.set("content-type", mediaTypeForPath(filename));

    // Explicitly declare partial content support here
    headers.set("accept-ranges", "bytes");

    headers.set("access-control-allow-origin", "*");
    headers.set("access-control-allow-methods", "GET,HEAD,OPTIONS");
    headers.set("access-control-allow-headers", "*");
    headers.set("access-control-expose-headers", "Content-Length, Content-Range, Accept-Ranges, Content-Type");
    headers.set("x-content-type-options", "nosniff");
    headers.set("x-proxied-by", "node-express");
    headers.set("x-worker-origin", publicBase(request, env));

    return new Response(upstream.body, { status: upstream.status, statusText: upstream.statusText, headers });
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

        const numericStreamId = String(parseInt(channel.key.slice(0, 8), 16) || 1);
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
            tv_archive: 0,
            direct_source: "",
            tv_archive_duration: 0,
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
                    const numericStreamId = String(parseInt(channel.key.slice(0, 8), 16) || 1);
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
                        tv_archive: 0,
                        direct_source: "",
                        tv_archive_duration: 0,
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
                        tv_archive: 0,
                        direct_source: "",
                        tv_archive_duration: 0,
                    });
                }
            }
        }

        if (wantedCategoryId === "999999" || (!wantedCategoryId || wantedCategoryId === "0")) {
            for (const channel of channelMap.values()) {
                if (!mappedKeys.has(channel.key)) {
                    if (!channel.is_xtream) {
                        const numericStreamId = String(parseInt(channel.key.slice(0, 8), 16) || 1);
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
                            tv_archive: 0,
                            direct_source: "",
                            tv_archive_duration: 0,
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
                            tv_archive: 0,
                            direct_source: "",
                            tv_archive_duration: 0,
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

    let payload;
    let logExtra = {};
    if (!action) {
        payload = xtreamUserInfoPayload(user, request, env);
    } else if (action === "get_all_categories") {
        payload = await xtreamAllCategoriesPayload(request, env, user);
        logExtra = { mode: "dqvod_categories_envelope" };
    } else if (action === "get_live_categories") {
        payload = await xtreamLiveCategories(env);
    } else if (action === "get_live_streams") {
        payload = await xtreamLiveStreams(env, categoryId, request, user);
        logExtra = { categoryId };
    } else if (action === "get_vod_categories") {
        payload = await xtreamVodCategories(env);
    } else if (action === "get_vod_streams") {
        payload = await xtreamVodStreams(env, categoryId);
        logExtra = { categoryId };
    } else if (action === "get_vod_info") {
        const vodId = cleanString(url.searchParams.get("vod_id") || url.searchParams.get("movie_id") || url.searchParams.get("stream_id"));
        payload = await xtreamVodInfoPayload(env, vodId);
        logExtra = { id: vodId };
    } else if (action === "get_series_categories") {
        payload = await xtreamSeriesCategories(env);
    } else if (action === "get_series") {
        payload = await xtreamSeriesList(env, categoryId);
        logExtra = { categoryId };
    } else if (action === "get_series_info") {
        const seriesId = cleanString(url.searchParams.get("series_id"));
        payload = await xtreamSeriesInfoPayload(env, seriesId);
        logExtra = { id: seriesId };
    } else if (action === "get_short_epg" || action === "get_simple_data_table") {
        payload = xtreamEmptyEpgPayload();
    } else if (action === "get_all_channels" || action === "get_all_streams" || action === "get_all_live_streams") {
        payload = await xtreamLiveStreams(env, categoryId, request, user);
        logExtra = { categoryId };
    } else {
        console.warn(`[xtream] unsupported action=${action}; returning empty list`);
        payload = [];
    }

    logXtreamAction(request, action, payload, logExtra);
    return json(payload);
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
        path === "/api/custom-categories/save"
    );

    if (request.method !== "GET" && request.method !== "HEAD" && !isDashboardMutation) {
        return json({ error: "Method not allowed." }, 405);
    }

    if (path === "/__version") {
        return json({
            build: APP_BUILD_ID,
            xtream_compatibility: "get_all_categories returns a categories envelope",
            updated_at: "2026-06-14T00:44:00+02:00",
        });
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
        // Proxy through our own /upseg/ endpoint — hides upstream credentials,
        // eliminates "unsafe URL" warnings in IPTV apps.
        const key = await streamKey(movieUrl);
        const token = await makeUrlToken({ u: movieUrl }, env);
        const filename = `${xtreamMovieMatch[3]}.${xtreamMovieMatch[4] || "mp4"}`;
        return withCors(new Response(null, {
            status: 302,
            headers: { location: `${publicBase(request, env)}/upseg/${key}/${token}/${filename}` },
        }));
    }

    // ─── Xtream series episode: /series/{user}/{pass}/{episode_id}.{ext} ─────────
    const xtreamSeriesMatch = path.match(/^\/series\/([^/]+)\/([^/]+)\/([0-9]+)(?:\.([^/]+))?$/);
    if (xtreamSeriesMatch) {
        await requireXtreamAuth(xtreamSeriesMatch[1], xtreamSeriesMatch[2]);
        const episodeUrl = await findXtreamEpisodeUrl(xtreamSeriesMatch[3]);
        if (!episodeUrl) throw new HttpError(404, "Episode not found — open the series in your app first to load episode data.");
        // Proxy through our own /upseg/ endpoint — hides upstream credentials.
        const key = await streamKey(episodeUrl);
        const token = await makeUrlToken({ u: episodeUrl }, env);
        const filename = `${xtreamSeriesMatch[3]}.${xtreamSeriesMatch[4] || "mp4"}`;
        return withCors(new Response(null, {
            status: 302,
            headers: { location: `${publicBase(request, env)}/upseg/${key}/${token}/${filename}` },
        }));
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

app.use(express.raw({ type: "*/*", limit: "64kb" }));

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

    // 3. Kick off live refresh in background (don't block startup)
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
