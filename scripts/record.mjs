// 雨雲ブレンド — hourly recorder (runs on GitHub Actions)
//
// Every hour:
//   1. finds the AMeDAS station nearest to HOME_LAT/HOME_LON (secrets; never written to the repo)
//   2. saves each model's hourly forecast (temperature, precipitation) for the next 24 h at the station
//   3. reads the station's observed temperature / 1-hour precipitation for the last 24 h
//   4. scores every saved forecast whose target hour now has an observation
//   5. writes data/stats.json (30-day summary the app reads) and data/state.json (working data)
//
// Privacy: everything written to the repo is encrypted with DATA_KEY (AES-256-GCM, key from PBKDF2-SHA256),
// and the log never prints place names, station ids, coordinates or URLs — on a public repository
// both the files and the Actions logs are visible to anyone.

import { readFile, writeFile, mkdir, rm } from "node:fs/promises";
import { webcrypto as crypto } from "node:crypto";

const DATA_DIR = new URL("../data/", import.meta.url);
const MODELS = {
  jma_seamless: "気象庁MSM",
  ecmwf_ifs025: "ECMWF",
  icon_seamless: "ICON",
  gfs_seamless: "GFS",
};
const LEAD_BINS = [["1-6", 1, 6], ["7-12", 7, 12], ["13-24", 13, 24]];
const TOD = [["night", 0, 6], ["morning", 6, 12], ["afternoon", 12, 18], ["evening", 18, 24]]; // JST hour buckets
const RAIN_MM = 0.5;          // AMeDAS gauges count in 0.5 mm steps
const KEEP_FORECAST_H = 30;   // keep snapshots long enough to score 24 h leads
const KEEP_DAYS = 60;         // daily aggregates kept
const STATS_DAYS = 30;        // summary window
const HOUR = 3600e3;

const now = process.env.RECORD_NOW ? Date.parse(process.env.RECORD_NOW) : Date.now();
const DATA_KEY = process.env.DATA_KEY || "";
const PBKDF2_ITER = 200000;
const lat = parseFloat(process.env.HOME_LAT), lon = parseFloat(process.env.HOME_LON);

const pad = n => String(n).padStart(2, "0");
const jst = ms => { const d = new Date(ms + 9 * HOUR); return { y: d.getUTCFullYear(), m: d.getUTCMonth() + 1, d: d.getUTCDate(), h: d.getUTCHours(), mi: d.getUTCMinutes() }; };
const amKey = ms => { const p = jst(ms); return `${p.y}${pad(p.m)}${pad(p.d)}${pad(p.h)}${pad(p.mi)}00`; };
const jstDate = ms => { const p = jst(ms); return `${p.y}-${pad(p.m)}-${pad(p.d)}`; };
const iso = ms => new Date(ms).toISOString().slice(0, 13) + ":00Z"; // hour key (UTC)
const amVal = v => Array.isArray(v) && v[0] != null && (v[1] === 0 || v[1] == null) ? v[0] : null;
const distKm = (a1, o1, a2, o2) => { const r = Math.PI / 180, x = (o2 - o1) * r * Math.cos((a1 + a2) / 2 * r), y = (a2 - a1) * r; return Math.hypot(x, y) * 6371; };
const round1 = v => Math.round(v * 10) / 10;

// errors never include the URL (it contains coordinates / station ids)
async function getJSON(url, tries = 3) {
  let last;
  for (let i = 0; i < tries; i++) {
    try {
      const r = await fetch(url, { headers: { "user-agent": "amagumo-blend-recorder" } });
      if (r.status === 404) return null;
      if (!r.ok) throw new Error(`HTTP ${r.status}`);
      return await r.json();
    } catch (e) { last = new Error(String(e.message || e).replace(/https?:\/\/\S+/g, "[url]")); await new Promise(res => setTimeout(res, 1500 * (i + 1))); }
  }
  throw last;
}
async function getText(url) {
  const r = await fetch(url, { headers: { "user-agent": "amagumo-blend-recorder" } });
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  return (await r.text()).trim();
}

// ---------- encryption (format shared with the app) ----------
const b64 = buf => Buffer.from(buf).toString("base64");
const unb64 = s => new Uint8Array(Buffer.from(s, "base64"));
async function deriveKey(salt) {
  const base = await crypto.subtle.importKey("raw", new TextEncoder().encode(DATA_KEY), "PBKDF2", false, ["deriveKey"]);
  return crypto.subtle.deriveKey({ name: "PBKDF2", salt, iterations: PBKDF2_ITER, hash: "SHA-256" }, base, { name: "AES-GCM", length: 256 }, false, ["encrypt", "decrypt"]);
}
async function encrypt(obj) {
  const salt = crypto.getRandomValues(new Uint8Array(16)), iv = crypto.getRandomValues(new Uint8Array(12));
  const ct = await crypto.subtle.encrypt({ name: "AES-GCM", iv }, await deriveKey(salt), new TextEncoder().encode(JSON.stringify(obj)));
  return { v: 1, alg: "AES-256-GCM", kdf: "PBKDF2-SHA256", iter: PBKDF2_ITER, salt: b64(salt), iv: b64(iv), data: b64(ct) };
}
async function decrypt(box) {
  const key = await deriveKey(unb64(box.salt));
  const pt = await crypto.subtle.decrypt({ name: "AES-GCM", iv: unb64(box.iv) }, key, unb64(box.data));
  return JSON.parse(new TextDecoder().decode(pt));
}
async function loadEncrypted(name, fallback) {
  let raw; try { raw = await readFile(new URL(name, DATA_DIR), "utf8"); } catch { return fallback; }
  try { return await decrypt(JSON.parse(raw)); }
  catch { console.warn("前回の記録を復号できませんでした(合言葉を変えた場合は正常です)。記録をやり直します"); return fallback; }
}
async function saveEncrypted(name, obj) {
  await mkdir(DATA_DIR, { recursive: true });
  await writeFile(new URL(name, DATA_DIR), JSON.stringify(await encrypt(obj)) + "\n");
}

// ---------- 1. station ----------
const AMEDAS = "https://www.jma.go.jp/bosai/amedas/";
async function pickStation(state) {
  const table = await getJSON(AMEDAS + "const/amedastable.json");
  const latest = Date.parse(await getText(AMEDAS + "data/latest_time.txt"));
  const map = await getJSON(AMEDAS + `data/map/${amKey(latest)}.json`);
  if (process.env.STATION_ID && table[process.env.STATION_ID]) {
    const st = table[process.env.STATION_ID];
    return { id: process.env.STATION_ID, name: st.kjName, lat: st.lat[0] + st.lat[1] / 60, lon: st.lon[0] + st.lon[1] / 60, latest };
  }
  // keep the previous station if it still reports (avoids switching back and forth)
  if (state.station && map?.[state.station.id] && amVal(map[state.station.id].temp) != null) return { ...state.station, latest };
  const cands = Object.entries(table).map(([id, st]) => {
    const la = st.lat[0] + st.lat[1] / 60, lo = st.lon[0] + st.lon[1] / 60;
    return { id, name: st.kjName, lat: +la.toFixed(4), lon: +lo.toFixed(4), d: distKm(lat, lon, la, lo) };
  }).filter(s => s.d <= 40 && map?.[s.id] && amVal(map[s.id].temp) != null && amVal(map[s.id].precipitation1h) != null)
    .sort((a, b) => a.d - b.d);
  if (!cands.length) throw new Error("40km以内に気温と雨量を測っているアメダスがありません");
  const { d, ...st } = cands[0];
  return { ...st, latest };
}

// ---------- 2. forecasts ----------
async function fetchForecasts(st) {
  const out = {};
  for (const key of Object.keys(MODELS)) {
    try {
      const j = await getJSON(`https://api.open-meteo.com/v1/forecast?latitude=${st.lat}&longitude=${st.lon}&models=${key}` +
        `&hourly=temperature_2m,precipitation&forecast_days=3&timezone=GMT`);
      const h = j?.hourly; if (!h?.time) continue;
      const T = h.temperature_2m || h[`temperature_2m_${key}`], P = h.precipitation || h[`precipitation_${key}`];
      const made = Math.floor(now / HOUR) * HOUR, rec = {};
      h.time.forEach((t, i) => {
        const ms = Date.parse(t + "Z"), lead = Math.round((ms - made) / HOUR);
        if (lead >= 1 && lead <= 24 && (T?.[i] != null || P?.[i] != null)) rec[iso(ms)] = [T?.[i] == null ? null : round1(T[i]), P?.[i] == null ? null : round1(P[i])];
      });
      if (Object.keys(rec).length) out[key] = rec;
    } catch (e) { console.warn(`forecast ${MODELS[key]}: ${e.message}`); }
  }
  return out;
}

// ---------- 3. observations (top of each hour, last 24 h) ----------
async function fetchObs(st) {
  const blocks = new Set();
  for (let t = st.latest - 24 * HOUR; t <= st.latest; t += 3 * HOUR) { const p = jst(t); blocks.add(`${p.y}${pad(p.m)}${pad(p.d)}_${pad(Math.floor(p.h / 3) * 3)}`); }
  { const p = jst(st.latest); blocks.add(`${p.y}${pad(p.m)}${pad(p.d)}_${pad(Math.floor(p.h / 3) * 3)}`); }
  const obs = {};
  for (const b of blocks) {
    let j; try { j = await getJSON(AMEDAS + `data/point/${st.id}/${b}.json`); } catch (e) { console.warn(`observation block: ${e.message}`); continue; }
    if (!j) continue;
    for (const [k, rec] of Object.entries(j)) {
      if (k.slice(10, 14) !== "0000") continue; // top of the hour only
      const ms = Date.UTC(+k.slice(0, 4), +k.slice(4, 6) - 1, +k.slice(6, 8), +k.slice(8, 10)) - 9 * HOUR;
      const t = amVal(rec.temp), p = amVal(rec.precipitation1h);
      if (t != null || p != null) obs[iso(ms)] = [t, p];
    }
  }
  return obs;
}

// ---------- 4. scoring ----------
const emptyCell = () => ({ n: 0, abs: 0, sum: 0, tp: 0, fp: 0, fn: 0, tn: 0, nr: 0 });
function addScore(cell, ft, fp, ot, op) {
  if (ft != null && ot != null) { const e = ft - ot; cell.n++; cell.abs += Math.abs(e); cell.sum += e; }
  if (fp != null && op != null) {
    const f = fp >= RAIN_MM, o = op >= RAIN_MM; cell.nr++;
    if (f && o) cell.tp++; else if (f && !o) cell.fp++; else if (!f && o) cell.fn++; else cell.tn++;
  }
}
function score(state, obs) {
  const verified = new Set(state.verified || []);
  let scored = 0;
  for (const [target, [ot, op]] of Object.entries(obs)) {
    if (verified.has(target)) continue;
    const tms = Date.parse(target);
    if (now - tms > 23 * HOUR) { verified.add(target); continue; } // too old: snapshots already pruned
    const day = jstDate(tms - 1), tod = TOD.find(([, a, b]) => { const h = jst(tms).h; return h >= a && h < b; })[0];
    let any = false;
    for (const [made, models] of Object.entries(state.forecasts || {})) {
      const lead = Math.round((tms - Date.parse(made)) / HOUR);
      const bin = LEAD_BINS.find(([, a, b]) => lead >= a && lead <= b); if (!bin) continue;
      for (const [model, rec] of Object.entries(models)) {
        const f = rec[target]; if (!f) continue;
        const agg = ((state.agg[day] ||= {})[model] ||= { lead: {}, tod: {} });
        addScore((agg.lead[bin[0]] ||= emptyCell()), f[0], f[1], ot, op);
        addScore((agg.tod[tod] ||= emptyCell()), f[0], f[1], ot, op);
        any = true;
      }
    }
    // only mark as done once the hour's observation is complete (has both values) and at least one forecast scored
    if (any && ot != null && op != null) { verified.add(target); scored++; }
  }
  state.verified = [...verified].sort().slice(-400);
  return scored;
}

// ---------- 5. summary ----------
function merge(a, b) { for (const k of Object.keys(b)) a[k] = (a[k] || 0) + b[k]; return a; }
function summarize(cell) {
  const r = { n: cell.n, nr: cell.nr };
  if (cell.n) { r.mae = +(cell.abs / cell.n).toFixed(2); r.bias = +(cell.sum / cell.n).toFixed(2); }
  if (cell.nr) {
    r.tp = cell.tp; r.fp = cell.fp; r.fn = cell.fn; r.tn = cell.tn;
    r.acc = +((cell.tp + cell.tn) / cell.nr).toFixed(3);
    const d = cell.tp + cell.fp + cell.fn; r.csi = d ? +(cell.tp / d).toFixed(3) : null; // null: no rain predicted or observed yet
  }
  return r;
}
function buildStats(state) {
  const since = jstDate(now - STATS_DAYS * 24 * HOUR);
  const days = Object.keys(state.agg).filter(d => d >= since).sort();
  const models = {};
  for (const key of Object.keys(MODELS)) {
    const all = emptyCell(), lead = {}, tod = {};
    for (const d of days) {
      const a = state.agg[d]?.[key]; if (!a) continue;
      for (const [b, c] of Object.entries(a.lead)) { merge(all, c); merge((lead[b] ||= emptyCell()), c); }
      for (const [t, c] of Object.entries(a.tod)) merge((tod[t] ||= emptyCell()), c);
    }
    if (!all.n && !all.nr) continue;
    models[key] = {
      label: MODELS[key], ...summarize(all),
      byLead: Object.fromEntries(Object.entries(lead).map(([b, c]) => [b, summarize(c)])),
      // tod cells count each target once per lead, so they are directly comparable with "all"
      byTod: Object.fromEntries(Object.entries(tod).map(([t, c]) => [t, summarize(c)])),
    };
  }
  const ranked = k => Object.entries(models).filter(([, m]) => m[k] != null && (k === "mae" ? m.n >= 20 : m.nr >= 20));
  const bestT = ranked("mae").sort((a, b) => a[1].mae - b[1].mae)[0]?.[0] || null;
  const bestR = ranked("csi").sort((a, b) => b[1].csi - a[1].csi)[0]?.[0] || null;
  return {
    version: 1, updated: new Date(now).toISOString(),
    station: { id: state.station.id, name: state.station.name, lat: state.station.lat, lon: state.station.lon },
    window_days: STATS_DAYS, days_recorded: days.length, first_day: days[0] || null,
    hours_scored: (state.verified || []).filter(t => Date.parse(t) >= now - STATS_DAYS * 24 * HOUR).length,
    rain_threshold_mm: RAIN_MM, lead_bins: LEAD_BINS.map(b => b[0]), tod_buckets: TOD.map(t => t[0]),
    best: { temperature: bestT, rain: bestR }, models,
  };
}

// ---------- main ----------
if (!isFinite(lat) || !isFinite(lon)) {
  console.error("HOME_LAT / HOME_LON が設定されていません(Settings → Secrets and variables → Actions で登録してください)");
  process.exit(1);
}
if (DATA_KEY.length < 12) {
  console.error("DATA_KEY(記録の合言葉、12文字以上)が設定されていません。Settings → Secrets and variables → Actions で登録してください");
  process.exit(1);
}
// remove any unencrypted files from older versions
for (const f of ["state.json", "stats.json"]) await rm(new URL(f, DATA_DIR), { force: true });
const state = await loadEncrypted("state.enc.json", { forecasts: {}, agg: {}, verified: [] });
state.forecasts ||= {}; state.agg ||= {}; state.verified ||= [];

const st = await pickStation(state);
if (state.station && state.station.id !== st.id) { console.log("観測所が変わったため、記録をやり直します"); state.forecasts = {}; state.agg = {}; state.verified = []; }
state.station = { id: st.id, name: st.name, lat: st.lat, lon: st.lon };

const obs = await fetchObs(st);
const scored = score(state, obs);

const made = iso(Math.floor(now / HOUR) * HOUR);
if (!state.forecasts[made]) {
  const fc = await fetchForecasts(st);
  if (Object.keys(fc).length) state.forecasts[made] = fc;
}
for (const m of Object.keys(state.forecasts)) if (now - Date.parse(m) > KEEP_FORECAST_H * HOUR) delete state.forecasts[m];
const keepFrom = jstDate(now - KEEP_DAYS * 24 * HOUR);
for (const d of Object.keys(state.agg)) if (d < keepFrom) delete state.agg[d];
state.lastRun = new Date(now).toISOString();

const stats = buildStats(state);
await saveEncrypted("state.enc.json", state);
await saveEncrypted("stats.enc.json", stats);
// counts only: no place, station or coordinates in the public log
console.log(`ok: observations ${Object.keys(obs).length}h / newly scored ${scored}h / forecast snapshots ${Object.keys(state.forecasts).length} / days ${stats.days_recorded}`);
