/*
 * KRP Live Timing Bridge v4.1
 * ───────────────────────────
 * Parses the Kart Racing Pro live-timing UDP stream (PiBoso forum, topic 5419)
 * and re-broadcasts it to the browser over WebSocket.
 *
 * Block layouts implemented and verified against krp_raw.log:
 *
 *   CLASSIFICATION  <session> <status> <timer> <length> <sessionLap> <numLaps>
 *                   [<type> <startEntry> <numEntries>]     <- newer servers, auto-detected
 *                   practice kart : nr bestLap lapNo totalLaps gap speed TRK|PIT
 *                   race kart     : nr raceTime|DNS|DSQ lap gap [penalty] [TRK|PIT]
 *   LAP             nr invalid sessionTime lapTime <splits…> speed
 *   BESTLAP/LASTLAP nr sessionTime lapTime lapNumber <splits…> speed
 *   SPLIT           nr splitNo time
 *   SPEED           nr speed
 *   EVENT           type name track trackLength categories
 *   ENTRY           nr name bike shortName categories guid extra
 *   TRACKPOSITION   nr x y z   (repeating)
 *   TRACKDATA       startFinish s1 s2 s3 speedTrap numSegments
 *   TRACKSEGMENT    idx type length radius angle x z height
 *
 * Record lengths are NOT fixed: a kart without a time is sent as "nr 0 TRK",
 * a race kart with no time as "nr 0 --", a DNS/DSQ kart as "nr DSQ", and the
 * number of splits depends on the track. Records are therefore parsed by shape,
 * not by a hard-coded stride.
 *
 * npm install ws
 * node timing_bridge_v4.js [ip] [password]
 */

const dgram = require('dgram');
const fs    = require('fs');

/* ── Config ─────────────────────────────────────────── */
let KRP_HOST   = '127.0.0.1';
let PASSWORD   = 'test';
const KRP_PORT   = 54420;
const LOCAL_PORT = 20000;
const WS_PORT    = 8765;

const LOG_PATH = process.env.KRP_LOG || 'krp_raw.log';

/* ── Log ────────────────────────────────────────────── */
let logStream = null;

function openLog(file) {
    logStream = fs.createWriteStream(file || LOG_PATH, { flags: 'w' });
    return logStream;
}

function log(tag, text) {
    const line = `[${tag}] ${text}`;
    console.log(line);
    if (logStream) logStream.write(line + '\n');
}

function logPacket(lines) {
    if (!logStream) return;
    logStream.write(`\n--- RAW ${lines[0]} (${lines.length} lines) ---\n`);
    lines.forEach((l, i) => logStream.write(`  [${String(i).padStart(2, '0')}] ${l}\n`));
}

/* ── Connection state ───────────────────────────────── */
const STATE = { DISCONNECTED: 0, CONNECTING: 1, CONNECTED: 2, RECEIVING: 3 };
let state = STATE.CONNECTING;
let lastConnectAt = 0, lastStartAt = 0, lastKeepAliveAt = 0;
let packetCount = 0;
let udp = null;
let wss = null;
const clients = new Set();

/* ── Race state ─────────────────────────────────────── */
function emptySession() {
    return {
        name: '', type: 'waiting', status: 'waiting', isRace: false,
        elapsedMs: 0, lengthMin: 0, currentLap: 0, totalLaps: 0,
        trackName: '', trackLength: 0,
        conditions: '', airTemp: 0, trackTemp: 0,
        splitPositions: [],
    };
}

const raceState = {
    session:        emptySession(),
    event:          { type: '', name: '', track: '', trackLength: 0 },
    entries:        {},
    classification: [],
    trackSegments:  [],
    numSegments:    0,
    messages:       [],
    connected:      false,
};

let mapSent = false;

/* ── Small helpers ──────────────────────────────────── */
const PRACTICE_KINDS = new Set(['practice', 'qualify', 'qualifying', 'warmup', 'testingday']);
const RACE_STATUS    = new Set(['DNS', 'DSQ', 'RET']);
const BIKE_STATUS    = new Set(['TRK', 'PIT']);
const PALETTE = ['#3b82f6', '#22c55e', '#f59e0b', '#8b5cf6', '#06b6d4',
                 '#ef4444', '#eab308', '#ec4899', '#14b8a6', '#f97316'];

function isInt(t) { return typeof t === 'string' && /^\d+$/.test(t); }
function isNum(t) { return typeof t === 'string' && /^-?\d+(\.\d+)?$/.test(t); }

/* A lapped gap arrives as "L", "L1" or — on current builds — "L 1",
   where the number is the laps down. */
function isLappedGap(t) {
    return typeof t === 'string' && /^L\s*\d*$/i.test(t.trim());
}
function isGap(t) {
    const v = String(t == null ? '' : t).trim();
    return v === '--' || isNum(v) || isLappedGap(v);
}
function gapLaps(t) {
    const m = String(t || '').trim().match(/^L\s*(\d+)$/i);
    return m ? parseInt(m[1], 10) : 0;
}

/* Session names come from the server ("PRACTICE 1", "FINAL", "PREFINAL", …).
   Everything that is not a practice-type session is treated as a race. */
function sessionKind(name) {
    const first = String(name || '').trim().split(/\s+/)[0].toLowerCase();
    if (!first || first === 'waiting') return 'waiting';
    return PRACTICE_KINDS.has(first) ? 'practice' : 'race';
}

function mapStatus(s) {
    switch (s) {
        case 'INPROGRESS':    return 'racing';
        case 'COMPLETE':      return 'finished';
        case 'WAITING':       return 'waiting';
        case 'PRESTART':      return 'prestart';
        case 'STARTSEQUENCE': return 'startsequence';
        case 'SIGHTINGLAP':   return 'sightinglap';
        case 'WARMUPLAP':     return 'warmuplap';
        case 'RACEOVER':      return 'raceover';
        default: {
            const v = String(s || '').toLowerCase();
            return (!v || v === '--') ? 'waiting' : v;
        }
    }
}

function colorFor(nr) {
    const n = parseInt(nr, 10);
    return PALETTE[(Number.isFinite(n) ? n : 0) % PALETTE.length];
}

/* What the timing screen should style the row as. */
function uiStatus(e) {
    const ds = (e.driverStatus || '').toUpperCase();
    if (ds === 'DNS' || ds === 'DSQ' || ds === 'RET') return 'out';
    if (e.bikeStatus === 'PIT') return 'pitted';
    return 'on_track';
}

function msToStr(ms) {
    if (!ms || ms <= 0) return '—';
    const m = Math.floor(ms / 60000);
    const s = Math.floor((ms % 60000) / 1000);
    const c = ms % 1000;
    return `${String(m).padStart(2, '0')}:${String(s).padStart(2, '0')}.${String(c).padStart(3, '0')}`;
}

/* Driver/bike identity outlives a session: ENTRY usually arrives before
   SESSION in the same packet, and the session start clears the table. */
const identities = {};

function ensureEntry(nr) {
    const key = String(nr);
    const e = raceState.entries[key] || (raceState.entries[key] = { nr: key });
    if (!e.color) e.color = colorFor(key);
    const id = identities[key];
    if (id) {
        if (!e.driver && id.driver) e.driver = id.driver;
        if (!e.kart   && id.kart)   e.kart   = id.kart;
        if (!e.short  && id.short)  e.short  = id.short;
        if (!e.class  && id.class)  e.class  = id.class;
    }
    return e;
}

function broadcast(obj) {
    if (!clients.size) return;
    const s = JSON.stringify(obj);
    for (const ws of clients) if (ws.readyState === 1) ws.send(s);
}

function sendLines(...lines) {
    if (!udp) return;
    udp.send(Buffer.from(lines.join('\n') + '\n'), KRP_PORT, KRP_HOST);
}

function addEvent(text) {
    raceState.messages.unshift({ text, time: Date.now() });
    if (raceState.messages.length > 30) raceState.messages.pop();
    broadcast({ type: 'event', text });
}

/* ── Session lifecycle ──────────────────────────────── */
function beginSession(name) {
    const old = raceState.session;
    const fresh = emptySession();
    fresh.name        = name;
    fresh.type        = sessionKind(name);
    fresh.isRace      = fresh.type === 'race';
    fresh.trackName   = old.trackName;
    fresh.trackLength = old.trackLength;
    fresh.conditions  = old.conditions;
    fresh.airTemp     = old.airTemp;
    fresh.trackTemp   = old.trackTemp;
    fresh.splitPositions = old.splitPositions;

    raceState.session        = fresh;
    raceState.entries        = {};
    raceState.classification = [];

    log('SES', `New session: ${name || '(none)'}  type:${fresh.type}`);
    broadcast({ type: 'reset', session: fresh });
}

/* Clubs restart heats under the same name: a PRESTART for the session that
   is already known means a fresh run, so drop the previous run's results. */
function syncSession(name, status) {
    if (!name || name === 'WAITING') return;
    const cur = raceState.session;
    if (name !== cur.name) { beginSession(name); return; }
    if (status === 'PRESTART' && cur.status !== 'prestart') beginSession(name);
}

/* ════════════════════════════════════════════════════════
   BLOCK SPLITTER
   ════════════════════════════════════════════════════════ */
const BLOCK_KW = new Set([
    'EVENT', 'ENTRY', 'ENTRYREMOVE',
    'SESSION', 'SESSIONSTATUS', 'SESSIONENTRY', 'WEATHER',
    'DRIVERSTATUS',
    'BESTLAP', 'LASTLAP', 'LAP',
    'SPLIT', 'SPEED',
    'PENALTY', 'PENALTYCLEAR', 'PENALTYCHANGE',
    'TRACKDATA', 'TRACKSEGMENT',
    'CLASSIFICATION', 'TRACKPOSITION',
    'CONTACT', 'END',
]);

function parseBlocks(lines) {
    let i = 0;
    while (i < lines.length) {
        const kw = (lines[i] || '').toUpperCase();
        if (!BLOCK_KW.has(kw)) { i++; continue; }
        let end = i + 1;
        while (end < lines.length && !BLOCK_KW.has((lines[end] || '').toUpperCase())) end++;
        handleBlock(kw, lines.slice(i + 1, end));
        i = end;
    }
}

function handleBlock(kw, d) {
    switch (kw) {
        case 'EVENT':           parseEvent(d);           break;
        case 'ENTRY':           parseEntry(d);           break;
        case 'ENTRYREMOVE':     parseEntryRemove(d);     break;
        case 'SESSION':         parseSession(d);         break;
        case 'SESSIONSTATUS':   parseSessionStatus(d);   break;
        case 'SESSIONENTRY':    parseSessionEntry(d);    break;
        case 'WEATHER':         parseWeather(d);         break;
        case 'LAP':             parseLapBlock(d, 'lap');   break;
        case 'BESTLAP':         parseLapBlock(d, 'best');  break;
        case 'LASTLAP':         parseLapBlock(d, 'last');  break;
        case 'SPLIT':           parseSplit(d);           break;
        case 'SPEED':           parseSpeed(d);           break;
        case 'TRACKDATA':       parseTrackData(d);       break;
        case 'TRACKSEGMENT':    parseTrackSegment(d);    break;
        case 'CLASSIFICATION':  parseClassification(d);  break;
        case 'TRACKPOSITION':   parseTrackPosition(d);   break;
        case 'DRIVERSTATUS':    parseDriverStatus(d);    break;
        case 'PENALTY':         parsePenalty(d);         break;
        case 'PENALTYCLEAR':    parsePenaltyClear(d);    break;
        case 'PENALTYCHANGE':   parsePenaltyChange(d);   break;
        case 'CONTACT':         break;
        case 'END':             break;
    }
}

/* ════════════════════════════════════════════════════════
   SESSION / EVENT / ENTRY
   ════════════════════════════════════════════════════════ */

/* EVENT: type name [track] trackLength categories
   Current KRP builds omit the track name (type name length categories). */
function parseEvent(d) {
    const type = (d[0] || '').toUpperCase();
    const name = d[1] || '';
    let track = '', trackLength = 0, categories = '';

    if (isNum(d[2]) && !isNum(d[3])) {
        trackLength = parseFloat(d[2]) || 0;
        categories  = d[3] || '';
    } else {
        track       = (d[2] || '').replace(/_/g, ' ');
        trackLength = parseFloat(d[3]) || 0;
        categories  = d[4] || '';
    }

    raceState.event = { type, name, track, trackLength, categories };
    if (track) raceState.session.trackName = track;
    raceState.session.trackLength = trackLength;
    log('EVT', `${type}  ${name}  ${track || '(track unnamed)'} (${trackLength} m)`);
    broadcast({ type: 'session', data: raceState.session });
}

/* ENTRY: nr name bike shortName categories guid extra */
function parseEntry(d) {
    const nr = d[0];
    if (!nr) return;
    const key = String(nr);
    const prev = identities[key] || {};
    identities[key] = {
        driver: d[1] || prev.driver || '',
        kart:   d[2] || prev.kart   || '',
        short:  d[3] || prev.short  || '',
        class:  d[4] || prev.class  || '',
    };
    const e = ensureEntry(key);
    if (d[1]) e.driver = d[1];
    if (d[2]) e.kart   = d[2];
    if (d[3]) e.short  = d[3];
    if (d[4]) e.class  = d[4];
    log('ENT', `#${nr}  ${e.driver}  [${e.kart}]`);
    broadcast({ type: 'entry', data: e });
}

/* ENTRYREMOVE: nr */
function parseEntryRemove(d) {
    const nr = d[0];
    if (!nr) return;
    const key = String(nr);
    if (raceState.entries[key]) {
        delete raceState.entries[key];
        raceState.classification = raceState.classification.filter(e => e.nr !== key);
        log('ENT', `#${nr} removed from session`);
        broadcast({ type: 'entry_remove', nr: key });
        broadcast({ type: 'classification', data: raceState.classification });
    }
}

/* SESSIONENTRY: nr — lists the karts taking part in the session */
function parseSessionEntry(d) {
    const nr = d[0];
    if (!nr) return;
    const e = ensureEntry(nr);
    broadcast({ type: 'entry', data: e });
}

/* SESSION: name state length(minutes for practice / laps for race) */
function parseSession(d) {
    const name = (d[0] || '').trim();
    const st   = (d[1] || '').toUpperCase();
    const len  = parseInt(d[2]) || 0;

    syncSession(name, st);

    const s = raceState.session;
    if (name) {
        s.name   = name;
        s.type   = sessionKind(name);
        s.isRace = s.type === 'race';
    }
    s.status = mapStatus(st);
    if (s.isRace) s.totalLaps = len;
    else          s.lengthMin = len;

    log('SES', `${name || s.name}  state:${st}  length:${len}  isRace:${s.isRace}`);
    broadcast({ type: 'session', data: s });
}

/* SESSIONSTATUS: name state — session start/finish notification */
function parseSessionStatus(d) {
    const name = (d[0] || '').trim();
    const st   = (d[1] || '').toUpperCase();

    syncSession(name, st);
    if (name) raceState.session.name = name;
    raceState.session.status = mapStatus(st);

    log('SES', `status: ${name || raceState.session.name} -> ${st}`);
    broadcast({ type: 'session', data: raceState.session });
}

/* WEATHER: conditions airTemp trackTemp */
function parseWeather(d) {
    const s = raceState.session;
    s.conditions = (d[0] || '').toLowerCase();
    s.airTemp    = parseFloat(d[1]) || 0;
    s.trackTemp  = parseFloat(d[2]) || 0;
    log('WX', `${d[0]}  air:${s.airTemp}°C  track:${s.trackTemp}°C`);
    broadcast({ type: 'session', data: s });
}

/* DRIVERSTATUS: nr state reason */
function parseDriverStatus(d) {
    const nr = d[0];
    if (!nr) return;
    const e = ensureEntry(nr);
    e.driverStatus       = (d[1] || '').toUpperCase();
    e.driverStatusReason = d[2] || '';
    e.status             = uiStatus(e);

    const text = `⚑ #${nr} ${e.driver || nr}  ${e.driverStatus}` +
                 (e.driverStatusReason ? ` (${e.driverStatusReason})` : '');
    addEvent(text);
    log('DRV', text);
    broadcast({ type: 'driver_status', nr, status: e.driverStatus, reason: e.driverStatusReason });

    rebuildClassification();
    broadcast({ type: 'classification', data: raceState.classification });
}

/* PENALTY: nr penaltyNo type [timeSeconds] offence */
function parsePenalty(d) {
    const nr = d[0];
    if (!nr) return;
    const type = (d[2] || '').toUpperCase();

    let timeSec = 0;
    let offence = '';
    if (type === 'TIME') {
        timeSec = parseInt(d[3]) || 0;
        offence = d[4] || '';
    } else {
        offence = d[3] || '';
    }

    const e = ensureEntry(nr);
    e.penalty = { type, timeSec, offence, no: parseInt(d[1]) || 0 };
    if (timeSec) e.penaltySec = timeSec;

    const text = `⚠️ #${nr} ${e.driver || nr}  ${type}` +
                 (timeSec ? ` +${timeSec}s` : '') +
                 (offence ? ` (${offence})` : '');
    addEvent(text);
    log('PEN', text);
    broadcast({ type: 'penalty', nr, penType: type, offence, timeSec });
}

function parsePenaltyClear(d) {
    const nr = d[0];
    if (!nr) return;
    const e = raceState.entries[nr];
    if (!e) return;
    delete e.penalty;
    e.penaltySec = 0;
    log('PEN', `#${nr} penalty cleared`);
    broadcast({ type: 'penalty_clear', nr });
}

function parsePenaltyChange(d) {
    const nr = d[0];
    if (!nr) return;
    const key = parseInt(d[1]) || 0;
    const timeSec = parseInt(d[2]) || 0;
    const e = raceState.entries[nr];
    if (!e) return;
    e.penalty = { ...(e.penalty || { type: 'TIME', offence: '', no: key }), timeSec };
    if (timeSec) e.penaltySec = timeSec;
    log('PEN', `#${nr} penalty ${key} -> ${timeSec}s`);
    broadcast({ type: 'penalty_change', nr, timeSec });
}

/* ════════════════════════════════════════════════════════
   LAP / SPLIT / SPEED
   ════════════════════════════════════════════════════════ */

/* Splits are cumulative and their number depends on the track;
   the last token is the speed trap when it carries a decimal point. */
function splitTail(tokens) {
    const t = tokens.filter(x => x !== '');
    let speed = 0;
    if (t.length && (t[t.length - 1].includes('.') || t.length > 3)) {
        speed = parseFloat(t.pop()) || 0;
    }
    const splits = t.map(x => parseInt(x, 10)).filter(Number.isFinite);
    return { splits, speed };
}

/* LAP:             nr invalid sessionTime lapTime <splits…> speed
   BESTLAP/LASTLAP: nr sessionTime lapTime lapNumber <splits…> speed */
function parseLapBlock(d, mode) {
    const nr = d[0];
    if (!nr) return;

    let invalid = false, sessionTime = 0, lapTime = 0, lapNo = 0, rest;
    if (mode === 'lap') {
        invalid     = parseInt(d[1], 10) !== 0;
        sessionTime = parseInt(d[2], 10) || 0;
        lapTime     = parseInt(d[3], 10) || 0;
        rest        = d.slice(4);
    } else {
        sessionTime = parseInt(d[1], 10) || 0;
        lapTime     = parseInt(d[2], 10) || 0;
        lapNo       = parseInt(d[3], 10) || 0;
        rest        = d.slice(4);
    }
    if (!lapTime) return;

    const { splits, speed } = splitTail(rest);
    const e = ensureEntry(nr);
    const isBest = !invalid && (!e.bestIndivLap || lapTime < e.bestIndivLap);

    if (mode !== 'best') {
        e.lastLap        = lapTime;
        e.lastLapNo      = lapNo;
        e.lastLapInvalid = invalid;
        e.lastSplits     = splits;
    }
    if (speed) e.speedTrap = speed;

    splits.forEach((ms, i) => {
        const k = 'bestS' + (i + 1);
        if (!e[k] || ms < e[k]) e[k] = ms;
    });
    e.sectorCount = Math.max(e.sectorCount || 0, splits.length);

    if (isBest) {
        e.bestIndivLap = lapTime;
        e.bestLap      = lapTime;
    }

    const marker = invalid ? '✗' : (isBest ? '🏆' : '🔵');
    const text = `${marker} #${nr} ${e.driver || '#' + nr}  lap:${msToStr(lapTime)}` +
                 (invalid ? ' INVALID' : '') + (isBest ? ' (BEST)' : '');
    addEvent(text);
    log('LAP', text);

    rebuildClassification();
    broadcast({
        type: 'lap', nr,
        ms: lapTime, best: e.bestLap || 0, isBest, invalid,
        speed, splits, lapNo, sessionTime,
    });
}

/* SPLIT: nr splitNo time — split number is 0-based */
function parseSplit(d) {
    const nr = d[0];
    if (!nr) return;
    const idx = parseInt(d[1], 10);
    const ms  = parseInt(d[2], 10) || 0;
    if (!Number.isFinite(idx)) return;
    ensureEntry(nr)[`splitCur${idx}`] = ms;
    broadcast({ type: 'split', nr, split: idx, ms });
    log('SPL', `#${nr}  S${idx + 1}  ${msToStr(ms)}`);
}

/* SPEED: nr speed */
function parseSpeed(d) {
    const nr = d[0];
    if (!nr) return;
    const speed = parseFloat(d[1]) || 0;
    ensureEntry(nr).speedTrap = speed;
    broadcast({ type: 'speed', nr, speed });
}

/* ════════════════════════════════════════════════════════
   TRACK GEOMETRY
   ════════════════════════════════════════════════════════ */

/* TRACKDATA: split positions… numSegments (the segment count is last and
   the number of positions varies between builds). */
function parseTrackData(d) {
    const nums = d.filter(isNum).map(Number);
    if (!nums.length) return;
    raceState.numSegments = nums[nums.length - 1] || 0;
    raceState.session.splitPositions = nums.slice(0, -1);
    raceState.trackSegments = [];
    mapSent = false;
    log('TRK', `${raceState.numSegments} segments, ${nums.length - 1} split positions`);
}

/* TRACKSEGMENT: idx type length radius angle x z height */
function parseTrackSegment(d) {
    const idx = parseInt(d[0], 10);
    if (!Number.isFinite(idx)) return;

    const seg = {
        idx,
        type: parseInt(d[1], 10) || 0,
        len:  parseFloat(d[2]) || 0,
        x:    parseFloat(d[5]) || 0,
        z:    parseFloat(d[6]) || 0,
        y:    parseFloat(d[7]) || 0,
    };
    while (raceState.trackSegments.length <= idx) raceState.trackSegments.push(null);
    raceState.trackSegments[idx] = seg;

    const filled = raceState.trackSegments.filter(Boolean).length;
    const total  = raceState.numSegments;
    if (!mapSent && total > 0 && filled === total) {
        mapSent = true;
        log('TRK', `Map complete (${total} segments)`);
        broadcast({ type: 'track_map', segments: raceState.trackSegments.filter(Boolean) });
    }
}

/* TRACKPOSITION: nr x y z (repeating) — only karts currently on track */
function parseTrackPosition(d) {
    let i = 0;
    while (d.length - i >= 4) {
        if (!isInt(d[i]) || parseInt(d[i], 10) <= 0) { i++; continue; }
        const e = ensureEntry(d[i]);
        e.x = parseFloat(d[i + 1]) || 0;
        e.y = parseFloat(d[i + 2]) || 0;
        e.z = parseFloat(d[i + 3]) || 0;
        broadcast({ type: 'pos', nr: e.nr, x: e.x, y: e.y, z: e.z });
        i += 4;
    }
}

/* ════════════════════════════════════════════════════════
   CLASSIFICATION
   ════════════════════════════════════════════════════════ */

/* Practice record, terminated by the bike status:
     nr bestLap lapNo totalLaps gap speed TRK|PIT
     nr 0 TRK                                   (no timed lap yet)   */
function parsePracticeRegion(tokens) {
    const out = [];
    let i = 0;
    while (i < tokens.length) {
        const nr = tokens[i];
        if (!isInt(nr) || parseInt(nr, 10) <= 0) return null;
        i++;

        if (!isNum(tokens[i])) return null;
        const bestLap = parseInt(tokens[i], 10);
        i++;

        /* short form: nr 0 TRK */
        if (bestLap === 0 && BIKE_STATUS.has((tokens[i] || '').toUpperCase())) {
            out.push({ nr, bestLap: 0, lapNo: 0, laps: 0, gapRaw: '--', speed: 0,
                       bike: tokens[i].toUpperCase() });
            i++;
            continue;
        }

        if (!isInt(tokens[i])) return null;
        const lapNo = parseInt(tokens[i], 10); i++;

        if (!isInt(tokens[i])) return null;
        const laps = parseInt(tokens[i], 10); i++;

        const gapRaw = tokens[i]; i++;
        if (!isGap(gapRaw)) return null;

        if (!isNum(tokens[i])) return null;
        const speed = parseFloat(tokens[i]); i++;

        const bike = (tokens[i] || '').toUpperCase(); i++;
        if (!BIKE_STATUS.has(bike)) return null;

        out.push({ nr, bestLap, lapNo, laps, gapRaw, speed, bike });
    }
    return out.length ? out : null;
}

/* Race record, variable length:
     nr raceTime lap gap [penalty|bikeStatus]
     nr 0 --                     (no race time yet)
     nr DNS                      (DNS / DSQ / RET)
   The record boundary is resolved by requiring the whole region to parse. */
function parseRaceRegion(tokens) {
    const memo = new Map();

    function go(p) {
        if (p === tokens.length) return [];
        if (memo.has(p)) return memo.get(p);

        const nr = tokens[p];
        if (!isInt(nr) || parseInt(nr, 10) <= 0) return null;

        const nxt = (tokens[p + 1] || '').toUpperCase();
        const cands = [];

        if (RACE_STATUS.has(nxt)) {
            cands.push({ len: 2, rec: { nr, status: nxt } });
        } else if (isNum(tokens[p + 1])) {
            const time = parseInt(tokens[p + 1], 10);
            if (time > 0) {
                if (isInt(tokens[p + 2])) {
                    const lap = parseInt(tokens[p + 2], 10);
                    const g = tokens[p + 3];
                    if (isGap(g)) {
                        cands.push({ len: 5, rec: { nr, time, lap, gapRaw: g, extra: tokens[p + 4] } });
                        cands.push({ len: 4, rec: { nr, time, lap, gapRaw: g } });
                    }
                }
            } else {
                const g = tokens[p + 2];
                if (isGap(g)) {
                    cands.push({ len: 4, rec: { nr, time: 0, lap: 0, gapRaw: g, extra: tokens[p + 3] } });
                    cands.push({ len: 3, rec: { nr, time: 0, lap: 0, gapRaw: g } });
                }
            }
        }

        for (const c of cands) {
            const rest = go(p + c.len);
            if (rest) {
                const rec = [c.rec].concat(rest);
                memo.set(p, rec);
                return rec;
            }
        }
        return null;
    }

    return go(0);
}

/* Newer servers insert "Classification Type, Start Entry, Number of Entries"
   between the header and the kart list. */
function hasTypeHeader(d, kindHint) {
    const t = d[6];
    if (t !== '0' && t !== '1' && t !== '2') return false;
    if (!isInt(d[7]) || !isInt(d[8])) return false;
    return t === (kindHint === 'race' ? '2' : '1');
}

function parseEntryRegion(d, kindHint) {
    if (d.length <= 6) return null;

    const offsets = hasTypeHeader(d, kindHint) ? [9, 6] : [6, 9];
    const kinds   = kindHint === 'race' ? ['race', 'practice'] : ['practice', 'race'];

    for (const off of offsets) {
        if (d.length - off < 2) continue;
        const tokens = d.slice(off);
        for (const kind of kinds) {
            const records = kind === 'race'
                ? parseRaceRegion(tokens)
                : parsePracticeRegion(tokens);
            if (!records) continue;
            if (off === 9 && isInt(d[8]) && records.length !== parseInt(d[8], 10)) continue;
            return { kind, offset: off, records };
        }
    }
    return null;
}

function applyRecords(records, kind) {
    const isRace = kind === 'race';
    const leaderLaps = records.reduce((m, r) => {
        const l = isRace ? (r.lap || 0) : (r.laps || 0);
        return Math.max(m, l);
    }, 0);

    records.forEach((r, idx) => {
        const nr = String(r.nr);
        const e = ensureEntry(nr);
        e.pos = idx + 1;

        let gapMs = 0, lapped = false;

        if (isRace) {
            e.raceTime = r.time || 0;
            e.laps     = r.lap  || 0;

            if (r.status) {                     /* DNS / DSQ / RET */
                e.driverStatus = r.status;
                e.gapMs    = 0;
                e.isLapped = false;
                e.lapsDown = 0;
                e.status   = uiStatus(e);
                return;
            }

            if (isLappedGap(r.gapRaw))  lapped = true;
            else if (r.gapRaw === '--') lapped = idx > 0 && e.laps < leaderLaps;
            else                        gapMs  = parseInt(r.gapRaw, 10) || 0;

            const extra = (r.extra || '').toUpperCase();
            if (BIKE_STATUS.has(extra))        e.bikeStatus = extra;
            else if (isInt(r.extra))           e.penaltySec = parseInt(r.extra, 10);
        } else {
            e.bestLap  = r.bestLap || 0;
            e.laps     = r.laps || 0;
            e.speedTrap = r.speed || 0;
            e.bikeStatus = r.bike;
            if (isLappedGap(r.gapRaw))    lapped = true;
            else if (r.gapRaw !== '--')   gapMs  = parseInt(r.gapRaw, 10) || 0;
        }

        e.gapMs    = gapMs;
        e.isLapped = lapped;
        e.lapsDown = lapped ? gapLaps(r.gapRaw) : 0;

        if (e.bestIndivLap && (!e.bestLap || e.bestIndivLap < e.bestLap)) {
            e.bestLap = e.bestIndivLap;
        }
        e.status = uiStatus(e);

        /* a kart in the pits has no live track position */
        if (e.bikeStatus === 'PIT') { delete e.x; delete e.y; delete e.z; }
    });
}

/*
 * CLASSIFICATION header:
 *   d[0] session   d[1] status   d[2] timer(ms)   d[3] length(min)
 *   d[4] sessionLap   d[5] numberOfLaps   [d[6..8] type/startEntry/numEntries]
 */
function parseClassification(d) {
    const name   = d[0] || raceState.session.name;
    const status = (d[1] || '').toUpperCase();

    /* beginSession swaps raceState.session — read it afterwards */
    syncSession(name, status);

    const s    = raceState.session;
    const kind = sessionKind(s.name);
    s.type      = kind;
    s.isRace    = kind === 'race';
    s.status    = mapStatus(status);
    s.elapsedMs = parseInt(d[2], 10) || 0;
    s.currentLap = parseInt(d[4], 10) || 0;
    s.totalLaps  = s.isRace ? (parseInt(d[5], 10) || 0) : 0;
    s.lengthMin  = s.isRace ? 0 : (parseInt(d[3], 10) || 0);

    const parsed = parseEntryRegion(d, kind);
    if (parsed) {
        applyRecords(parsed.records, parsed.kind);
        rebuildClassification();
        broadcast({ type: 'classification', data: raceState.classification });
    } else {
        log('CLS', `could not parse entries (${d.length} tokens) — header kept`);
    }

    broadcast({ type: 'session', data: s });
}

/* ════════════════════════════════════════════════════════
   HELPERS
   ════════════════════════════════════════════════════════ */
function rebuildClassification() {
    raceState.classification = Object.values(raceState.entries)
        .filter(e => e.pos > 0)
        .sort((a, b) => a.pos - b.pos);
}

/* ════════════════════════════════════════════════════════
   PACKET HANDLING
   ════════════════════════════════════════════════════════ */

/* Returns the message id that must be ACKed (MSG packets) or null. */
function handleLines(lines) {
    const cmd = lines[0].toUpperCase();

    switch (cmd) {
        case 'OK':
            if (state !== STATE.RECEIVING) {
                state = STATE.CONNECTED;
                lastStartAt = 0;
                raceState.connected = true;
                log('KRP', 'Connected ✓');
                broadcast({ type: 'connected' });
            }
            break;

        case 'WRONGPASSWORD':
            log('KRP', '❌ Wrong password');
            state = STATE.DISCONNECTED;
            lastConnectAt = Date.now();
            raceState.connected = false;
            broadcast({ type: 'error', message: 'Wrong password' });
            break;

        case 'FULL':
            log('KRP', '❌ Server already has a client');
            state = STATE.DISCONNECTED;
            lastConnectAt = Date.now();
            raceState.connected = false;
            broadcast({ type: 'error', message: 'Server full (another timing client is connected)' });
            break;

        case 'ALIVE':
            lastKeepAliveAt = Date.now();
            break;

        case 'MSG': {
            if (state !== STATE.RECEIVING) log('KRP', 'Receiving data');
            state = STATE.RECEIVING;
            lastKeepAliveAt = Date.now();
            const msgId = lines[1] || '';
            parseBlocks(lines.slice(2));
            return msgId;
        }

        case 'DATA': {
            if (state !== STATE.RECEIVING) log('KRP', 'Receiving data');
            state = STATE.RECEIVING;
            lastKeepAliveAt = Date.now();
            parseBlocks(lines.slice(1));
            break;
        }

        default:
            log('UNK', cmd);
    }
    return null;
}

/* One UDP datagram -> log once, parse once, ACK once. */
function handleDatagram(text) {
    const lines = String(text)
        .split('\n')
        .map(l => l.replace(/\r$/, '').trim())
        .filter(Boolean);
    if (!lines.length) return null;

    packetCount++;
    logPacket(lines);

    const ack = handleLines(lines);
    if (ack) sendLines('ACK', ack);
    return ack;
}

/* ════════════════════════════════════════════════════════
   CONNECTION LOOP
   ════════════════════════════════════════════════════════ */
function tick() {
    const now = Date.now();

    if (state === STATE.CONNECTING) {
        if (now - lastConnectAt > 2000) {
            sendLines('CONNECT', PASSWORD);
            lastConnectAt = now;
            log('KRP', 'CONNECT sent');
        }
    } else if (state === STATE.CONNECTED) {
        if (now - lastStartAt > 1000) {
            /* param 1 = track data + kart positions, param 2 = contacts off */
            sendLines('START', '1', '0');
            lastStartAt = now;
            lastKeepAliveAt = now;
            log('KRP', 'START sent');
        }
    } else if (state === STATE.RECEIVING) {
        if (now - lastKeepAliveAt > 15000) {
            sendLines('KEEPALIVE');
            lastKeepAliveAt = now;
        }
    } else if (state === STATE.DISCONNECTED) {
        if (now - lastConnectAt > 5000) {
            log('KRP', 'Reconnecting…');
            state = STATE.CONNECTING;
            lastConnectAt = now;
            raceState.connected = false;
            broadcast({ type: 'disconnected' });
        }
    }
}

function printSummary() {
    const s = raceState.session;
    log('SYS', '─'.repeat(60));
    log('SYS', `Event   : ${raceState.event.name || '—'}`);
    log('SYS', `Track   : ${s.trackName || '—'} ${s.trackLength ? '(' + s.trackLength + ' m)' : ''}`);
    log('SYS', `Session : ${s.name || '—'}  [${s.isRace ? 'RACE' : 'PRACTICE'}]  ${s.status}`);
    log('SYS', `Karts   : ${Object.keys(raceState.entries).length}`);
    log('SYS', `Packets : ${packetCount}`);

    const sorted = raceState.classification;
    sorted.forEach(e => {
        const time = e.isRace
            ? (e.raceTime ? msToStr(e.raceTime) : '—')
            : (e.bestLap ? msToStr(e.bestLap) : '—');
        log('SYS', `  P${String(e.pos).padStart(2)}  #${String(e.nr).padStart(3)}  ` +
                   `${(e.driver || '').padEnd(24)}  time:${time}  ` +
                   `best:${e.bestLap ? msToStr(e.bestLap) : '—'}  laps:${e.laps || 0}` +
                   `${e.isLapped ? '  LAP' : ''}`);
    });
}

function main() {
    KRP_HOST = process.argv[2] || '127.0.0.1';
    PASSWORD = process.argv[3] || 'test';

    openLog();

    const { WebSocketServer } = require('ws');
    wss = new WebSocketServer({ port: WS_PORT });

    wss.on('connection', ws => {
        clients.add(ws);
        try { ws.send(JSON.stringify({ type: 'snapshot', data: raceState })); } catch (e) { /* ignore */ }
        log('WS', `Client connected (${clients.size} total)`);

        ws.on('close', () => {
            clients.delete(ws);
            log('WS', `Client disconnected (${clients.size} remaining)`);
        });
        ws.on('error', () => {});
    });

    udp = dgram.createSocket('udp4');
    udp.on('error', err => log('ERR', err.message));
    udp.bind(LOCAL_PORT, '0.0.0.0', () => {
        log('SYS', `Listening UDP :${LOCAL_PORT}   WS :${WS_PORT}`);
        log('SYS', `Connecting to KRP ${KRP_HOST}:${KRP_PORT}  (pass: ${PASSWORD || '(none)'})`);
    });

    udp.on('message', buf => {
        try {
            handleDatagram(buf.toString('utf8'));
        } catch (err) {
            log('ERR', `packet: ${err.message}`);
        }
    });

    setInterval(tick, 100);

    process.on('SIGINT', () => {
        printSummary();
        sendLines('DISCONNECT');
        state = STATE.DISCONNECTED;
        setTimeout(() => {
            if (logStream) logStream.end(() => process.exit(0));
            else process.exit(0);
        }, 200);
    });
}

module.exports = {
    raceState,
    STATE,
    handleDatagram,
    handleLines,
    parseBlocks,
    parseEntryRegion,
    parseClassification,
    parseLapBlock,
    parsePracticeRegion,
    parseRaceRegion,
    beginSession,
    openLog,
    get state() { return state; },
    get packetCount() { return packetCount; },
};

if (require.main === module) main();
