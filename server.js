// =====================================================================
//  Arena of Clodo Legends — serveur relais multijoueur
//  Aucune dépendance : Node.js (>= 18) suffit.  Lancer :  node server.js
//
//  Rôle du serveur (volontairement minimal) :
//   * salons avec code à 4 lettres, choix d'équipe, hôte ;
//   * relais des messages de draft / préparation entre joueurs ;
//   * « lockstep » : chaque joueur envoie ses commandes par tour (50 ms),
//     le serveur renvoie à tous le tour complet dès que tout le monde l'a envoyé.
//     Le combat est calculé à l'identique sur chaque PC (moteur déterministe).
// =====================================================================
"use strict";
const http = require("http");
const crypto = require("crypto");

const PORT = process.env.PORT || 8080;
const TURN_TIMEOUT_MS = 20000;     // un joueur muet trop longtemps est déconnecté
const START_TIMEOUT_MS = 60000;    // plus de patience au lancement (chargement du combat)
const HASH_EVERY = 40;             // contrôle anti-désynchronisation (tours)
const MAX_ROOMS = 500;

// ------------------------------------------------------------------ WebSocket minimal (RFC 6455)
const GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

class Sock {
  constructor(socket) {
    this.socket = socket;
    this.buf = Buffer.alloc(0);
    this.frag = [];
    this.open = true;
    this.onmessage = null;
    this.onclose = null;
    socket.setNoDelay(true);
    socket.on("data", (d) => this._data(d));
    socket.on("close", () => this._closed());
    socket.on("error", () => this._closed());
  }
  _closed() {
    if (!this.open) return;
    this.open = false;
    if (this.onclose) this.onclose();
  }
  _data(d) {
    this.buf = Buffer.concat([this.buf, d]);
    for (;;) {
      if (this.buf.length < 2) return;
      const b0 = this.buf[0], b1 = this.buf[1];
      const fin = (b0 & 0x80) !== 0, op = b0 & 0x0f, masked = (b1 & 0x80) !== 0;
      let len = b1 & 0x7f, off = 2;
      if (len === 126) { if (this.buf.length < 4) return; len = this.buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (this.buf.length < 10) return; len = Number(this.buf.readBigUInt64BE(2)); off = 10; }
      if (len > 1 << 20) { this.close(); return; }            // 1 Mo max
      const need = off + (masked ? 4 : 0) + len;
      if (this.buf.length < need) return;
      let payload = this.buf.subarray(off + (masked ? 4 : 0), need);
      if (masked) {
        const m = this.buf.subarray(off, off + 4);
        payload = Buffer.from(payload);
        for (let i = 0; i < payload.length; i++) payload[i] ^= m[i & 3];
      }
      this.buf = this.buf.subarray(need);
      if (op === 0x8) { this.close(); return; }                // close
      if (op === 0x9) { this._send(0xA, payload); continue; }  // ping -> pong
      if (op === 0xA) continue;                                // pong
      if (op === 0x1 || op === 0x2 || op === 0x0) {
        this.frag.push(payload);
        if (fin) {
          const msg = Buffer.concat(this.frag).toString("utf8");
          this.frag = [];
          if (this.onmessage) this.onmessage(msg);
        }
      }
    }
  }
  _send(op, payload) {
    if (!this.open) return;
    const len = payload.length;
    let head;
    if (len < 126) head = Buffer.from([0x80 | op, len]);
    else if (len < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(len, 2); }
    else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeBigUInt64BE(BigInt(len), 2); }
    try { this.socket.write(Buffer.concat([head, payload])); } catch (e) { this._closed(); }
  }
  send(obj) { this._send(0x1, Buffer.from(JSON.stringify(obj), "utf8")); }
  close() {
    if (this.open) { try { this._send(0x8, Buffer.alloc(0)); this.socket.end(); } catch (e) {} }
    this._closed();
  }
}

// ------------------------------------------------------------------ salons
const rooms = new Map();     // code -> room
let nextId = 1;

function newCode() {
  const L = "ABCDEFGHJKLMNPQRSTUVWXYZ";   // sans I ni O (lisibilité)
  for (;;) {
    let c = "";
    for (let i = 0; i < 4; i++) c += L[crypto.randomInt(L.length)];
    if (!rooms.has(c)) return c;
  }
}

function roomState(r) {
  return {
    t: "room", code: r.code, host: r.host, size: r.size, diff: r.diff, phase: r.phase, ver: r.ver,
    players: [...r.players.values()].map((p) => ({ id: p.id, name: p.name, team: p.team, slot: p.slot })),
  };
}
function broadcast(r, obj, except) {
  for (const p of r.players.values()) if (p !== except) p.sock.send(obj);
}
function pushRoom(r) { broadcast(r, roomState(r)); }

function freeSlot(r, team) {
  const used = new Set([...r.players.values()].filter((p) => p.team === team).map((p) => p.slot));
  for (let s = 0; s < r.size; s++) if (!used.has(s)) return s;
  return -1;
}

// Remet les emplacements en ordre (0,1,2…) dans chaque équipe, dans l'ordre d'arrivée.
function compactSlots(r) {
  for (const team of [0, 1]) {
    const list = [...r.players.values()].filter((p) => p.team === team).sort((a, b) => a.slot - b.slot);
    list.forEach((p, i) => { p.slot = i; });
  }
}

function leaveRoom(p) {
  const r = p.room;
  if (!r) return;
  p.room = null;
  r.players.delete(p.id);
  if (r.players.size === 0) { stopGame(r); rooms.delete(r.code); return; }
  if (r.phase === "game" && r.game && r.game.active.has(p.id)) {
    r.game.active.delete(p.id);
    r.game.drops.push({ c: "drop", team: p.team, slot: p.slot });
    broadcast(r, { t: "left", id: p.id, name: p.name, team: p.team, slot: p.slot });
    if (!r.game.t0) { let all = true; for (const id of r.game.active) if (!r.game.ready.has(id)) all = false; if (all) beginClock(r); }
  } else if (r.phase === "lobby") {
    compactSlots(r);
  } else {
    broadcast(r, { t: "left", id: p.id, name: p.name, team: p.team, slot: p.slot });
  }
  if (r.host === p.id) {
    r.host = [...r.players.keys()][0];
  }
  pushRoom(r);
}

// ------------------------------------------------------------------ horloge du combat
// Le serveur donne le rythme : un « tour » toutes les TURN_MS, avec les commandes reçues
// depuis le tour précédent. Un joueur lent ou qui décroche ne bloque plus les autres.
const TURN_MS = 50;
function startGame(r) {
  r.phase = "game";
  stopGame(r);
  r.game = {
    active: new Set(r.players.keys()),
    ready: new Set(),
    pending: [],           // commandes reçues depuis le dernier tour
    hashes: new Map(),     // tour -> Map(id -> hash)
    next: 0,
    drops: [],
    t0: 0,                 // début de l'horloge (0 = pas encore lancée)
    created: Date.now(),
    lastSeen: new Map(),
  };
  for (const id of r.players.keys()) r.game.lastSeen.set(id, Date.now());
}

function stopGame(r) {
  if (r.game && r.game.timer) clearInterval(r.game.timer);
}

function beginClock(r) {
  const g = r.game;
  if (!g || g.t0) return;
  g.t0 = Date.now();
  g.timer = setInterval(() => tickGame(r), 10);
}

function tickGame(r) {
  const g = r.game;
  if (!g || r.phase !== "game") { stopGame(r); return; }
  const due = Math.floor((Date.now() - g.t0) / TURN_MS);
  let guard = 0;
  while (g.next <= due && guard++ < 40) {
    let cmds = g.pending;
    g.pending = [];
    if (g.drops.length) { cmds = cmds.concat(g.drops); g.drops = []; }
    broadcast(r, { t: "turn", k: g.next, c: cmds });
    g.next++;
  }
}

// compat : l'ancien code appelait flushTurns après un départ
function flushTurns(r) {}

// ------------------------------------------------------------------ messages
function handle(p, raw) {
  let m;
  try { m = JSON.parse(raw); } catch (e) { return; }
  if (!m || typeof m.t !== "string") return;
  const r = p.room;
  switch (m.t) {
    case "hello":
      p.name = String(m.name || "Gladiateur").slice(0, 20);
      p.ver = String(m.ver || "");
      p.sock.send({ t: "welcome", id: p.id });
      break;
    case "create": {
      if (r) leaveRoom(p);
      if (rooms.size >= MAX_ROOMS) { p.sock.send({ t: "error", msg: "Serveur plein, réessayez plus tard." }); return; }
      const code = newCode();
      const room = { code, host: p.id, size: clamp(m.size, 1, 4, 2), diff: clamp(m.diff, 0, 2, 1), phase: "lobby", ver: p.ver, players: new Map(), game: null };
      rooms.set(code, room);
      p.room = room; p.team = 0; p.slot = 0;
      room.players.set(p.id, p);
      pushRoom(room);
      break;
    }
    case "join": {
      const code = String(m.code || "").toUpperCase().trim();
      const room = rooms.get(code);
      if (!room) { p.sock.send({ t: "error", msg: "Aucun salon avec le code " + code + "." }); return; }
      if (room.ver !== p.ver) { p.sock.send({ t: "error", msg: "Version différente de celle de l'hôte (" + room.ver + "). Mettez le jeu à jour." }); return; }
      if (room.phase !== "lobby") { p.sock.send({ t: "error", msg: "La partie de ce salon a déjà commencé." }); return; }
      let team = 0, slot = freeSlot(room, 0);
      const s1 = freeSlot(room, 1);
      // équilibre : on rejoint l'équipe la moins remplie
      const n0 = [...room.players.values()].filter((q) => q.team === 0).length;
      const n1 = [...room.players.values()].filter((q) => q.team === 1).length;
      if ((n1 < n0 && s1 >= 0) || slot < 0) { team = 1; slot = s1; }
      if (slot < 0) { p.sock.send({ t: "error", msg: "Salon complet." }); return; }
      if (r) leaveRoom(p);
      p.room = room; p.team = team; p.slot = slot;
      room.players.set(p.id, p);
      pushRoom(room);
      break;
    }
    case "leave":
      leaveRoom(p);
      p.sock.send({ t: "left_room" });
      break;
    case "set":
      if (!r || r.host !== p.id || r.phase !== "lobby") return;
      if (m.size !== undefined) {
        const ns = clamp(m.size, 1, 4, r.size);
        // on refuse de réduire sous le nombre de joueurs présents dans une équipe
        for (const team of [0, 1]) {
          if ([...r.players.values()].filter((q) => q.team === team).length > ns) {
            p.sock.send({ t: "error", msg: "Trop de joueurs dans une équipe pour ce format." }); return;
          }
        }
        r.size = ns;
        compactSlots(r);
      }
      if (m.diff !== undefined) r.diff = clamp(m.diff, 0, 2, r.diff);
      pushRoom(r);
      break;
    case "team": {
      if (!r || r.phase !== "lobby") return;
      const team = m.team === 1 ? 1 : 0;
      if (team === p.team) return;
      const s = freeSlot(r, team);
      if (s < 0) { p.sock.send({ t: "error", msg: "Cette équipe est complète." }); return; }
      p.team = team; p.slot = s;
      compactSlots(r);
      pushRoom(r);
      break;
    }
    case "phase":
      if (!r || r.host !== p.id) return;
      if (m.phase === "lobby") { stopGame(r); r.phase = "lobby"; r.game = null; }
      else if (m.phase === "draft") { if (r.phase === "lobby") r.phase = "draft"; }
      pushRoom(r);
      break;
    case "relay": {
      if (!r) return;
      const out = { t: "relay", from: p.id, d: m.d };
      if (m.to === "host") { const h = r.players.get(r.host); if (h) h.sock.send(out); }
      else if (m.to === "all") broadcast(r, out);
      else if (m.to === "others") broadcast(r, out, p);
      else { const q = r.players.get(m.to); if (q) q.sock.send(out); }
      break;
    }
    case "start":
      if (!r || r.host !== p.id) return;
      startGame(r);
      pushRoom(r);
      break;
    case "ready": {
      // le combat est chargé chez ce joueur ; l'horloge démarre quand tout le monde est prêt
      if (!r || !r.game) return;
      r.game.ready.add(p.id);
      let all = true;
      for (const id of r.game.active) if (!r.game.ready.has(id)) all = false;
      if (all) beginClock(r);
      break;
    }
    case "in": {
      if (!r || !r.game || !r.game.active.has(p.id)) return;
      const g = r.game;
      g.lastSeen.set(p.id, Date.now());
      const cmds = Array.isArray(m.c) ? m.c.slice(0, 32) : [];
      for (const c of cmds) if (c && typeof c === "object") g.pending.push(c);
      if (m.h !== undefined) {
        const k = Number(m.k) | 0;
        if (!g.hashes.has(k)) g.hashes.set(k, new Map());
        const hs = g.hashes.get(k);
        hs.set(p.id, m.h);
        if (hs.size >= 2 && new Set(hs.values()).size > 1) broadcast(r, { t: "desync", k: k });
        if (g.hashes.size > 50) g.hashes.delete(g.hashes.keys().next().value);
      }
      break;
    }
    case "ping":
      p.sock.send({ t: "pong", s: m.s });
      break;
  }
}

function clamp(v, a, b, def) {
  v = Number(v);
  if (!Number.isFinite(v)) return def;
  return Math.max(a, Math.min(b, Math.round(v)));
}

// ------------------------------------------------------------------ joueurs lents
setInterval(() => {
  const now = Date.now();
  for (const r of rooms.values()) {
    const g = r.game;
    if (!g || r.phase !== "game" || g.active.size === 0) continue;
    // l'horloge démarre même si quelqu'un tarde à charger
    if (!g.t0 && now - g.created > START_TIMEOUT_MS / 4) beginClock(r);
  }
}, 2000);

// ------------------------------------------------------------------ serveur HTTP + upgrade
const server = http.createServer((req, res) => {
  res.writeHead(200, { "Content-Type": "text/plain; charset=utf-8", "Access-Control-Allow-Origin": "*" });
  res.end("Arena of Clodo — serveur multijoueur OK. Salons actifs : " + rooms.size + "\n");
});

server.on("upgrade", (req, socket) => {
  const key = req.headers["sec-websocket-key"];
  if (!key || (req.headers.upgrade || "").toLowerCase() !== "websocket") { socket.destroy(); return; }
  const accept = crypto.createHash("sha1").update(key + GUID).digest("base64");
  socket.write("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: " + accept + "\r\n\r\n");
  const p = { id: nextId++, name: "Gladiateur", ver: "", room: null, team: 0, slot: 0, sock: new Sock(socket) };
  p.sock.onmessage = (msg) => { try { handle(p, msg); } catch (e) { console.error(e); } };
  p.sock.onclose = () => leaveRoom(p);
});

// garde les connexions en vie derrière les hébergeurs (ping toutes les 25 s)
setInterval(() => {
  for (const r of rooms.values()) for (const p of r.players.values()) p.sock._send(0x9, Buffer.alloc(0));
}, 25000);

server.listen(PORT, () => console.log("Serveur Arena of Clodo à l'écoute sur le port " + PORT));
