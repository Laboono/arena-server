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
const PROTO = 5;                   // 5 : recherche de partie (files 1v1…4v4)
const ACCEPT_MS = Number(process.env.ACCEPT_MS) || 10000;   // fenêtre « Partie trouvée ! »

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
    t: "room", code: r.code, host: r.host, size: r.size, diff: r.diff, phase: r.phase, ver: r.ver, mode: r.mode || "classic",
    mm: r.mm ? r.qsize : 0,
    players: [...r.players.values()].map((p) => ({ id: p.id, name: p.name, team: p.team, slot: p.slot })),
  };
}
function broadcast(r, obj, except) {
  for (const p of r.players.values()) if (p !== except) p.sock.send(obj);
}
function pushRoom(r) { broadcast(r, roomState(r)); }

// Pas d'IA en multijoueur : seuls les joueurs présents jouent (8 au maximum).
// Arène : deux camps (0 = bleu, 1 = rouge), de taille libre (1v4, 2v3…).
// Battle Royale : chacun est seul dans son « équipe » (0 à 7), toujours à l'emplacement 0.
const MAX_PLAYERS = 8;
function teamCount(r, team) {
  return [...r.players.values()].filter((q) => q.team === team).length;
}

// Remet les emplacements en ordre (0,1,2…) dans chaque équipe, dans l'ordre d'arrivée.
// En Battle Royale, ce sont les numéros d'équipe qui sont resserrés (0,1,2…).
function compactSlots(r) {
  if (r.mode === "br") {
    const list = [...r.players.values()].sort((a, b) => a.team - b.team);
    list.forEach((p, i) => { p.team = i; p.slot = 0; });
    return;
  }
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
  } else if (r.phase === "draft") {
    // départ pendant la draft : sans IA, tout le monde revient au salon
    r.phase = "lobby";
    compactSlots(r);
    broadcast(r, { t: "left", id: p.id, name: p.name, team: p.team, slot: p.slot });
  } else {
    broadcast(r, { t: "left", id: p.id, name: p.name, team: p.team, slot: p.slot });
  }
  if (r.host === p.id) {
    r.host = [...r.players.keys()][0];
  }
  pushRoom(r);
}

// ------------------------------------------------------------------ recherche de partie (files 1v1…4v4)
// Une file par taille d'équipe ET par version du jeu (on ne mélange pas les versions).
// Dès qu'une file contient 2×taille joueurs, une « partie trouvée » est proposée : chacun a
// ACCEPT_MS pour accepter. Si tout le monde accepte, le serveur crée un salon normal (équipes
// réparties) et passe directement à la draft. Sinon, ceux qui ont refusé / pas répondu sortent
// de la file et les autres y retournent en tête. Aucune IA : uniquement de vrais joueurs.
const clients = new Set();   // tous les joueurs connectés
const queues = new Map();    // "version|taille" -> [joueurs] (ordre d'arrivée)
const matches = new Map();   // id -> partie proposée en attente d'acceptation
let nextMatch = 1;
const QSIZES = [1, 2, 3, 4];

function qkey(ver, size) { return ver + "|" + size; }
function qlist(key) { if (!queues.has(key)) queues.set(key, []); return queues.get(key); }

function queueCounts(ver) {
  const c = QSIZES.map((s) => qlist(qkey(ver, s)).length);
  for (const m of matches.values()) if (m.ver === ver) c[m.size - 1] += m.players.length;
  return c;
}
// envoie le nombre de joueurs en recherche à tous ceux de cette version qui ne sont pas dans un salon
function pushCounts(ver) {
  const c = queueCounts(ver);
  for (const q of clients) if (q.ver === ver && !q.room && q.proto >= 5) q.sock.send({ t: "qcount", c });
}
function sendQueue(p) {
  p.sock.send(p.queue ? { t: "queue", size: p.qsize, el: Date.now() - p.qsince } : { t: "queue", size: 0 });
}

function enqueue(p, size, head) {
  const key = qkey(p.ver, size);
  const q = qlist(key);
  if (head) q.unshift(p); else q.push(p);
  p.queue = key; p.qsize = size;
  if (!head) p.qsince = Date.now();
  sendQueue(p);
}

function dequeue(p, notify) {
  if (!p.queue) return false;
  const q = qlist(p.queue);
  const i = q.indexOf(p);
  if (i >= 0) q.splice(i, 1);
  p.queue = null;
  if (notify) sendQueue(p);
  return true;
}

function tryMatch(ver, size) {
  const q = qlist(qkey(ver, size));
  while (q.length >= size * 2) {
    const group = q.splice(0, size * 2);
    const m = { id: nextMatch++, ver, size, players: group, acc: new Set(), timer: null };
    matches.set(m.id, m);
    for (const p of group) {
      p.queue = null; p.match = m;
      p.sock.send({ t: "match", id: m.id, size, n: group.length, ms: ACCEPT_MS });
    }
    m.timer = setTimeout(() => {
      // délai écoulé : ceux qui n'ont pas accepté sortent de la file
      cancelMatch(m, m.players.filter((p) => !m.acc.has(p.id)), "timeout");
    }, ACCEPT_MS + 400);
  }
}

// annule une partie proposée : `out` quittent la recherche, les autres retournent en tête de file
function cancelMatch(m, out, reason) {
  if (!matches.has(m.id)) return;
  matches.delete(m.id);
  clearTimeout(m.timer);
  const outSet = new Set(out);
  const back = m.players.filter((p) => !outSet.has(p) && p.sock.open);
  // ceux qui avaient accepté passent devant ceux qui n'avaient pas encore répondu
  back.sort((a, b) => (m.acc.has(b.id) ? 1 : 0) - (m.acc.has(a.id) ? 1 : 0));
  for (const p of m.players) p.match = null;
  for (const p of out) if (p.sock.open) p.sock.send({ t: "match_cancel", requeued: false, reason });
  for (let i = back.length - 1; i >= 0; i--) {
    const p = back[i];
    p.sock.send({ t: "match_cancel", requeued: true, reason });
    enqueue(p, m.size, true);
  }
  tryMatch(m.ver, m.size);
  pushCounts(m.ver);
}

function acceptMatch(p) {
  const m = p.match;
  if (!m || m.acc.has(p.id)) return;
  m.acc.add(p.id);
  for (const q of m.players) q.sock.send({ t: "match_acc", id: m.id, acc: m.acc.size, n: m.players.length });
  if (m.acc.size >= m.players.length) launchMatch(m);
}

// tout le monde a accepté : salon normal (comme une partie perso), équipes réparties, puis draft
function launchMatch(m) {
  matches.delete(m.id);
  clearTimeout(m.timer);
  if (rooms.size >= MAX_ROOMS) {
    for (const p of m.players) p.match = null;
    for (const p of m.players) { p.sock.send({ t: "error", msg: "Serveur plein, réessayez plus tard." }); p.sock.send({ t: "match_cancel", requeued: false, reason: "full" }); }
    pushCounts(m.ver);
    return;
  }
  const code = newCode();
  const room = { code, host: m.players[0].id, size: MAX_PLAYERS, diff: 1, phase: "lobby", ver: m.ver, players: new Map(), game: null, mode: "classic", mm: true, qsize: m.size };
  rooms.set(code, room);
  m.players.forEach((p, i) => {
    p.match = null;
    if (p.room) leaveRoom(p);
    p.room = room; p.team = i % 2; p.slot = Math.floor(i / 2);
    room.players.set(p.id, p);
  });
  compactSlots(room);
  room.phase = "draft";
  pushRoom(room);
  pushCounts(m.ver);
}

// le joueur quitte toute recherche (file ou partie proposée = refus)
function leaveSearch(p, reason) {
  if (p.match) cancelMatch(p.match, [p], reason);
  else if (dequeue(p, true)) pushCounts(p.ver);
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
      p.proto = Number(m.proto) || 4;
      p.sock.send({ t: "welcome", id: p.id, proto: PROTO });
      if (p.proto >= 5) p.sock.send({ t: "qcount", c: queueCounts(p.ver) });
      break;
    case "queue": {
      // entrer dans la file d'un mode (1v1…4v4) ; une seule file à la fois
      const size = clamp(m.size, 1, 4, 1);
      if (r) { p.sock.send({ t: "error", msg: "Quittez le salon avant de rechercher une partie." }); sendQueue(p); return; }
      if (p.match) return;
      if (p.queue === qkey(p.ver, size)) { sendQueue(p); return; }
      dequeue(p, false);
      enqueue(p, size, false);
      tryMatch(p.ver, size);
      pushCounts(p.ver);
      break;
    }
    case "unqueue":
      leaveSearch(p, "declined");
      break;
    case "accept":
      acceptMatch(p);
      break;
    case "decline":
      if (p.match) cancelMatch(p.match, [p], "declined");
      break;
    case "create": {
      leaveSearch(p, "declined");
      if (r) leaveRoom(p);
      if (rooms.size >= MAX_ROOMS) { p.sock.send({ t: "error", msg: "Serveur plein, réessayez plus tard." }); return; }
      const code = newCode();
      const room = { code, host: p.id, size: MAX_PLAYERS, diff: 1, phase: "lobby", ver: p.ver, players: new Map(), game: null, mode: m.mode === "br" ? "br" : "classic" };
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
      if (room.players.size >= MAX_PLAYERS) { p.sock.send({ t: "error", msg: "Salon complet." }); return; }
      if (room.mm) { p.sock.send({ t: "error", msg: "Ce salon vient de la recherche de partie : impossible de le rejoindre." }); return; }
      leaveSearch(p, "declined");
      if (r) leaveRoom(p);
      if (room.mode === "br") {
        p.team = room.players.size; p.slot = 0;
      } else {
        // on rejoint le camp le moins rempli (chacun peut ensuite changer de camp)
        const n0 = teamCount(room, 0), n1 = teamCount(room, 1);
        p.team = n1 < n0 ? 1 : 0;
        p.slot = teamCount(room, p.team);
      }
      p.room = room;
      room.players.set(p.id, p);
      compactSlots(room);
      pushRoom(room);
      break;
    }
    case "leave":
      leaveRoom(p);
      p.sock.send({ t: "left_room" });
      if (p.proto >= 5) { p.sock.send({ t: "qcount", c: queueCounts(p.ver) }); sendQueue(p); }
      break;
    case "set":
      if (!r || r.host !== p.id || r.phase !== "lobby") return;
      if (m.diff !== undefined) r.diff = clamp(m.diff, 0, 2, r.diff);
      pushRoom(r);
      break;
    case "team": {
      if (!r || r.phase !== "lobby" || r.mode === "br") return;
      const team = m.team === 1 ? 1 : 0;
      if (team === p.team) return;
      p.team = team; p.slot = 99;
      compactSlots(r);
      pushRoom(r);
      break;
    }
    case "phase":
      if (!r || r.host !== p.id) return;
      if (m.phase === "lobby") { stopGame(r); r.phase = "lobby"; r.game = null; }
      else if (m.phase === "draft") {
        if (r.phase !== "lobby") return;
        // il faut au moins un joueur dans chaque camp (Arène) ou deux joueurs (Battle Royale)
        const ok = r.mode === "br" ? r.players.size >= 2 : teamCount(r, 0) >= 1 && teamCount(r, 1) >= 1;
        if (!ok) { p.sock.send({ t: "error", msg: r.mode === "br" ? "Il faut au moins 2 joueurs." : "Il faut au moins un joueur dans chaque équipe." }); return; }
        compactSlots(r);
        r.phase = "draft";
      }
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
  let nq = 0;
  for (const q of queues.values()) nq += q.length;
  res.end("Arena of Clodo — serveur multijoueur OK. Salons actifs : " + rooms.size + " · en recherche : " + nq + "\n");
});

server.on("upgrade", (req, socket) => {
  const key = req.headers["sec-websocket-key"];
  if (!key || (req.headers.upgrade || "").toLowerCase() !== "websocket") { socket.destroy(); return; }
  const accept = crypto.createHash("sha1").update(key + GUID).digest("base64");
  socket.write("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: " + accept + "\r\n\r\n");
  const p = { id: nextId++, name: "Gladiateur", ver: "", proto: 4, room: null, team: 0, slot: 0, queue: null, qsize: 0, qsince: 0, match: null, sock: new Sock(socket) };
  clients.add(p);
  p.sock.onmessage = (msg) => { try { handle(p, msg); } catch (e) { console.error(e); } };
  p.sock.onclose = () => {
    clients.delete(p);
    try { leaveSearch(p, "left"); } catch (e) { console.error(e); }
    leaveRoom(p);
  };
});

// garde les connexions en vie derrière les hébergeurs (ping toutes les 25 s)
setInterval(() => {
  for (const p of clients) p.sock._send(0x9, Buffer.alloc(0));
}, 25000);

server.listen(PORT, () => console.log("Serveur Arena of Clodo à l'écoute sur le port " + PORT));
