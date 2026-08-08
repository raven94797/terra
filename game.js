'use strict';
/* =========================================================
 * 泰拉瑞亚 · Web Edition  —— 地表世界
 * 世界生成 / 物理 / 挖掘放置 / 昼夜循环 / 视差背景
 * ========================================================= */

// ---------------- 工具 ----------------
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function makeNoise(seed) {
  const rand = mulberry32(seed);
  const perm = new Uint8Array(512);
  const p = new Uint8Array(256);
  for (let i = 0; i < 256; i++) p[i] = i;
  for (let i = 255; i > 0; i--) {
    const j = (rand() * (i + 1)) | 0;
    const t = p[i]; p[i] = p[j]; p[j] = t;
  }
  for (let i = 0; i < 512; i++) perm[i] = p[i & 255];
  const fade = t => t * t * (3 - 2 * t);
  function noise1(x) {
    const xi = Math.floor(x) & 255, xf = x - Math.floor(x);
    const u = fade(xf);
    return perm[xi] / 255 + (perm[xi + 1] / 255 - perm[xi] / 255) * u;
  }
  function noise2(x, y) {
    const xi = Math.floor(x) & 255, yi = Math.floor(y) & 255;
    const xf = x - Math.floor(x), yf = y - Math.floor(y);
    const u = fade(xf), v = fade(yf);
    const aa = perm[(perm[xi] + yi) & 255] / 255;
    const ba = perm[(perm[xi + 1] + yi) & 255] / 255;
    const ab = perm[(perm[xi] + yi + 1) & 255] / 255;
    const bb = perm[(perm[xi + 1] + yi + 1) & 255] / 255;
    return aa + (ba - aa) * u + (ab - aa) * v + (aa - ba - ab + bb) * u * v;
  }
  return { noise1, noise2 };
}

const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const lerp = (a, b, t) => a + (b - a) * t;

// ---------------- 配置 ----------------
const TILE = 40;
const WORLD_W = 600, WORLD_H = 160;
const SURFACE_Y = 42;
const DAY_LENGTH = 240;

const T = { AIR: 0, GRASS: 1, DIRT: 2, STONE: 3, WOOD: 4, LEAVES: 5, SAND: 6 };
const TILE_DEF = {
  [T.GRASS]:  { key: 'grass',  name: '草方块', hard: 0.45, img: 'assets/tiles/grass.png',  cropTop: 0.10 },
  [T.DIRT]:   { key: 'dirt',   name: '泥土',   hard: 0.40, img: 'assets/tiles/dirt.png' },
  [T.STONE]:  { key: 'stone',  name: '石头',   hard: 1.05, img: 'assets/tiles/stone.png' },
  [T.WOOD]:   { key: 'wood',   name: '木材',   hard: 0.70, img: 'assets/tiles/wood.png' },
  [T.LEAVES]: { key: 'leaves', name: '树叶',   hard: 0.18, img: 'assets/tiles/leaves.png' },
  [T.SAND]:   { key: 'sand',   name: '沙子',   hard: 0.40, img: 'assets/tiles/sand.png' },
};
const HOTBAR_ORDER = [T.GRASS, T.DIRT, T.STONE, T.WOOD, T.LEAVES, T.SAND];

// ---------------- 全局状态 ----------------
const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');
let VW = 0, VH = 0;
function resize() {
  VW = canvas.width = window.innerWidth;
  VH = canvas.height = window.innerHeight;
}
window.addEventListener('resize', resize);
resize();

const world = new Uint8Array(WORLD_W * WORLD_H);
const surfaceH = new Int16Array(WORLD_W);
const tex = {};
const sprites = {};
const inv = {};
HOTBAR_ORDER.forEach(t => inv[t] = 0);
inv[T.DIRT] = 30; inv[T.WOOD] = 20; inv[T.STONE] = 20; inv[T.SAND] = 10; inv[T.GRASS] = 10; inv[T.LEAVES] = 10;

let selSlot = 0;
let timeOfDay = 0.32;
const cam = { x: 0, y: 0 };
const particles = [];
const clouds = [];
const stars = [];
let noise, noiseB;
let helpVisible = true;
let ready = false;

// ---------------- 战斗 / 生命 ----------------
let hp = 100, maxHp = 100;
let invuln = 0;
let dead = false, deadTimer = 0;
let gel = 0;
let shake = 0;
let swordCd = 0, swordAnim = 0;
const swordDir = { x: 1, y: 0 };
const SWORD_RANGE = TILE * 3.2;
const SWORD_ARC = 1.25;
const SWORD_DMG = 18;
const slimes = [];
let slimeSpawnTimer = 1.5;
const MAX_SLIMES = 8;
let spawnX = 0, spawnY = 0;

// ---------------- 资源加载 ----------------
function loadImage(src) {
  // 通过 fetch + blob URL 加载图片，保证与页面同源，
  // 避免 getImageData 时画布被跨域污染（CORS / file://）。
  return fetch(src)
    .then(r => {
      if (!r.ok) throw new Error('HTTP ' + r.status + ' @ ' + src);
      return r.blob();
    })
    .then(blob => new Promise((res, rej) => {
      const url = URL.createObjectURL(blob);
      const im = new Image();
      im.onload = () => { URL.revokeObjectURL(url); res(im); };
      im.onerror = () => { URL.revokeObjectURL(url); rej(new Error('load fail: ' + src)); };
      im.src = url;
    }));
}

function makeTile(img, cropTop = 0) {
  const S = 64, c = document.createElement('canvas');
  c.width = c.height = S * 2;
  const g = c.getContext('2d');
  g.imageSmoothingEnabled = true;
  const sy = img.height * cropTop, sh = img.height - sy;
  g.drawImage(img, 0, sy, img.width, sh, 0, 0, S, S);
  g.save(); g.translate(S * 2, 0); g.scale(-1, 1);
  g.drawImage(img, 0, sy, img.width, sh, 0, 0, S, S); g.restore();
  g.save(); g.translate(0, S * 2); g.scale(1, -1);
  g.drawImage(img, 0, sy, img.width, sh, 0, 0, S, S); g.restore();
  g.save(); g.translate(S * 2, S * 2); g.scale(-1, -1);
  g.drawImage(img, 0, sy, img.width, sh, 0, 0, S, S); g.restore();
  return c;
}

function removeWhiteBG(img, threshold = 232) {
  const w = img.width, h = img.height;
  const c = document.createElement('canvas');
  c.width = w; c.height = h;
  const g = c.getContext('2d');
  g.drawImage(img, 0, 0);
  const id = g.getImageData(0, 0, w, h);
  const d = id.data;
  const visited = new Uint8Array(w * h);
  const stack = [];
  const isWhite = i => d[i * 4] >= threshold && d[i * 4 + 1] >= threshold && d[i * 4 + 2] >= threshold;
  for (let x = 0; x < w; x++) {
    if (isWhite(x)) stack.push(x);
    const bi = (h - 1) * w + x;
    if (isWhite(bi)) stack.push(bi);
  }
  for (let y = 0; y < h; y++) {
    const li = y * w;
    if (isWhite(li)) stack.push(li);
    const ri = y * w + w - 1;
    if (isWhite(ri)) stack.push(ri);
  }
  while (stack.length) {
    const i = stack.pop();
    if (visited[i] || !isWhite(i)) continue;
    visited[i] = 1;
    d[i * 4 + 3] = 0;
    const x = i % w, y = (i / w) | 0;
    if (x > 0) stack.push(i - 1);
    if (x < w - 1) stack.push(i + 1);
    if (y > 0) stack.push(i - w);
    if (y < h - 1) stack.push(i + w);
  }
  g.putImageData(id, 0, 0);
  let minX = w, minY = h, maxX = -1, maxY = -1;
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (d[(y * w + x) * 4 + 3] > 8) {
        if (x < minX) minX = x;
        if (x > maxX) maxX = x;
        if (y < minY) minY = y;
        if (y > maxY) maxY = y;
      }
    }
  }
  if (maxX < 0) return c;
  const cw = maxX - minX + 1, ch = maxY - minY + 1;
  const out = document.createElement('canvas');
  out.width = cw; out.height = ch;
  out.getContext('2d').drawImage(c, minX, minY, cw, ch, 0, 0, cw, ch);
  return out;
}

// ---------------- 世界生成 ----------------
function idx(tx, ty) { return ty * WORLD_W + tx; }
function getTile(tx, ty) {
  if (tx < 0 || tx >= WORLD_W) return T.STONE;
  if (ty < 0) return T.AIR;
  if (ty >= WORLD_H) return T.STONE;
  return world[idx(tx, ty)];
}
function setTile(tx, ty, v) {
  if (tx < 0 || tx >= WORLD_W || ty < 0 || ty >= WORLD_H) return;
  world[idx(tx, ty)] = v;
}
function isSolidType(v) { return v !== T.AIR; }

function genWorld() {
  noise = makeNoise(1337);
  noiseB = makeNoise(8866);

  for (let x = 0; x < WORLD_W; x++) {
    const base = noise.noise1(x * 0.008) * 14;
    const hills = noise.noise1(x * 0.035 + 100) * 7;
    const detail = noise.noise1(x * 0.13 + 300) * 2;
    surfaceH[x] = Math.round(SURFACE_Y + base + hills + detail - 10);
  }

  for (let x = 0; x < WORLD_W; x++) {
    const desert = noiseB.noise1(x * 0.006 + 50) > 0.62;
    const dirtDepth = 4 + ((noise.noise1(x * 0.09 + 77) * 3) | 0);
    for (let y = surfaceH[x]; y < WORLD_H; y++) {
      const depth = y - surfaceH[x];
      if (depth === 0) setTile(x, y, desert ? T.SAND : T.GRASS);
      else if (depth <= (desert ? dirtDepth + 2 : dirtDepth)) setTile(x, y, desert ? T.SAND : T.DIRT);
      else setTile(x, y, T.STONE);
    }
  }

  for (let x = 2; x < WORLD_W - 2; x++) {
    for (let y = surfaceH[x] + 6; y < WORLD_H - 4; y++) {
      const n = noise.noise2(x * 0.075, y * 0.075);
      const n2 = noiseB.noise2(x * 0.05 + 40, y * 0.05);
      if (n > 0.74 || (n2 > 0.78 && n > 0.62)) setTile(x, y, T.AIR);
    }
  }

  const spawnTX = WORLD_W >> 1;
  let lastTree = -10;
  for (let x = 8; x < WORLD_W - 8; x++) {
    if (Math.abs(x - spawnTX) < 10) continue;
    if (x - lastTree < 7) continue;
    if (getTile(x, surfaceH[x]) !== T.GRASS) continue;
    if (Math.abs(surfaceH[x - 1] - surfaceH[x]) > 1 || Math.abs(surfaceH[x + 1] - surfaceH[x]) > 1) continue;
    if (noiseB.noise1(x * 0.21 + 9) < 0.56) continue;
    growTree(x, surfaceH[x] - 1);
    lastTree = x;
  }

  const target = surfaceH[spawnTX];
  for (let x = spawnTX - 5; x <= spawnTX + 5; x++) {
    if (surfaceH[x] > target) {
      for (let y = target; y < surfaceH[x]; y++) setTile(x, y, T.AIR);
      surfaceH[x] = target;
      setTile(x, target, T.GRASS);
    }
  }
}

function growTree(tx, groundY) {
  const rand = mulberry32(tx * 31 + 7);
  const h = 5 + ((rand() * 4) | 0);
  for (let i = 0; i < h; i++) setTile(tx, groundY - i, T.WOOD);
  const topY = groundY - h;
  const r = 2 + ((rand() * 2) | 0);
  for (let dy = -r; dy <= r; dy++) {
    for (let dx = -r; dx <= r; dx++) {
      const dist = Math.sqrt(dx * dx + dy * dy * 1.4);
      if (dist <= r + 0.4) {
        const x = tx + dx, y = topY + dy;
        const cur = getTile(x, y);
        if ((cur === T.AIR || cur === T.WOOD) && !(dx === 0 && dy > 0)) setTile(x, y, T.LEAVES);
      }
    }
  }
  setTile(tx, topY, T.WOOD);
  if (rand() < 0.5) setTile(tx, topY + 1, T.WOOD);
}

// ---------------- 音效 ----------------
let AC = null;
function audio() {
  if (!AC) AC = new (window.AudioContext || window.webkitAudioContext)();
  if (AC.state === 'suspended') AC.resume();
  return AC;
}
function sfxDig() {
  try {
    const ac = audio();
    const buf = ac.createBuffer(1, ac.sampleRate * 0.06, ac.sampleRate);
    const ch = buf.getChannelData(0);
    for (let i = 0; i < ch.length; i++) ch[i] = (Math.random() * 2 - 1) * (1 - i / ch.length);
    const src = ac.createBufferSource(); src.buffer = buf;
    const f = ac.createBiquadFilter(); f.type = 'highpass'; f.frequency.value = 900;
    const g = ac.createGain(); g.gain.value = 0.18;
    src.connect(f); f.connect(g); g.connect(ac.destination); src.start();
  } catch (e) { }
}
function sfxPlace() {
  try {
    const ac = audio();
    const o = ac.createOscillator(); o.type = 'sine';
    o.frequency.setValueAtTime(160, ac.currentTime);
    o.frequency.exponentialRampToValueAtTime(70, ac.currentTime + 0.09);
    const g = ac.createGain();
    g.gain.setValueAtTime(0.25, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + 0.1);
    o.connect(g); g.connect(ac.destination);
    o.start(); o.stop(ac.currentTime + 0.11);
  } catch (e) { }
}
function sfxJump() {
  try {
    const ac = audio();
    const o = ac.createOscillator(); o.type = 'square';
    o.frequency.setValueAtTime(220, ac.currentTime);
    o.frequency.exponentialRampToValueAtTime(440, ac.currentTime + 0.1);
    const g = ac.createGain();
    g.gain.setValueAtTime(0.06, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + 0.12);
    o.connect(g); g.connect(ac.destination);
    o.start(); o.stop(ac.currentTime + 0.13);
  } catch (e) { }
}
function sfxHurt() {
  try {
    const ac = audio();
    const o = ac.createOscillator(); o.type = 'sawtooth';
    o.frequency.setValueAtTime(320, ac.currentTime);
    o.frequency.exponentialRampToValueAtTime(80, ac.currentTime + 0.18);
    const g = ac.createGain();
    g.gain.setValueAtTime(0.22, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + 0.2);
    o.connect(g); g.connect(ac.destination);
    o.start(); o.stop(ac.currentTime + 0.21);
  } catch (e) { }
}
function sfxSlimeHit() {
  try {
    const ac = audio();
    const o = ac.createOscillator(); o.type = 'triangle';
    o.frequency.setValueAtTime(520, ac.currentTime);
    o.frequency.exponentialRampToValueAtTime(160, ac.currentTime + 0.08);
    const g = ac.createGain();
    g.gain.setValueAtTime(0.16, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + 0.09);
    o.connect(g); g.connect(ac.destination);
    o.start(); o.stop(ac.currentTime + 0.1);
  } catch (e) { }
}
function sfxSlimeDie() {
  try {
    const ac = audio();
    const o = ac.createOscillator(); o.type = 'square';
    o.frequency.setValueAtTime(240, ac.currentTime);
    o.frequency.exponentialRampToValueAtTime(70, ac.currentTime + 0.12);
    const g = ac.createGain();
    g.gain.setValueAtTime(0.12, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + 0.13);
    o.connect(g); g.connect(ac.destination);
    o.start(); o.stop(ac.currentTime + 0.14);
  } catch (e) { }
}

// ---------------- 物理 ----------------
const GRAV = 0.55, MAX_FALL = 14;

function rectHitsSolid(x, y, w, h) {
  const x0 = Math.floor(x / TILE), x1 = Math.floor((x + w - 0.01) / TILE);
  const y0 = Math.floor(y / TILE), y1 = Math.floor((y + h - 0.01) / TILE);
  for (let ty = y0; ty <= y1; ty++)
    for (let tx = x0; tx <= x1; tx++)
      if (isSolidType(getTile(tx, ty))) return true;
  return false;
}

class Entity {
  constructor(x, y, w, h) {
    this.x = x; this.y = y; this.w = w; this.h = h;
    this.vx = 0; this.vy = 0;
    this.onGround = false;
    this.face = 1;
    this.walkPhase = 0;
  }
  moveX(dx) {
    this.x += dx;
    const x0 = Math.floor(this.x / TILE), x1 = Math.floor((this.x + this.w - 0.01) / TILE);
    const y0 = Math.floor(this.y / TILE), y1 = Math.floor((this.y + this.h - 0.01) / TILE);
    for (let ty = y0; ty <= y1; ty++) {
      for (let tx = x0; tx <= x1; tx++) {
        if (isSolidType(getTile(tx, ty))) {
          if (dx > 0) this.x = tx * TILE - this.w - 0.01;
          else if (dx < 0) this.x = (tx + 1) * TILE + 0.01;
          this.vx = 0;
          return true;
        }
      }
    }
    return false;
  }
  moveY(dy) {
    this.y += dy;
    const x0 = Math.floor(this.x / TILE), x1 = Math.floor((this.x + this.w - 0.01) / TILE);
    const y0 = Math.floor(this.y / TILE), y1 = Math.floor((this.y + this.h - 0.01) / TILE);
    for (let ty = y0; ty <= y1; ty++) {
      for (let tx = x0; tx <= x1; tx++) {
        if (isSolidType(getTile(tx, ty))) {
          if (dy > 0) { this.y = ty * TILE - this.h - 0.01; this.onGround = true; }
          else if (dy < 0) this.y = (ty + 1) * TILE + 0.01;
          this.vy = 0;
          return true;
        }
      }
    }
    return false;
  }
  physics() {
    this.vy = Math.min(this.vy + GRAV, MAX_FALL);
    this.moveX(this.vx);
    this.onGround = false;
    this.moveY(this.vy);
    if (!this.onGround && rectHitsSolid(this.x, this.y + 1.5, this.w, this.h) && this.vy >= 0) {
      this.onGround = true;
    }
  }
  get cx() { return this.x + this.w / 2; }
  get cy() { return this.y + this.h / 2; }
}

// ---------------- 玩家 ----------------
const player = new Entity(0, 0, 26, 92);
const P_SPEED = 4.4, P_JUMP = -13.6;

function updatePlayer(dt) {
  if (dead) {
    player.vx = lerp(player.vx, 0, 0.2);
    player.physics();
    return;
  }
  const left = keys['a'] || keys['arrowleft'];
  const right = keys['d'] || keys['arrowright'];
  const jump = keys['w'] || keys[' '] || keys['arrowup'];

  let target = 0;
  if (left) { target = -P_SPEED; player.face = -1; }
  if (right) { target = P_SPEED; player.face = 1; }
  player.vx = lerp(player.vx, target, player.onGround ? 0.35 : 0.18);
  if (Math.abs(player.vx) < 0.05) player.vx = 0;

  if (jump && player.onGround && !player.jumpHeld) {
    player.vy = P_JUMP;
    player.jumpHeld = true;
    sfxJump();
  }
  if (!jump) {
    player.jumpHeld = false;
    if (player.vy < P_JUMP * 0.4) player.vy = P_JUMP * 0.4;
  }

  player.physics();
  if (Math.abs(player.vx) > 0.5 && player.onGround) player.walkPhase += dt * 10;
  else player.walkPhase *= 0.8;
}

// ---------------- 向导 NPC ----------------
const guide = new Entity(0, 0, 26, 92);
guide.ai = { state: 'idle', timer: 2, dir: 1 };

function updateGuide(dt) {
  const ai = guide.ai;
  ai.timer -= dt;
  const distP = player.cx - guide.cx;

  if (Math.abs(distP) < TILE * 3.5) {
    guide.face = distP > 0 ? 1 : -1;
    guide.vx = lerp(guide.vx, 0, 0.3);
  } else {
    if (ai.timer <= 0) {
      if (ai.state === 'idle') {
        ai.state = 'walk';
        ai.dir = Math.random() < 0.5 ? -1 : 1;
        ai.timer = 1.5 + Math.random() * 3;
      } else {
        ai.state = 'idle';
        ai.timer = 1 + Math.random() * 2.5;
      }
    }
    if (ai.state === 'walk') {
      guide.face = ai.dir;
      guide.vx = lerp(guide.vx, ai.dir * 1.6, 0.2);
      const aheadX = ai.dir > 0 ? guide.x + guide.w + 2 : guide.x - 2;
      const wallAhead = isSolidType(getTile(Math.floor(aheadX / TILE), Math.floor((guide.y + guide.h - 6) / TILE)));
      const groundAhead = isSolidType(getTile(Math.floor(aheadX / TILE), Math.floor((guide.y + guide.h + TILE * 0.7) / TILE)));
      if (wallAhead && guide.onGround) guide.vy = P_JUMP * 0.85;
      if (!groundAhead && guide.onGround) { ai.dir *= -1; ai.timer = 1 + Math.random() * 2; }
    } else {
      guide.vx = lerp(guide.vx, 0, 0.3);
    }
  }

  guide.physics();
  if (Math.abs(guide.vx) > 0.3 && guide.onGround) guide.walkPhase += dt * 7;
  else guide.walkPhase *= 0.8;
}

// ---------------- 史莱姆敌人 ----------------
class Slime extends Entity {
  constructor(cx, bottomY, big) {
    const w = big ? 44 : 28;
    const h = big ? 30 : 20;
    super(cx - w / 2, bottomY - h, w, h);
    this.big = big;
    this.maxHp = big ? 40 : 15;
    this.hp = this.maxHp;
    this.jump = big ? 9.5 : 8;
    this.speed = big ? 1.7 : 2.1;
    this.timer = 0.5 + Math.random() * 1.2;
    this.dir = Math.random() < 0.5 ? -1 : 1;
    this.flash = 0;
    this.phase = Math.random() * 6.28;
  }
}

function overlap(a, b) {
  return a.x < b.x + b.w && a.x + a.w > b.x && a.y < b.y + b.h && a.y + a.h > b.y;
}

function spawnSlime(cx, bottomY, big) {
  const s = new Slime(cx, bottomY, big);
  slimes.push(s);
}

function trySpawnSlime() {
  for (let attempt = 0; attempt < 6; attempt++) {
    const dir = Math.random() < 0.5 ? -1 : 1;
    const distTiles = 18 + Math.random() * 26;
    const tx = clamp(Math.round(player.cx / TILE + dir * distTiles), 6, WORLD_W - 6);
    let gy = surfaceH[tx];
    while (gy < WORLD_H && !isSolidType(getTile(tx, gy))) gy++;
    if (gy >= WORLD_H) continue;
    if (Math.abs(tx * TILE - player.cx) < TILE * 10) continue;
    const w = 44, h = 30, x = tx * TILE + TILE / 2, y = gy * TILE;
    if (rectHitsSolid(x - w / 2, y - h, w, h)) continue;
    spawnSlime(x, y, Math.random() < 0.3);
    return;
  }
}

function updateSlimes(dt) {
  slimeSpawnTimer -= dt;
  if (slimeSpawnTimer <= 0 && slimes.length < MAX_SLIMES && !dead) {
    trySpawnSlime();
    slimeSpawnTimer = 3.5 + Math.random() * 5;
  }
  for (let i = slimes.length - 1; i >= 0; i--) {
    const s = slimes[i];
    s.flash = Math.max(0, s.flash - dt);
    s.phase += dt * 7;
    s.timer -= dt;
    const dx = player.cx - s.cx;
    if (s.onGround && s.timer <= 0 && Math.abs(dx) < TILE * 50) {
      s.dir = dx > 0 ? 1 : -1;
      s.vy = -s.jump;
      s.vx = s.dir * s.speed;
      s.timer = 0.9 + Math.random() * 1.5;
    } else if (!s.onGround) {
      s.vx = lerp(s.vx, 0, 0.015);
    }
    s.physics();
    if (Math.abs(s.vx) < 0.1 && !s.onGround) {
      s.dir *= -1;
      s.vx = s.dir * s.speed;
    }
    if (overlap(s, player) && invuln <= 0 && !dead) {
      hurtPlayer(12, dx > 0 ? 5 : -5);
    }
    if (s.y > WORLD_H * TILE + 100) slimes.splice(i, 1);
  }
}

function slimeHit(s, dmg, dx, dy) {
  s.hp -= dmg;
  s.flash = 0.14;
  s.vx = dx * 4.5;
  s.vy = -6;
  s.timer = 0.35;
  if (s.hp <= 0) slimeDie(s);
}

function slimeDie(s) {
  const i = slimes.indexOf(s);
  if (i >= 0) slimes.splice(i, 1);
  spawnSlimeParticles(s);
  gel += s.big ? 2 : 1;
  sfxSlimeDie();
  if (s.big) {
    spawnSlime(s.cx, s.y + s.h, false);
    spawnSlime(s.cx + 6, s.y + s.h, false);
  }
}

function spawnSlimeParticles(s) {
  const col = s.big ? '#6bd13d' : '#4ab32d';
  for (let i = 0; i < 14; i++) {
    particles.push({
      x: s.cx + (Math.random() - 0.5) * s.w,
      y: s.cy + (Math.random() - 0.5) * s.h,
      vx: (Math.random() - 0.5) * 7,
      vy: -Math.random() * 6 - 1,
      life: 0.45 + Math.random() * 0.4,
      t: 0,
      color: col,
      size: 4 + Math.random() * 5,
      spin: 0, rot: 0, rect: true,
    });
  }
}

// ---------------- 输入 ----------------
const keys = {};
const mouse = { x: 0, y: 0, left: false, right: false };

window.addEventListener('keydown', e => {
  const k = e.key.toLowerCase();
  keys[k] = true;
  if (k === ' ') e.preventDefault();
  if (k === 'h') {
    helpVisible = !helpVisible;
    document.getElementById('help').style.display = helpVisible ? 'block' : 'none';
  }
  const n = parseInt(k, 10);
  if (n >= 1 && n <= HOTBAR_ORDER.length) selSlot = n - 1;
});
window.addEventListener('keyup', e => { keys[e.key.toLowerCase()] = false; });
canvas.addEventListener('contextmenu', e => e.preventDefault());
canvas.addEventListener('mousedown', e => {
  if (e.button === 0) mouse.left = true;
  if (e.button === 2) mouse.right = true;
});
window.addEventListener('mouseup', e => {
  if (e.button === 0) mouse.left = false;
  if (e.button === 2) mouse.right = false;
});
window.addEventListener('mousemove', e => { mouse.x = e.clientX; mouse.y = e.clientY; });
window.addEventListener('wheel', e => {
  selSlot = (selSlot + (e.deltaY > 0 ? 1 : -1) + HOTBAR_ORDER.length) % HOTBAR_ORDER.length;
}, { passive: true });

// ---------------- 挖掘 / 放置 ----------------
const REACH = 5.5 * TILE;
const mining = { tx: -1, ty: -1, progress: 0 };
let placeCooldown = 0;

function mouseTile() {
  const wx = mouse.x + cam.x, wy = mouse.y + cam.y;
  return { tx: Math.floor(wx / TILE), ty: Math.floor(wy / TILE), wx, wy };
}

function inReach(tx, ty) {
  const cx = (tx + 0.5) * TILE, cy = (ty + 0.5) * TILE;
  const dx = cx - player.cx, dy = cy - (player.y + player.h * 0.45);
  return dx * dx + dy * dy <= REACH * REACH;
}

function spawnBreakParticles(tx, ty, type) {
  const src = tex[type];
  if (!src) return;
  for (let i = 0; i < 9; i++) {
    const sx = ((Math.random() * 3) | 0) * 16 + ((Math.random() < 0.5) ? 64 : 0);
    const sy = ((Math.random() * 3) | 0) * 16 + ((Math.random() < 0.5) ? 64 : 0);
    particles.push({
      x: tx * TILE + TILE / 2 + (Math.random() - 0.5) * TILE * 0.6,
      y: ty * TILE + TILE / 2 + (Math.random() - 0.5) * TILE * 0.6,
      vx: (Math.random() - 0.5) * 5,
      vy: -Math.random() * 5 - 1,
      life: 0.55 + Math.random() * 0.4,
      t: 0,
      src, sx, sy, size: 9 + Math.random() * 5,
      spin: (Math.random() - 0.5) * 0.3,
      rot: Math.random() * 6.28,
    });
  }
}

function updateMining(dt) {
  placeCooldown -= dt;
  const { tx, ty } = mouseTile();
  const target = getTile(tx, ty);
  const canReach = inReach(tx, ty);

  if (mouse.left && canReach && target !== T.AIR) {
    if (mining.tx !== tx || mining.ty !== ty) {
      mining.tx = tx; mining.ty = ty; mining.progress = 0;
    }
    const def = TILE_DEF[target];
    mining.progress += dt / def.hard;
    if (Math.random() < dt * 14) sfxDig();
    if (Math.random() < dt * 30) {
      // 挖掘碎屑
      const src = tex[target];
      if (src) particles.push({
        x: (tx + 0.5) * TILE + (Math.random() - 0.5) * TILE * 0.7,
        y: (ty + 0.5) * TILE + (Math.random() - 0.5) * TILE * 0.7,
        vx: (Math.random() - 0.5) * 3, vy: -Math.random() * 3,
        life: 0.4, t: 0, src, sx: 32, sy: 32, size: 6 + Math.random() * 4,
        spin: (Math.random() - 0.5) * 0.4, rot: Math.random() * 6.28,
      });
    }
    if (mining.progress >= 1) {
      setTile(tx, ty, T.AIR);
      inv[target] = (inv[target] || 0) + 1;
      spawnBreakParticles(tx, ty, target);
      sfxDig();
      mining.progress = 0;
      mining.tx = -1;
    }
  } else {
    mining.progress = 0;
    mining.tx = -1;
  }

  // 放置
  if (mouse.right && canReach && target === T.AIR && placeCooldown <= 0) {
    const type = HOTBAR_ORDER[selSlot];
    if (inv[type] > 0) {
      // 需要邻接实心块
      let adjacent = false;
      for (let dy = -1; dy <= 1 && !adjacent; dy++)
        for (let dx = -1; dx <= 1 && !adjacent; dx++)
          if (dx || dy) if (isSolidType(getTile(tx + dx, ty + dy))) adjacent = true;
      if (adjacent) {
        const px = tx * TILE, py = ty * TILE;
        const overlapsPlayer = px < player.x + player.w && px + TILE > player.x && py < player.y + player.h && py + TILE > player.y;
        const overlapsGuide = px < guide.x + guide.w && px + TILE > guide.x && py < guide.y + guide.h && py + TILE > guide.y;
        if (!overlapsPlayer && !overlapsGuide) {
          setTile(tx, ty, type);
          inv[type]--;
          sfxPlace();
          placeCooldown = 0.16;
        }
      }
    }
  }
}

// ---------------- 剑击 / 玩家生命 ----------------
function updateSword(dt) {
  swordCd -= dt;
  swordAnim = Math.max(0, swordAnim - dt * 5);
  shake = Math.max(0, shake - dt * 1.6);
  if (mouse.left && swordCd <= 0 && !dead) {
    const wx = mouse.x + cam.x, wy = mouse.y + cam.y;
    const px = player.cx, py = player.y + player.h * 0.45;
    const dx = wx - px, dy = wy - py;
    const len = Math.hypot(dx, dy);
    swordDir.x = len > 0.01 ? dx / len : 1;
    swordDir.y = len > 0.01 ? dy / len : 0;
    let hitAny = false;
    const cosA = Math.cos(SWORD_ARC / 2);
    for (const s of slimes) {
      const sx = s.cx - px, sy = s.cy - py;
      const d = Math.hypot(sx, sy);
      if (d > SWORD_RANGE) continue;
      const dot = d > 0.01 ? (sx * swordDir.x + sy * swordDir.y) / d : 1;
      if (dot >= cosA) {
        slimeHit(s, SWORD_DMG, swordDir.x, swordDir.y);
        hitAny = true;
      }
    }
    if (hitAny) sfxSlimeHit();
    swordCd = 0.45;
    swordAnim = 1;
  }
}

function hurtPlayer(dmg, kb) {
  hp -= dmg;
  invuln = 1.0;
  shake = 0.5;
  player.vy = -7;
  player.vx = kb;
  sfxHurt();
  if (hp <= 0) {
    hp = 0;
    if (!dead) { dead = true; deadTimer = 2.0; }
  }
}

function updateDeath(dt) {
  if (!dead) return;
  deadTimer -= dt;
  if (deadTimer <= 0) {
    dead = false;
    hp = maxHp;
    invuln = 2;
    player.x = spawnX;
    player.y = spawnY;
    player.vx = 0; player.vy = 0;
    cam.x = player.cx - VW / 2;
    cam.y = player.cy - VH / 2;
    for (let i = slimes.length - 1; i >= 0; i--) {
      if (Math.abs(slimes[i].cx - player.cx) < TILE * 6) slimes.splice(i, 1);
    }
  }
}

function updateParticles(dt) {
  for (let i = particles.length - 1; i >= 0; i--) {
    const p = particles[i];
    p.t += dt;
    if (p.t >= p.life) { particles.splice(i, 1); continue; }
    p.vy += 0.35;
    p.x += p.vx;
    p.y += p.vy;
    p.rot += p.spin;
    // 简单地面反弹
    const tx = Math.floor(p.x / TILE), ty = Math.floor((p.y + p.size / 2) / TILE);
    if (isSolidType(getTile(tx, ty)) && p.vy > 0) {
      p.vy *= -0.45;
      p.vx *= 0.7;
      p.y = ty * TILE - p.size / 2 - 1;
    }
  }
}

// ---------------- 相机 ----------------
function updateCamera(dt) {
  const tx = player.cx - VW / 2;
  const ty = player.cy - VH * 0.55;
  cam.x = lerp(cam.x, tx, 1 - Math.pow(0.002, dt));
  cam.y = lerp(cam.y, ty, 1 - Math.pow(0.002, dt));
  cam.x = clamp(cam.x, 0, WORLD_W * TILE - VW);
  cam.y = clamp(cam.y, -TILE * 20, WORLD_H * TILE - VH);
}

// ---------------- 天空 / 昼夜 ----------------
function skyState() {
  const h = Math.sin(timeOfDay * Math.PI * 2); // >0白天
  const day = clamp(h * 3 + 0.15, 0, 1);
  const dusk = clamp(1 - Math.abs(h) * 5, 0, 1);
  const night = clamp(-h * 3, 0, 1);
  return { h, day, dusk, night };
}
function mixColor(c1, c2, t) {
  return [lerp(c1[0], c2[0], t) | 0, lerp(c1[1], c2[1], t) | 0, lerp(c1[2], c2[2], t) | 0];
}
const SKY = {
  dayTop: [58, 132, 229], dayBot: [168, 216, 255],
  duskTop: [56, 52, 118], duskBot: [255, 148, 74],
  nightTop: [7, 9, 32], nightBot: [24, 29, 66],
};

function drawSky(s) {
  let top = mixColor(SKY.nightTop, SKY.dayTop, s.day);
  let bot = mixColor(SKY.nightBot, SKY.dayBot, s.day);
  top = mixColor(top, SKY.duskTop, s.dusk);
  bot = mixColor(bot, SKY.duskBot, s.dusk);
  const g = ctx.createLinearGradient(0, 0, 0, VH);
  g.addColorStop(0, `rgb(${top[0]},${top[1]},${top[2]})`);
  g.addColorStop(1, `rgb(${bot[0]},${bot[1]},${bot[2]})`);
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, VW, VH);
}

function drawStars(s) {
  if (s.night <= 0.05) return;
  ctx.save();
  for (const st of stars) {
    const tw = 0.55 + 0.45 * Math.sin(performance.now() * 0.002 * st.sp + st.ph);
    ctx.globalAlpha = s.night * tw * 0.9;
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(st.x * VW, st.y * VH * 0.75, st.sz, st.sz);
  }
  ctx.restore();
}

function drawSunMoon(s) {
  const horizonY = (SURFACE_Y - 6) * TILE - cam.y;
  const ang = timeOfDay * Math.PI * 2;
  // 太阳
  const sunX = VW * (0.5 + 0.42 * Math.cos(ang - Math.PI / 2));
  const sunY = horizonY - Math.sin(ang) * VH * 0.42;
  if (s.h > -0.08) {
    ctx.save();
    const glow = ctx.createRadialGradient(sunX, sunY, 6, sunX, sunY, 90);
    glow.addColorStop(0, 'rgba(255,236,150,0.95)');
    glow.addColorStop(0.35, 'rgba(255,214,90,0.55)');
    glow.addColorStop(1, 'rgba(255,200,80,0)');
    ctx.fillStyle = glow;
    ctx.fillRect(sunX - 90, sunY - 90, 180, 180);
    ctx.fillStyle = '#ffe27a';
    ctx.beginPath(); ctx.arc(sunX, sunY, 26, 0, 6.29); ctx.fill();
    ctx.fillStyle = '#fff3b8';
    ctx.beginPath(); ctx.arc(sunX - 4, sunY - 5, 17, 0, 6.29); ctx.fill();
    ctx.restore();
  }
  // 月亮
  const mang = ang + Math.PI;
  const moonX = VW * (0.5 + 0.42 * Math.cos(mang - Math.PI / 2));
  const moonY = horizonY - Math.sin(mang) * VH * 0.42;
  if (s.h < 0.08) {
    ctx.save();
    ctx.globalAlpha = clamp(s.night + 0.35, 0, 1);
    const glow = ctx.createRadialGradient(moonX, moonY, 8, moonX, moonY, 70);
    glow.addColorStop(0, 'rgba(220,228,255,0.5)');
    glow.addColorStop(1, 'rgba(220,228,255,0)');
    ctx.fillStyle = glow;
    ctx.fillRect(moonX - 70, moonY - 70, 140, 140);
    ctx.fillStyle = '#e8edff';
    ctx.beginPath(); ctx.arc(moonX, moonY, 21, 0, 6.29); ctx.fill();
    ctx.fillStyle = '#c9d2f0';
    ctx.beginPath(); ctx.arc(moonX - 6, moonY - 3, 5, 0, 6.29); ctx.fill();
    ctx.beginPath(); ctx.arc(moonX + 5, moonY + 6, 4, 0, 6.29); ctx.fill();
    ctx.beginPath(); ctx.arc(moonX + 7, moonY - 7, 3, 0, 6.29); ctx.fill();
    ctx.restore();
  }
}

function drawMountains() {
  const img = sprites.mountains;
  if (!img) return;
  const par = 0.25;
  const scale = (VH * 0.24) / img.height;
  const w = img.width * scale, h = img.height * scale;
  const baseY = (SURFACE_Y + 1.5) * TILE - cam.y * 0.9 - h;
  let off = -(cam.x * par) % w;
  if (off > 0) off -= w;
  ctx.save();
  ctx.globalAlpha = 0.9;
  for (let x = off; x < VW; x += w) {
    ctx.drawImage(img, x, baseY, w, h);
  }
  ctx.restore();
}

function drawClouds(dt) {
  ctx.save();
  ctx.fillStyle = '#ffffff';
  const wrapW = VW + 700;
  for (const c of clouds) {
    c.x += c.sp * dt;
    // 屏幕锚定 + 视差：x 在屏幕上循环，y 固定于天空区域
    let sx = (c.x - cam.x * 0.4) % wrapW;
    if (sx < -350) sx += wrapW;
    const sy = c.y - cam.y * 0.12;
    ctx.globalAlpha = 0.5 + c.o * 0.35;
    for (const b of c.blobs) {
      ctx.beginPath();
      ctx.ellipse(sx + b.dx * c.s, sy + b.dy * c.s, b.rx * c.s, b.ry * c.s, 0, 0, 6.29);
      ctx.fill();
    }
  }
  ctx.restore();
}

// ---------------- 世界渲染 ----------------
function drawTiles() {
  const x0 = Math.max(0, Math.floor(cam.x / TILE) - 1);
  const y0 = Math.max(0, Math.floor(cam.y / TILE) - 1);
  const x1 = Math.min(WORLD_W - 1, Math.ceil((cam.x + VW) / TILE) + 1);
  const y1 = Math.min(WORLD_H - 1, Math.ceil((cam.y + VH) / TILE) + 1);
  for (let ty = y0; ty <= y1; ty++) {
    for (let tx = x0; tx <= x1; tx++) {
      const v = world[idx(tx, ty)];
      if (v === T.AIR) continue;
      const t = tex[v];
      if (!t) continue;
      // 变体选择（伪随机稳定）
      const h2 = (tx * 73856093) ^ (ty * 19349663);
      const sx = (h2 & 1) * 64, sy = ((h2 >> 1) & 1) * 64;
      ctx.drawImage(t, sx, sy, 64, 64, tx * TILE - cam.x, ty * TILE - cam.y, TILE + 0.5, TILE + 0.5);
      // 矿石点缀：石头层偶尔闪现铜矿斑点
      if (v === T.STONE && ty > SURFACE_Y + 8) {
        const n = noise.noise2(tx * 0.35, ty * 0.35);
        if (n > 0.82) {
          const px = tx * TILE - cam.x, py = ty * TILE - cam.y;
          ctx.fillStyle = 'rgba(224,132,60,0.85)';
          const r = mulberry32(tx * 91 + ty * 57);
          for (let i = 0; i < 4; i++) {
            ctx.fillRect(px + r() * (TILE - 8), py + r() * (TILE - 8), 6, 6);
          }
        }
      }
    }
  }
  // 地表草装饰
  ctx.strokeStyle = 'rgba(46,120,40,0.9)';
  ctx.lineWidth = 2;
  ctx.beginPath();
  for (let tx = x0; tx <= x1; tx++) {
    if (world[idx(tx, surfaceH[tx])] !== T.GRASS) continue;
    if (getTile(tx, surfaceH[tx] - 1) !== T.AIR) continue;
    const n = noiseB.noise1(tx * 0.5 + 7);
    if (n < 0.55) continue;
    const blades = 2 + ((n * 10) | 0);
    const bx = tx * TILE - cam.x, by = surfaceH[tx] * TILE - cam.y;
    for (let i = 0; i < blades; i++) {
      const gx = bx + 4 + ((i * 9 + tx * 13) % (TILE - 8));
      const gh = 5 + ((i * 7 + tx) % 6);
      ctx.moveTo(gx, by + 1);
      ctx.lineTo(gx + 2, by - gh);
    }
  }
  ctx.stroke();
}

function drawEntity(e, spr) {
  if (!spr) return;
  const scale = e.h / spr.height;
  const dw = spr.width * scale, dh = e.h;
  const bob = e.onGround ? Math.abs(Math.sin(e.walkPhase)) * 3 : 0;
  const tilt = e.onGround ? Math.sin(e.walkPhase) * 0.035 : clamp(e.vy * 0.004, -0.06, 0.08);
  ctx.save();
  ctx.translate(e.cx - cam.x, e.y + e.h - cam.y - bob);
  ctx.rotate(tilt);
  ctx.scale(e.face, 1);
  ctx.drawImage(spr, -dw / 2, -dh, dw, dh);
  ctx.restore();
}

function drawGuideName() {
  ctx.save();
  ctx.font = 'bold 13px "Microsoft YaHei", sans-serif';
  ctx.textAlign = 'center';
  ctx.fillStyle = 'rgba(0,0,0,0.45)';
  ctx.fillText('向导', guide.cx - cam.x + 1, guide.y - cam.y - 9);
  ctx.fillStyle = '#ffe98a';
  ctx.fillText('向导', guide.cx - cam.x, guide.y - cam.y - 10);
  ctx.restore();
}

function drawSword() {
  if (swordAnim <= 0.02) return;
  const baseX = player.cx - cam.x, baseY = player.y + player.h * 0.4 - cam.y;
  const ang = Math.atan2(swordDir.y, swordDir.x);
  const wind = (1 - swordAnim) * 0.9;
  const sgn = Math.cos(ang) >= 0 ? 1 : -1;
  ctx.save();
  ctx.translate(baseX, baseY);
  ctx.rotate(ang + wind * sgn * 0.6);
  ctx.globalAlpha = clamp(swordAnim * 1.3, 0, 1);
  // 挥剑残影
  ctx.strokeStyle = `rgba(255,255,255,${swordAnim * 0.5})`;
  ctx.lineWidth = 12;
  ctx.lineCap = 'round';
  ctx.beginPath();
  ctx.arc(0, 0, 34, -0.7, 0.7);
  ctx.stroke();
  // 剑刃
  ctx.fillStyle = '#d7deea';
  ctx.fillRect(14, -4, 52, 8);
  ctx.fillStyle = '#aab6c8';
  ctx.fillRect(14, 1, 52, 2);
  // 剑尖
  ctx.beginPath();
  ctx.moveTo(66, -4); ctx.lineTo(80, 0); ctx.lineTo(66, 4);
  ctx.closePath();
  ctx.fillStyle = '#f2f6fc';
  ctx.fill();
  // 护手
  ctx.fillStyle = '#7a5a2a';
  ctx.fillRect(8, -9, 7, 17);
  ctx.fillStyle = '#5d4520';
  ctx.fillRect(8, 4, 7, 4);
  ctx.restore();
}

function drawMiningCrack() {
  if (mining.tx < 0 || mining.progress <= 0) return;
  const px = mining.tx * TILE - cam.x, py = mining.ty * TILE - cam.y;
  const stage = Math.min(3, (mining.progress * 4) | 0);
  const r = mulberry32(mining.tx * 131 + mining.ty * 17);
  ctx.save();
  ctx.strokeStyle = `rgba(20,16,10,${0.35 + stage * 0.18})`;
  ctx.lineWidth = 2;
  ctx.beginPath();
  for (let i = 0; i < 3 + stage * 3; i++) {
    const x1 = px + r() * TILE, y1 = py + r() * TILE;
    const x2 = x1 + (r() - 0.5) * TILE * 0.5, y2 = y1 + (r() - 0.5) * TILE * 0.5;
    ctx.moveTo(x1, y1);
    ctx.lineTo(x2, y2);
  }
  ctx.stroke();
  ctx.restore();
}

function drawHoverHighlight() {
  const { tx, ty } = mouseTile();
  if (!inReach(tx, ty)) return;
  if (getTile(tx, ty) === T.AIR && !mouse.right) {
    // 空气格：仅右键预览
  }
  ctx.save();
  ctx.strokeStyle = 'rgba(255,255,255,0.65)';
  ctx.lineWidth = 2;
  ctx.setLineDash([6, 4]);
  ctx.strokeRect(tx * TILE - cam.x + 1, ty * TILE - cam.y + 1, TILE - 2, TILE - 2);
  ctx.restore();
}

function drawParticles() {
  for (const p of particles) {
    const a = 1 - p.t / p.life;
    if (p.rect) {
      ctx.save();
      ctx.globalAlpha = a;
      ctx.fillStyle = p.color;
      ctx.fillRect(p.x - cam.x - p.size / 2, p.y - cam.y - p.size / 2, p.size, p.size);
      ctx.restore();
      continue;
    }
    ctx.save();
    ctx.globalAlpha = a;
    ctx.translate(p.x - cam.x, p.y - cam.y);
    ctx.rotate(p.rot);
    ctx.drawImage(p.src, p.sx, p.sy, 16, 16, -p.size / 2, -p.size / 2, p.size, p.size);
    ctx.restore();
  }
}

function drawNightOverlay(s) {
  if (s.night <= 0.02) return;
  ctx.fillStyle = `rgba(6,8,30,${s.night * 0.42})`;
  ctx.fillRect(0, 0, VW, VH);
}

function roundRectPath(ctx, x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.arcTo(x + w, y, x + w, y + h, r);
  ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r);
  ctx.arcTo(x, y, x + w, y, r);
  ctx.closePath();
}

// ---------------- 史莱姆绘制 ----------------
function drawSlimes() {
  for (const s of slimes) {
    const x = s.x - cam.x, y = s.y - cam.y;
    const w = s.w, h = s.h;
    const air = !s.onGround;
    const sqY = air ? 1.1 : 1 - 0.08 * Math.abs(Math.sin(s.phase));
    const sqX = air ? 0.9 : 1 + 0.05 * Math.abs(Math.sin(s.phase));
    ctx.save();
    ctx.translate(x + w / 2, y + h);
    ctx.scale(sqX, sqY);
    ctx.translate(-w / 2, -h);
    const body = s.flash > 0 ? '#ffffff' : (s.big ? '#6bd13d' : '#4ab32d');
    const shade = s.flash > 0 ? '#e8e8e8' : (s.big ? '#4a9a29' : '#368a20');
    roundRectPath(ctx, 0, 0, w, h, 7);
    ctx.fillStyle = body;
    ctx.fill();
    ctx.fillStyle = shade;
    ctx.fillRect(2, h * 0.68, w - 4, h * 0.3);
    // 眼睛跟随玩家
    const look = clamp((player.cx - s.cx) / 60, -1, 1) * 2;
    ctx.fillStyle = '#ffffff';
    const ey = h * 0.36;
    ctx.fillRect(w * 0.14, ey, w * 0.22, h * 0.22);
    ctx.fillRect(w * 0.64, ey, w * 0.22, h * 0.22);
    ctx.fillStyle = '#151515';
    ctx.fillRect(w * 0.22 + look * 1.5, ey + h * 0.07, w * 0.09, h * 0.09);
    ctx.fillRect(w * 0.72 + look * 1.5, ey + h * 0.07, w * 0.09, h * 0.09);
    // 嘴
    ctx.fillStyle = shade;
    ctx.fillRect(w * 0.36, h * 0.6, w * 0.28, h * 0.12);
    // 受伤血条
    if (s.hp < s.maxHp) {
      const bw = w * 0.8, bx = (w - bw) / 2, by = -9;
      ctx.fillStyle = 'rgba(0,0,0,0.55)';
      ctx.fillRect(bx, by, bw, 4);
      ctx.fillStyle = '#ff4757';
      ctx.fillRect(bx + 1, by + 1, (bw - 2) * Math.max(0, s.hp / s.maxHp), 2);
    }
    ctx.restore();
  }
}

// ---------------- HUD ----------------
function drawHeart(cx, cy, size, frac, flicker) {
  ctx.save();
  ctx.translate(cx, cy);
  ctx.scale(size / 30, size / 30);
  if (flicker) ctx.globalAlpha = 0.5;
  const heart = () => {
    ctx.beginPath();
    ctx.moveTo(0, 12);
    ctx.bezierCurveTo(-14, 1, -10, -11, -2, -8);
    ctx.bezierCurveTo(-2, -12, 2, -12, 2, -8);
    ctx.bezierCurveTo(10, -11, 14, 1, 0, 12);
    ctx.closePath();
  };
  heart();
  ctx.fillStyle = 'rgba(16,6,10,0.6)';
  ctx.fill();
  if (frac <= 0) { ctx.restore(); return; }
  ctx.save();
  if (frac < 1) {
    ctx.beginPath();
    ctx.rect(-16, -16, 32 * frac, 32);
    ctx.clip();
  }
  heart();
  ctx.fillStyle = '#ff3b57';
  ctx.fill();
  ctx.fillStyle = '#ff7a8f';
  ctx.beginPath();
  ctx.arc(-4, -6, 4, 0, 6.29);
  ctx.fill();
  ctx.restore();
  ctx.restore();
}

function drawHpUI() {
  const X = 16, Y = 14;
  const hearts = Math.ceil(maxHp / 20);
  const full = hp / 20;
  for (let i = 0; i < hearts; i++) {
    const frac = clamp(full - i, 0, 1);
    const flicker = invuln > 0 && (Math.floor(performance.now() / 90) % 2 === 0);
    drawHeart(X + 8 + i * 30, Y + 14, 30, frac, flicker);
  }
  ctx.save();
  ctx.font = 'bold 15px "Microsoft YaHei", sans-serif';
  ctx.textAlign = 'left';
  ctx.shadowColor = 'rgba(0,0,0,0.75)';
  ctx.shadowBlur = 4;
  ctx.fillStyle = '#c8ffc8';
  ctx.fillText('凝胶 ×' + gel, X + 6, Y + 48);
  ctx.restore();
}

function drawHurtFlash() {
  if (invuln > 0 && !dead) {
    ctx.fillStyle = `rgba(190,20,20,${invuln * 0.22})`;
    ctx.fillRect(0, 0, VW, VH);
  }
}

function drawDeathScreen() {
  if (!dead) return;
  ctx.fillStyle = 'rgba(60,0,0,0.4)';
  ctx.fillRect(0, 0, VW, VH);
  ctx.save();
  ctx.textAlign = 'center';
  ctx.shadowColor = 'rgba(0,0,0,0.8)';
  ctx.shadowBlur = 8;
  ctx.font = 'bold 46px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#ff5b5b';
  ctx.fillText('你 死 了', VW / 2, VH / 2 - 10);
  ctx.font = '16px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#ffd0d0';
  ctx.fillText('正在重生…', VW / 2, VH / 2 + 26);
  ctx.restore();
}

// ---------------- 热键栏 UI ----------------
const hotbarEl = document.getElementById('hotbar');
const slotEls = [];
function buildHotbar() {
  HOTBAR_ORDER.forEach((t, i) => {
    const slot = document.createElement('div');
    slot.className = 'slot';
    const num = document.createElement('span');
    num.className = 'num'; num.textContent = i + 1;
    const cv = document.createElement('canvas');
    cv.width = cv.height = 64;
    const cnt = document.createElement('span');
    cnt.className = 'count';
    slot.appendChild(num); slot.appendChild(cv); slot.appendChild(cnt);
    hotbarEl.appendChild(slot);
    slotEls.push({ slot, cv, cnt, type: t });
  });
}
function refreshHotbarIcons() {
  for (const s of slotEls) {
    const t = tex[s.type];
    if (!t) continue;
    const g = s.cv.getContext('2d');
    g.imageSmoothingEnabled = false;
    g.drawImage(t, 0, 0, 64, 64, 0, 0, 64, 64);
  }
}
function updateHotbar() {
  for (let i = 0; i < slotEls.length; i++) {
    const s = slotEls[i];
    s.slot.classList.toggle('sel', i === selSlot);
    s.cnt.textContent = inv[s.type] || 0;
  }
}

function updateClock(s) {
  const el = document.getElementById('clock');
  if (s.night > 0.5) el.textContent = '☾ 夜晚';
  else if (s.dusk > 0.4) el.textContent = '☀ 黄昏';
  else el.textContent = '☀ 白天';
}

// ---------------- 云 / 星星初始化 ----------------
function initSky() {
  const r = mulberry32(2024);
  for (let i = 0; i < 10; i++) {
    const blobs = [];
    const n = 3 + ((r() * 3) | 0);
    for (let j = 0; j < n; j++) {
      blobs.push({ dx: j * 34 - n * 16 + r() * 12, dy: r() * 12 - 6, rx: 26 + r() * 20, ry: 13 + r() * 8 });
    }
    clouds.push({
      x: r() * 2400, y: 25 + r() * 190,
      s: 0.7 + r() * 0.9, sp: 0.25 + r() * 0.5, o: r(), blobs,
    });
  }
  for (let i = 0; i < 170; i++) {
    stars.push({ x: r(), y: r(), sz: r() < 0.8 ? 2 : 3, sp: 0.6 + r() * 2.4, ph: r() * 6.28 });
  }
}

// ---------------- 主循环 ----------------
let lastT = 0;
function loop(ts) {
  requestAnimationFrame(loop);
  if (!ready) return;
  let dt = Math.min((ts - lastT) / 1000, 0.05);
  lastT = ts;

  timeOfDay = (timeOfDay + dt / DAY_LENGTH) % 1;

  updatePlayer(dt);
  updateGuide(dt);
  updateSlimes(dt);
  updateMining(dt);
  updateSword(dt);
  updateParticles(dt);
  updateDeath(dt);
  updateCamera(dt);

  const s = skyState();
  // 屏幕震动
  const shx = shake > 0 ? (Math.random() - 0.5) * shake * 14 : 0;
  const shy = shake > 0 ? (Math.random() - 0.5) * shake * 14 : 0;
  ctx.save();
  ctx.translate(shx, shy);
  drawSky(s);
  drawStars(s);
  drawSunMoon(s);
  drawMountains();
  drawClouds(dt);
  drawTiles();
  drawSlimes();
  drawEntity(guide, sprites.guide);
  drawGuideName();
  drawEntity(player, sprites.player);
  drawSword();
  drawParticles();
  drawMiningCrack();
  drawNightOverlay(s);
  drawHoverHighlight();
  ctx.restore();
  drawHurtFlash();
  drawDeathScreen();
  drawHpUI();
  updateHotbar();
  updateClock(s);
}

// ---------------- 初始化 ----------------
async function init() {
  const loadbar = document.querySelector('#loadbar > div');
  const loadtext = document.getElementById('loadtext');
  const setP = (p, t) => { loadbar.style.width = (p * 100) + '%'; if (t) loadtext.textContent = t; };

  try {
    setP(0.05, '加载方块纹理…');
    const tileTypes = Object.keys(TILE_DEF).map(Number);
    const tileImgs = await Promise.all(tileTypes.map(t => loadImage(TILE_DEF[t].img)));
    tileTypes.forEach((t, i) => { tex[t] = makeTile(tileImgs[i], TILE_DEF[t].cropTop || 0); });
    setP(0.4, '处理角色素材…');

    const [pImg, gImg, mImg] = await Promise.all([
      loadImage('assets/sprites/player.png'),
      loadImage('assets/sprites/guide.png'),
      loadImage('assets/bg/mountains.png'),
    ]);
    setP(0.6, '抠除背景…');
    sprites.player = removeWhiteBG(pImg);
    setP(0.72);
    sprites.guide = removeWhiteBG(gImg);
    setP(0.84, '生成世界…');
    sprites.mountains = removeWhiteBG(mImg);

    await new Promise(r => setTimeout(r, 30));
    genWorld();
    initSky();
    buildHotbar();
    refreshHotbarIcons();

    // 出生点
    const spawnTX = WORLD_W >> 1;
    player.x = spawnTX * TILE + TILE / 2 - player.w / 2;
    player.y = (surfaceH[spawnTX] - 3) * TILE;
    spawnX = player.x; spawnY = player.y;
    guide.x = player.x + TILE * 4;
    guide.y = player.y;
    cam.x = player.cx - VW / 2;
    cam.y = player.cy - VH / 2;

    // 初始史莱姆
    for (let i = 0; i < 3; i++) trySpawnSlime();

    setP(1, '完成！');
    ready = true;
    setTimeout(() => {
      const lo = document.getElementById('loading');
      lo.style.opacity = '0';
      setTimeout(() => lo.remove(), 550);
    }, 250);
  } catch (err) {
    loadtext.textContent = '资源加载失败：' + err.message;
    console.error(err);
  }
}

requestAnimationFrame(loop);
init();

