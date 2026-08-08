'use strict';
/* =========================================================
 * 松林卫士 · Pine Grove Guardian  —— 线虫灾害主题
 * 剧情：松林被松树线虫病侵染。向导指引主角找到益生菌与无人机，
 *       利用无人机释放益生菌，净化线虫并击败传播线虫的天牛Boss。
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
  [T.GRASS]:  { key: 'grass',  name: '草皮',   hard: 0.45, img: 'assets/tiles/grass.png',  cropTop: 0.10 },
  [T.DIRT]:   { key: 'dirt',   name: '泥土',   hard: 0.40, img: 'assets/tiles/dirt.png' },
  [T.STONE]:  { key: 'stone',  name: '岩石',   hard: 1.05, img: 'assets/tiles/stone.png' },
  [T.WOOD]:   { key: 'wood',   name: '松木',   hard: 0.70, img: 'assets/tiles/wood.png' },
  [T.LEAVES]: { key: 'leaves', name: '松针',   hard: 0.18, img: 'assets/tiles/leaves.png' },
  [T.SAND]:   { key: 'sand',   name: '沙地',   hard: 0.40, img: 'assets/tiles/sand.png' },
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
let shake = 0;
let spawnX = 0, spawnY = 0;

// ---------------- 无人机 / 益生菌 ----------------
const drone = { x: 0, y: 0, vx: 0, vy: 0, rot: 0, rotor: 0, cd: 0 };
let proBiotic = 0;          // 益生菌能量
const MAX_PROBIOTIC = 6;
const probioticShots = [];   // 益生菌弹
const probioticPickups = []; // 可拾取的益生菌菌落
const WORMS = [];            // 线虫
let longicorn = null;        // 天牛Boss
let bossActive = false;
let bossAlertShown = 0;
let victory = false, victoryTimer = 0;
let spawnTimer = 1.5;
const MAX_WORMS = 8;
let missionStarted = false;  // 向导交付无人机后开始战斗
let purified = 0;            // 净化的线虫数量
const BOSS_TRIGGER = 6;      // 净化达到该数量后，天牛出现

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

// ---------------- 世界生成（松林） ----------------
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
    growPine(x, surfaceH[x] - 1);
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

  // 散布益生菌菌落（可拾取）
  for (let i = 0; i < 10; i++) {
    const tx = 20 + ((noiseB.noise1(i * 37.7 + 5) * (WORLD_W - 40)) | 0);
    let gy = surfaceH[tx];
    while (gy < WORLD_H && !isSolidType(getTile(tx, gy))) gy++;
    if (gy >= WORLD_H) continue;
    probioticPickups.push({
      x: tx * TILE + TILE / 2,
      y: (gy - 1) * TILE - 6,
      taken: false,
      respawn: 8 + i * 0.5,
      phase: i * 1.3,
    });
  }
}

// 针叶松树
function growPine(tx, groundY) {
  const rand = mulberry32(tx * 31 + 7);
  const h = 9 + ((rand() * 5) | 0);       // 更高
  for (let i = 0; i < h; i++) setTile(tx, groundY - i, T.WOOD);
  const topY = groundY - h;
  // 针叶层：多层三角形簇
  let layerR = 2;
  for (let dy = 0; dy >= -4; dy--) {
    const y = topY + dy;
    const r = layerR;
    for (let dx = -r; dx <= r; dx++) {
      const x = tx + dx;
      const cur = getTile(x, y);
      if ((cur === T.AIR || cur === T.WOOD) && Math.abs(dx) + Math.abs(dy + 2) <= r + 1) {
        setTile(x, y, T.LEAVES);
      }
    }
    layerR = Math.min(3, layerR + (dy % 2 === 0 ? 1 : 0));
  }
  // 树顶尖
  setTile(tx, topY - 1, T.LEAVES);
  setTile(tx + (rand() < 0.5 ? 1 : -1), topY, T.LEAVES);
  setTile(tx, topY, T.LEAVES);
}

// ---------------- 音效 ----------------
let AC = null;
function audio() {
  if (!AC) AC = new (window.AudioContext || window.webkitAudioContext)();
  if (AC.state === 'suspended') AC.resume();
  return AC;
}
function tone(freq0, freq1, dur, type, vol) {
  try {
    const ac = audio();
    const o = ac.createOscillator(); o.type = type || 'sine';
    o.frequency.setValueAtTime(freq0, ac.currentTime);
    if (freq1) o.frequency.exponentialRampToValueAtTime(freq1, ac.currentTime + dur);
    const g = ac.createGain();
    g.gain.setValueAtTime(vol || 0.15, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.001, ac.currentTime + dur);
    o.connect(g); g.connect(ac.destination);
    o.start(); o.stop(ac.currentTime + dur + 0.02);
  } catch (e) { }
}
function sfxDig() { tone(0, 0, 0.06, 'sine', 0); }
function sfxPlace() { tone(160, 70, 0.1, 'sine', 0.2); }
function sfxJump() { tone(220, 440, 0.1, 'square', 0.05); }
function sfxHurt() { tone(320, 80, 0.2, 'sawtooth', 0.18); }
function sfxDrone() { tone(700, 900, 0.05, 'triangle', 0.06); }
function sfxProbiotic() { tone(500, 1200, 0.08, 'triangle', 0.12); }
function sfxPurify() { tone(900, 300, 0.14, 'square', 0.12); }
function sfxBoss() { tone(150, 400, 0.6, 'sawtooth', 0.18); }
function sfxPickup() { tone(800, 1600, 0.12, 'sine', 0.12); }
function sfxVictory() { tone(600, 1200, 0.6, 'triangle', 0.15); }

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

// ---------------- 输入 ----------------
const keys = {};
const mouse = { x: 0, y: 0, left: false, right: false };

window.addEventListener('keydown', e => {
  const k = e.key.toLowerCase();
  keys[k] = true;
  if (k === ' ') e.preventDefault();
  if (k === 'h') {
    helpVisible = !helpVisible;
    const el = document.getElementById('help');
    if (el) el.style.display = helpVisible ? 'block' : 'none';
  }
  const n = parseInt(k, 10);
  if (n >= 1 && n <= HOTBAR_ORDER.length) selSlot = n - 1;
});
window.addEventListener('keyup', e => { keys[e.key.toLowerCase()] = false; });
window.addEventListener('mousedown', e => {
  if (e.button === 0) mouse.left = true;
  if (e.button === 2) mouse.right = true;
});
window.addEventListener('mouseup', e => {
  if (e.button === 0) mouse.left = false;
  if (e.button === 2) mouse.right = false;
});
window.addEventListener('mousemove', e => { mouse.x = e.clientX; mouse.y = e.clientY; });

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
    // 交付无人机
    if (!missionStarted && distP >= -TILE * 2) {
      missionStarted = true;
      sfxPickup();
      drone.given = true;
    }
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

// ---------------- 线虫敌人 ----------------
class Worm extends Entity {
  constructor(cx, bottomY) {
    super(cx - 22, bottomY - 12, 44, 12);
    this.maxHp = 12;
    this.hp = this.maxHp;
    this.speed = 1.3;
    this.dir = Math.random() < 0.5 ? -1 : 1;
    this.flash = 0;
    this.phase = Math.random() * 6.28;
    this.timer = 0.5 + Math.random();
    this.buried = false;
  }
}

function overlap(a, b) {
  return a.x < b.x + b.w && a.x + a.w > b.x && a.y < b.y + b.h && a.y + a.h > b.y;
}

function spawnWorm(cx, bottomY) {
  const w = new Worm(cx, bottomY);
  WORMS.push(w);
}

function trySpawnWorm() {
  for (let attempt = 0; attempt < 6; attempt++) {
    const dir = Math.random() < 0.5 ? -1 : 1;
    const distTiles = 16 + Math.random() * 24;
    const tx = clamp(Math.round(player.cx / TILE + dir * distTiles), 6, WORLD_W - 6);
    let gy = surfaceH[tx];
    while (gy < WORLD_H && !isSolidType(getTile(tx, gy))) gy++;
    if (gy >= WORLD_H) continue;
    if (Math.abs(tx * TILE - player.cx) < TILE * 8) continue;
    const w = 44, h = 12, x = tx * TILE + TILE / 2, y = gy * TILE;
    if (rectHitsSolid(x - w / 2, y - h, w, h)) continue;
    spawnWorm(x, y);
    return;
  }
}

function updateWorms(dt) {
  if (missionStarted) {
    spawnTimer -= dt;
    if (spawnTimer <= 0 && WORMS.length < MAX_WORMS && !dead && !victory) {
      trySpawnWorm();
      spawnTimer = 3.5 + Math.random() * 4;
    }
  }
  for (let i = WORMS.length - 1; i >= 0; i--) {
    const w = WORMS[i];
    w.flash = Math.max(0, w.flash - dt);
    w.phase += dt * 8;
    w.timer -= dt;
    const dx = player.cx - w.cx;
    // 朝玩家缓慢蠕动
    if (Math.abs(dx) > 4) w.dir = dx > 0 ? 1 : -1;
    w.vx = lerp(w.vx, w.dir * w.speed, 0.08);
    w.physics();
    // 蠕动弹跳
    if (w.onGround && w.timer <= 0) {
      w.vy = -4.5;
      w.timer = 1 + Math.random() * 1.5;
    }
    if (overlap(w, player) && invuln <= 0 && !dead) {
      hurtPlayer(14, dx > 0 ? 5 : -5);
    }
    if (w.y > WORLD_H * TILE + 100) WORMS.splice(i, 1);
  }
}

function wormHit(w, dmg) {
  w.hp -= dmg;
  w.flash = 0.14;
  if (w.hp <= 0) {
    const i = WORMS.indexOf(w);
    if (i >= 0) WORMS.splice(i, 1);
    spawnWormParticles(w);
    sfxPurify();
    purified++;
    if (!bossActive && !victory && missionStarted && purified >= BOSS_TRIGGER) {
      spawnBoss();
    }
  }
}

function spawnWormParticles(w) {
  for (let i = 0; i < 10; i++) {
    particles.push({
      x: w.cx + (Math.random() - 0.5) * w.w,
      y: w.cy + (Math.random() - 0.5) * w.h,
      vx: (Math.random() - 0.5) * 6,
      vy: -Math.random() * 5 - 1,
      life: 0.4 + Math.random() * 0.4,
      t: 0,
      color: Math.random() < 0.5 ? '#ffd5c8' : '#9ae66a',
      size: 3 + Math.random() * 4,
      spin: 0, rot: 0, rect: true,
    });
  }
}

// ---------------- 天牛 Boss ----------------
class Longicorn extends Entity {
  constructor(cx, y) {
    super(cx - 40, y - 32, 80, 32);
    this.maxHp = 300;
    this.hp = this.maxHp;
    this.phase = 0;
    this.attackTimer = 2.5;
    this.speed = 2.2;
    this.dir = Math.random() < 0.5 ? -1 : 1;
    this.animT = 0;
    this.enraged = false;
    this.flash = 0;
  }
}

function spawnBoss() {
  const dir = player.cx > WORLD_W * TILE / 2 ? -1 : 1;
  const tx = clamp(Math.round(player.cx / TILE + dir * 24), 8, WORLD_W - 8);
  longicorn = new Longicorn(tx * TILE, surfaceH[tx] * TILE - 60);
  bossActive = true;
  bossAlertShown = 2.2;
  sfxBoss();
}

function updateBoss(dt) {
  if (!bossActive || !longicorn) return;
  const b = longicorn;
  b.flash = Math.max(0, b.flash - dt);
  b.animT += dt;
  b.phase += dt * 4;
  b.attackTimer -= dt;

  const dx = player.cx - b.cx;

  // 朝玩家移动（天牛缓慢飞行，贴近玩家）
  b.dir = dx > 0 ? 1 : -1;
  b.vx = lerp(b.vx, b.dir * b.speed, 0.05);
  b.vy = lerp(b.vy, (player.cy - b.cy) * 0.02, 0.05);
  b.physics();

  // 释放小线虫
  if (b.attackTimer <= 0) {
    for (let i = 0; i < 2 + (b.enraged ? 1 : 0); i++) {
      spawnWorm(b.cx + (i - 0.5) * 20, b.cy + b.h / 2);
    }
    sfxBoss();
    b.attackTimer = 3 + (b.enraged ? 1.5 : 3.5);
  }

  // 触碰伤害
  if (overlap(b, player) && invuln <= 0 && !dead) {
    hurtPlayer(18, dx > 0 ? 7 : -7);
  }

  // 半血狂暴
  if (!b.enraged && b.hp <= b.maxHp / 2) {
    b.enraged = true;
    b.speed = 3.1;
    sfxBoss();
  }

  if (b.hp <= 0) {
    bossDefeated();
  }
}

function bossHit(dmg) {
  if (!longicorn) return;
  longicorn.hp -= dmg;
  longicorn.flash = 0.1;
  longicorn.hp = Math.max(0, longicorn.hp);
  if (longicorn.hp <= 0) bossDefeated();
}

function bossDefeated() {
  if (!bossActive) return;
  for (let i = 0; i < 26; i++) {
    particles.push({
      x: longicorn.cx + (Math.random() - 0.5) * longicorn.w,
      y: longicorn.cy + (Math.random() - 0.5) * longicorn.h,
      vx: (Math.random() - 0.5) * 9,
      vy: -Math.random() * 7 - 1,
      life: 0.6 + Math.random() * 0.6,
      t: 0,
      color: Math.random() < 0.5 ? '#ff8a4c' : '#9ae66a',
      size: 4 + Math.random() * 6,
      spin: 0, rot: 0, rect: true,
    });
  }
  longicorn = null;
  bossActive = false;
  victory = true;
  victoryTimer = 3.5;
  sfxVictory();
}

// ---------------- 无人机 / 益生菌 ----------------
function updateDrone(dt) {
  drone.rotor += dt * 40;
  drone.cd -= dt;
  drone.given = missionStarted && !victory;

  if (!drone.given) {
    // 尚未获得无人机：待命在向导旁
    drone.x = guide.cx;
    drone.y = guide.y - 60;
    drone.rot = Math.sin(performance.now() * 0.002) * 0.1;
    return;
  }

  // 跟随玩家，悬浮在玩家头顶
  const tx = player.cx;
  const ty = player.y + player.h * 0.18 - 60;
  drone.vx = lerp(drone.vx, (tx - drone.x) * 0.1, 0.1);
  drone.vy = lerp(drone.vy, (ty - drone.y) * 0.08, 0.1);
  drone.x += drone.vx * dt;
  drone.y += drone.vy * dt;
  drone.rot = clamp((tx - drone.x) * 0.01, -0.25, 0.25);

  // 发射益生菌（鼠标左键）
  if ((mouse.left || keys['j'] || keys['q']) && drone.cd <= 0 && proBiotic > 0 && !dead) {
    const wx = mouse.x + cam.x, wy = mouse.y + cam.y;
    const dx = wx - drone.x, dy = wy - drone.y;
    const len = Math.hypot(dx, dy) || 1;
    probioticShots.push({
      x: drone.x, y: drone.y,
      vx: (dx / len) * 10, vy: (dy / len) * 10,
      life: 1.4,
    });
    proBiotic--;
    drone.cd = 0.28;
    sfxDrone();
    sfxProbiotic();
  }

  // 益生菌弹
  for (let i = probioticShots.length - 1; i >= 0; i--) {
    const s = probioticShots[i];
    s.x += s.vx; s.y += s.vy;
    s.life -= dt;
    let used = false;
    if (s.life <= 0) used = true;
    // 命中线虫
    for (let wi = WORMS.length - 1; wi >= 0; wi--) {
      const w = WORMS[wi];
      if (s.x > w.x - 4 && s.x < w.x + w.w + 4 && s.y > w.y - 4 && s.y < w.y + w.h + 4) {
        wormHit(w, 100);
        used = true;
        break;
      }
    }
    // 命中天牛
    if (!used && bossActive && longicorn && s.x > longicorn.x - 6 && s.x < longicorn.x + longicorn.w + 6 && s.y > longicorn.y - 6 && s.y < longicorn.y + longicorn.h + 6) {
      bossHit(25);
      used = true;
    }
    if (used) {
      // 净化粒子
      for (let j = 0; j < 6; j++) {
        particles.push({
          x: s.x, y: s.y,
          vx: (Math.random() - 0.5) * 4,
          vy: (Math.random() - 0.5) * 4,
          life: 0.3 + Math.random() * 0.3,
          t: 0,
          color: '#b7ff5e',
          size: 3 + Math.random() * 3,
          spin: 0, rot: 0, rect: true,
        });
      }
      probioticShots.splice(i, 1);
    }
  }

  // 益生菌菌落拾取
  for (const p of probioticPickups) {
    if (p.taken) { p.respawn -= dt; if (p.respawn <= 0) { p.taken = false; p.respawn = 8; } continue; }
    if (!missionStarted) continue;
    const dx = p.x - player.cx, dy = p.y - (player.y + player.h * 0.4);
    if (dx * dx + dy * dy < TILE * TILE * 1.2) {
      if (proBiotic < MAX_PROBIOTIC) {
        proBiotic++;
        p.taken = true;
        p.respawn = 10 + Math.random() * 8;
        sfxPickup();
      }
    }
  }
}

// ---------------- 玩家受击 / 死亡 ----------------
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
    for (let i = WORMS.length - 1; i >= 0; i--) {
      if (Math.abs(WORMS[i].cx - player.cx) < TILE * 6) WORMS.splice(i, 1);
    }
  }
}

function updateVictory(dt) {
  if (!victory) return;
  victoryTimer -= dt;
  // 净化：所有线虫消散
  for (let i = WORMS.length - 1; i >= 0; i--) {
    wormHit(WORMS[i], 100);
  }
  if (victoryTimer <= 0) {
    victory = false;
    // 重置Boss以便再次挑战
    bossActive = false;
    longicorn = null;
    purified = 0;
    WORMS.length = 0;
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
  dayTop: [70, 138, 96], dayBot: [190, 224, 180],   // 松林绿调
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
      const h2 = (tx * 73856093) ^ (ty * 19349663);
      const sx = (h2 & 1) * 64, sy = ((h2 >> 1) & 1) * 64;
      ctx.drawImage(t, sx, sy, 64, 64, tx * TILE - cam.x, ty * TILE - cam.y, TILE + 0.5, TILE + 0.5);
      // 受侵染的枯黄松针（带病斑的树）
      if (v === T.LEAVES) {
        const n = noise.noise2(tx * 0.2 + 31, ty * 0.2 + 17);
        if (n > 0.55) {
          const px = tx * TILE - cam.x, py = ty * TILE - cam.y;
          ctx.fillStyle = 'rgba(190,120,40,0.8)';
          const r = mulberry32(tx * 71 + ty * 23);
          for (let i = 0; i < 3; i++) {
            ctx.fillRect(px + r() * (TILE - 10), py + r() * (TILE - 10), 5, 5);
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

// ---------------- 线虫绘制 ----------------
function drawWorms() {
  for (const w of WORMS) {
    const x = w.x - cam.x, y = w.y - cam.y;
    const segs = 6, segW = w.w / segs;
    const baseY = y + w.h;
    const body = w.flash > 0 ? '#ffffff' : '#f2c3b5';
    const dark = w.flash > 0 ? '#e8e8e8' : '#d79a86';
    // 蠕动波
    for (let i = 0; i < segs; i++) {
      const sx = x + i * segW;
      const offset = Math.sin(w.phase + i * 0.8) * 3;
      const sy = baseY - offset - 4;
      ctx.fillStyle = body;
      ctx.beginPath();
      ctx.ellipse(sx + segW / 2, sy, segW * 0.62, 6, 0, 0, 6.29);
      ctx.fill();
      if (i === segs - 1) {
        // 头部朝向
        const hx = sx + segW * (w.dir > 0 ? 0.8 : -0.8);
        ctx.fillStyle = dark;
        ctx.beginPath();
        ctx.ellipse(hx, sy - 1, segW * 0.7, 5, 0, 0, 6.29);
        ctx.fill();
        ctx.fillStyle = '#2a1a14';
        ctx.fillRect(hx - 2, sy - 3, 2, 2);
      }
    }
  }
}

// ---------------- 天牛绘制 ----------------
function drawLongicorn() {
  if (!longicorn) return;
  const b = longicorn;
  const x = b.x - cam.x, y = b.y - cam.y;
  const w = b.w, h = b.h;
  const body = b.flash > 0 ? '#fff' : (b.enraged ? '#e05b2a' : '#b06a3a');
  const dark = b.flash > 0 ? '#eee' : (b.enraged ? '#a33f18' : '#7a4522');
  const wingA = Math.sin(b.animT * 20) * 0.9;
  ctx.save();
  ctx.translate(x + w / 2, y + h / 2);
  ctx.rotate(b.dir > 0 ? 0 : Math.PI);
  // 翅膀（张开）
  ctx.save();
  ctx.rotate(wingA);
  ctx.fillStyle = body;
  ctx.beginPath();
  ctx.ellipse(-6, -14, 12, 16, 0, 0, 6.29);
  ctx.fill();
  ctx.restore();
  ctx.save();
  ctx.rotate(-wingA);
  ctx.beginPath();
  ctx.ellipse(-6, 14, 12, 16, 0, 0, 6.29);
  ctx.fill();
  ctx.restore();
  // 身体
  ctx.fillStyle = dark;
  roundRectPath(ctx, -w / 2 + 8, -h / 2, w - 16, h, 8);
  ctx.fill();
  // 斑纹
  ctx.fillStyle = '#3a2210';
  for (let i = 0; i < 4; i++) {
    ctx.beginPath();
    ctx.arc(-8 - i * 8, 0, 3, 0, 6.29);
    ctx.fill();
  }
  // 头部 + 触角
  ctx.fillStyle = dark;
  ctx.beginPath();
  ctx.arc(w / 2 - 8, 0, 9, 0, 6.29);
  ctx.fill();
  ctx.strokeStyle = '#2a1a10';
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(w / 2 - 4, -6);
  ctx.lineTo(w / 2 + 12, -16 + Math.sin(b.animT * 8) * 2);
  ctx.moveTo(w / 2 - 4, 6);
  ctx.lineTo(w / 2 + 12, 16 + Math.cos(b.animT * 8) * 2);
  ctx.stroke();
  // 眼睛
  ctx.fillStyle = '#ffd94d';
  ctx.beginPath(); ctx.arc(w / 2 - 4, -4, 3, 0, 6.29); ctx.fill();
  ctx.beginPath(); ctx.arc(w / 2 - 4, 4, 3, 0, 6.29); ctx.fill();
  ctx.restore();
}

// ---------------- 无人机绘制 ----------------
function drawDrone() {
  const x = drone.x - cam.x, y = drone.y - cam.y;
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(drone.rot);
  // 旋翼
  const rotorOffset = Math.sin(drone.rotor) * 4;
  ctx.strokeStyle = 'rgba(200,220,255,0.5)';
  ctx.lineWidth = 3;
  ctx.beginPath();
  ctx.moveTo(-20, -8 + rotorOffset);
  ctx.lineTo(20, -8 + rotorOffset);
  ctx.stroke();
  // 机身
  ctx.fillStyle = '#3a4a5a';
  roundRectPath(ctx, -16, -5, 32, 14, 4);
  ctx.fill();
  ctx.fillStyle = '#5a738c';
  roundRectPath(ctx, -16, -5, 32, 5, 4);
  ctx.fill();
  // 益生菌舱（发光）
  const glow = 0.5 + 0.5 * Math.sin(performance.now() * 0.004);
  ctx.fillStyle = `rgba(155,230,106,${0.5 + glow * 0.5})`;
  ctx.beginPath();
  ctx.arc(0, 4, 5 + glow * 1.5, 0, 6.29);
  ctx.fill();
  ctx.restore();
}

// ---------------- 益生菌弹绘制 ----------------
function drawProbioticShots() {
  for (const s of probioticShots) {
    ctx.save();
    ctx.fillStyle = 'rgba(183,255,94,0.4)';
    ctx.beginPath();
    ctx.arc(s.x - cam.x, s.y - cam.y, 10, 0, 6.29);
    ctx.fill();
    ctx.fillStyle = '#c8ff7a';
    ctx.beginPath();
    ctx.arc(s.x - cam.x, s.y - cam.y, 5, 0, 6.29);
    ctx.fill();
    ctx.fillStyle = '#ffffff';
    ctx.beginPath();
    ctx.arc(s.x - cam.x - 1, s.y - cam.y - 1, 2, 0, 6.29);
    ctx.fill();
    ctx.restore();
  }
}

// ---------------- 益生菌菌落绘制 ----------------
function drawProbioticPickups() {
  for (const p of probioticPickups) {
    if (p.taken) continue;
    if (!missionStarted) continue;
    const pulse = 0.6 + 0.4 * Math.sin(performance.now() * 0.003 + p.phase);
    const x = p.x - cam.x, y = p.y - cam.y;
    ctx.save();
    ctx.fillStyle = `rgba(155,230,106,${0.25 + pulse * 0.2})`;
    ctx.beginPath();
    ctx.arc(x, y, 14 + pulse * 3, 0, 6.29);
    ctx.fill();
    ctx.fillStyle = '#9ae66a';
    ctx.beginPath();
    ctx.arc(x, y, 7, 0, 6.29);
    ctx.fill();
    ctx.fillStyle = '#d7ffb0';
    ctx.beginPath();
    ctx.arc(x - 2, y - 2, 3, 0, 6.29);
    ctx.fill();
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
  // 益生菌能量条
  ctx.save();
  ctx.font = 'bold 15px "Microsoft YaHei", sans-serif';
  ctx.textAlign = 'left';
  ctx.shadowColor = 'rgba(0,0,0,0.75)';
  ctx.shadowBlur = 4;
  ctx.fillStyle = '#d7ffb0';
  ctx.fillText('益生菌', X + 6, Y + 46);
  ctx.shadowBlur = 0;
  const barW = 150, bx = X + 60, by = Y + 34;
  ctx.fillStyle = 'rgba(0,0,0,0.55)';
  roundRectPath(ctx, bx, by, barW, 14, 7);
  ctx.fill();
  const fill = clamp(proBiotic / MAX_PROBIOTIC, 0, 1);
  if (fill > 0) {
    ctx.fillStyle = '#9ae66a';
    roundRectPath(ctx, bx + 2, by + 2, (barW - 4) * fill, 10, 5);
    ctx.fill();
  }
  ctx.restore();
}

function drawBossBar() {
  if (!bossActive || !longicorn) return;
  const w = Math.min(VW * 0.55, 460);
  const x = VW / 2 - w / 2, y = 16, h = 20;
  ctx.save();
  ctx.textAlign = 'center';
  ctx.font = 'bold 14px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#fff';
  ctx.shadowColor = 'rgba(0,0,0,0.8)';
  ctx.shadowBlur = 4;
  ctx.fillText('松墨天牛', VW / 2, y - 4);
  ctx.shadowBlur = 0;
  ctx.fillStyle = 'rgba(0,0,0,0.6)';
  roundRectPath(ctx, x, y + 2, w, h, 6);
  ctx.fill();
  const frac = clamp(longicorn.hp / longicorn.maxHp, 0, 1);
  ctx.fillStyle = longicorn.enraged ? '#ff5b3a' : '#ff9a4c';
  roundRectPath(ctx, x + 2, y + 4, (w - 4) * frac, h - 4, 5);
  ctx.fill();
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
  ctx.fillText('你 倒 下 了', VW / 2, VH / 2 - 10);
  ctx.font = '16px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#ffd0d0';
  ctx.fillText('线虫仍在蔓延…重生后继续战斗', VW / 2, VH / 2 + 26);
  ctx.restore();
}

function drawVictoryScreen() {
  if (!victory) return;
  ctx.save();
  ctx.textAlign = 'center';
  ctx.shadowColor = 'rgba(0,0,0,0.8)';
  ctx.shadowBlur = 8;
  ctx.font = 'bold 40px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#9ae66a';
  ctx.fillText('松林得救了！', VW / 2, VH / 2 - 30);
  ctx.font = '17px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#e8ffd0';
  ctx.fillText('益生菌已净化线虫，天牛被击败', VW / 2, VH / 2 + 6);
  ctx.restore();
}

function drawBossAlert() {
  if (bossAlertShown <= 0) return;
  ctx.save();
  ctx.textAlign = 'center';
  const a = Math.min(1, bossAlertShown);
  ctx.globalAlpha = a;
  ctx.shadowColor = 'rgba(0,0,0,0.8)';
  ctx.shadowBlur = 8;
  ctx.font = 'bold 32px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#ff8a4c';
  ctx.fillText('松墨天牛出现了！', VW / 2, VH * 0.32);
  ctx.restore();
}

function drawObjective() {
  if (victory) return;
  ctx.save();
  ctx.textAlign = 'center';
  ctx.font = '13px "Microsoft YaHei", sans-serif';
  ctx.shadowColor = 'rgba(0,0,0,0.7)';
  ctx.shadowBlur = 3;
  ctx.fillStyle = 'rgba(255,255,255,0.85)';
  if (!missionStarted) {
    ctx.fillText('靠近向导领取无人机，净化线虫灾害', VW / 2, VH - 80);
  } else if (!bossActive && WORMS.length > 0) {
    ctx.fillText('发射益生菌净化线虫（鼠标左键）', VW / 2, VH - 80);
  }
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
  bossAlertShown = Math.max(0, bossAlertShown - dt);
  shake = Math.max(0, shake - dt * 1.6);

  updatePlayer(dt);
  updateGuide(dt);
  updateWorms(dt);
  updateBoss(dt);
  updateDrone(dt);
  updateParticles(dt);
  updateDeath(dt);
  updateVictory(dt);
  updateCamera(dt);

  const s = skyState();
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
  drawWorms();
  drawLongicorn();
  drawEntity(guide, sprites.guide);
  drawGuideName();
  drawEntity(player, sprites.player);
  drawDrone();
  drawProbioticShots();
  drawProbioticPickups();
  drawParticles();
  drawNightOverlay(s);
  ctx.restore();
  drawHurtFlash();
  drawDeathScreen();
  drawVictoryScreen();
  drawBossAlert();
  drawBossBar();
  drawHpUI();
  drawObjective();
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
    setP(0.84, '生成松林…');
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

    // 初始线虫
    for (let i = 0; i < 3; i++) trySpawnWorm();

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
