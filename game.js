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

// ---------------- 工具系统 ----------------
const TOOL_PICKAXE = 'pickaxe';
const TOOL_REMOTE = 'remote';
const TOOL_SUMMONER = 'summoner';   // 召唤器：直接召唤天牛Boss
const TOOL_DEFS = {
  [TOOL_PICKAXE]: { name: '稿子', icon: 'pickaxe' },
  [TOOL_REMOTE]:  { name: '遥控器', icon: 'remote' },
  [TOOL_SUMMONER]: { name: '召唤器', icon: 'summoner' },
};
let ownedTools = [TOOL_PICKAXE, TOOL_SUMMONER];  // 初始有稿子+召唤器
let selTool = TOOL_PICKAXE;          // 当前手持工具
let remoteGiven = false;             // 向导是否已交付遥控器

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
HOTBAR_ORDER.forEach(t => inv[t] = 0); // 背包：挖掘所得方块

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
const drone = { x: 0, y: 0, vx: 0, vy: 0, rot: 0, rotor: 0, cd: 0, deployed: false };
// 向导身边的守卫无人机：始终跟随向导，自动攻击附近的线虫
const guardDrone = { x: 0, y: 0, vx: 0, vy: 0, rot: 0, rotor: 0, cd: 0, target: null };
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

// ---------------- 向导对话 ----------------
let dialogOpen = false;      // 对话面板是否打开
let dialogLine = 0;          // 当前对话索引
let dialogCooldown = 0;      // 防止按住E连点
let talkHint = 0;            // 提示"按E交谈"闪烁计时
let dialogTypewriter = 0;    // 打字机效果进度
const DIALOG = {
  intro: [                    // 初始（未领取遥控器）
    '呼……终于找到你了。我是这片松林的守林人。',
    '你手里的稿子可派上用场——挖开泥土岩石，收集方块备用。',
    '等等，我把这个遥控器和一点益生菌交给你。',
    '靠近我就能领取。拿遥控器时按右键，就能召唤无人机了。',
  ],
  ready: [                    // 已领取遥控器，正在净化线虫
    '很好！你拿到遥控器和益生菌了。',
    '我身边的这架守卫无人机会自动帮你清除线虫。',
    '你也能用遥控器召唤自己的无人机，左键喷洒益生菌。',
    '天牛可不好对付——它会冲锋、发射孢子弹，还会释放线虫！',
  ],
  boss: [                     // 天牛出现
    '小心！那就是传播线虫的松墨天牛！',
    '它会朝你冲锋、吐出孢子弹，还会不断释放小线虫！',
    '保持遥控器在手，无人机持续发射益生菌命中它的身体！',
    '半血之后它会进入狂暴，弹幕更密，务必走位躲开！',
  ],
  victory: [                  // 胜利后
    '太好了……松林终于得救了！',
    '你不仅消灭了线虫，还击败了松墨天牛。',
    '这片林子会慢慢恢复生机。谢谢你，守卫者。',
    '不过也许……远处还有别的威胁。保持警惕。',
  ],
};

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
      const timer = setTimeout(() => { URL.revokeObjectURL(url); rej(new Error('load timeout: ' + src)); }, 10000);
      im.onload = () => { clearTimeout(timer); URL.revokeObjectURL(url); res(im); };
      im.onerror = () => { clearTimeout(timer); URL.revokeObjectURL(url); rej(new Error('load fail: ' + src)); };
      im.src = url;
    }));
}

// 把大图缩小到不超过 maxW 宽（等比），降低抠图/处理开销，避免同步阻塞
function downscaleImage(img, maxW = 520) {
  const w = img.width, h = img.height;
  if (w <= maxW) return img;
  const ratio = maxW / w;
  const nw = Math.round(w * ratio), nh = Math.round(h * ratio);
  const c = document.createElement('canvas');
  c.width = nw; c.height = nh;
  c.getContext('2d').imageSmoothingEnabled = true;
  c.getContext('2d').drawImage(img, 0, 0, nw, nh);
  return c;
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

// 清理部件：去除残留的纯白背景（含两腿间空隙的白），再裁剪透明边距
function cleanPart(c) {
  const w = c.width, h = c.height;
  const g = c.getContext('2d');
  const id = g.getImageData(0, 0, w, h);
  const d = id.data;
  for (let i = 0; i < w * h; i++) {
    const r = d[i * 4], gg = d[i * 4 + 1], b = d[i * 4 + 2];
    // 纯白/接近纯白 → 透明
    if (r > 240 && gg > 240 && b > 240) d[i * 4 + 3] = 0;
  }
  g.putImageData(id, 0, 0);
  return trimTransparent(c);
}

// 裁掉帧底部的纯黑/暗色基线（扫描底部像素，若大面积为暗色则裁掉该行）
function trimFrameBottom(frameCanvas, maxTrim = 14) {
  const w = frameCanvas.width, h = frameCanvas.height;
  const g = frameCanvas.getContext('2d');
  const id = g.getImageData(0, 0, w, h);
  const d = id.data;
  // 从底部向上扫描，找到第一个"含主体像素"的行作为保留行
  let cutRows = 0;
  for (let row = h - 1; row >= 0 && cutRows < maxTrim; row--) {
    let darkCount = 0, total = 0;
    for (let x = 0; x < w; x++) {
      const i = (row * w + x) * 4;
      const r = d[i], gg = d[i + 1], b = d[i + 2], a = d[i + 3];
      if (a < 30) continue;
      total++;
      // 暗色像素：明度 < 80
      if (r + gg + b < 240) darkCount++;
    }
    // 若该行几乎全暗（>60%）且不透明像素较多，认为是基线
    if (total > w * 0.3 && darkCount / total > 0.6) cutRows++;
    else break;
  }
  if (cutRows === 0) return frameCanvas;
  const newH = h - cutRows;
  const out = document.createElement('canvas');
  out.width = w; out.height = newH;
  out.getContext('2d').drawImage(frameCanvas, 0, 0, w, newH, 0, 0, w, newH);
  return out;
}

// 把 sprite sheet 横向切分为 N 个独立帧 canvas
// 返回 { frames: [canvas,...], frameW, frameH }
function splitSheetFrames(img, frameCount, trimBottom = true) {
  const w = img.width, h = img.height;
  const frameW = Math.floor(w / frameCount);
  const frames = [];
  for (let i = 0; i < frameCount; i++) {
    const c = document.createElement('canvas');
    c.width = frameW; c.height = h;
    c.getContext('2d').drawImage(img, i * frameW, 0, frameW, h, 0, 0, frameW, h);
    const final = trimBottom ? trimFrameBottom(c) : c;
    frames.push(final);
  }
  return { frames, frameW, frameH: frames[0].height };
}

// 裁剪掉画布四周的完全透明边距（保留所有不透明像素）
function trimTransparent(c) {
  const w = c.width, h = c.height;
  const g = c.getContext('2d');
  const id = g.getImageData(0, 0, w, h);
  const d = id.data;
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

// 把人物 sprite 从髋部切分为上半身 + 左腿 + 右腿
// hipYFrac: 髋部相对 sprite 高度的比例（0~1）
// midXFrac: 左右腿分界线相对 sprite 宽度的比例
// legFrac: 单腿宽度相对 sprite 宽度的比例
function splitSpriteParts(img, hipYFrac, midXFrac, legFrac) {
  const w = img.width, h = img.height;
  const hipY = Math.round(h * hipYFrac);       // 头顶到髋部的像素
  const midX = Math.round(w * midXFrac);
  const legW = Math.round(w * legFrac);
  const upperH = hipY;
  const legH = h - hipY;                        // 脚底到髋部
  // 切分并只去纯白、保持原始矩形尺寸（不裁剪透明边距，避免接缝缺口）
  const mk = (sw, sh, sx, sy) => {
    const c = document.createElement('canvas');
    c.width = sw; c.height = sh;
    c.getContext('2d').drawImage(img, sx, sy, sw, sh, 0, 0, sw, sh);
    removeWhiteKeepSize(c);
    return c;
  };
  const upper = mk(w, upperH, 0, 0);
  const leftLeg = mk(legW, legH, midX - legW, hipY);
  const rightLeg = mk(legW, legH, midX, hipY);
  return {
    upper,
    leftLeg,
    rightLeg,
    // 布局信息（原始像素单位）
    upperW: w, upperH,
    leftLegX: midX - legW,
    rightLegX: midX,
    legW, legH,
    hipY,
    fullW: w, fullH: h,
  };
}

// 把纯白像素设为透明，但保持画布尺寸不变（用于切分部件，避免接缝缺口）
function removeWhiteKeepSize(c) {
  const w = c.width, h = c.height;
  const g = c.getContext('2d');
  const id = g.getImageData(0, 0, w, h);
  const d = id.data;
  for (let i = 0; i < w * h; i++) {
    if (d[i * 4] > 240 && d[i * 4 + 1] > 240 && d[i * 4 + 2] > 240) d[i * 4 + 3] = 0;
  }
  g.putImageData(id, 0, 0);
}
function removeBossBG(img) {
  // 品红(#ff00ff)色键 + 洪水填充：去掉背景及抗锯齿边缘的紫红晕边
  const w = img.width, h = img.height;
  const c = document.createElement('canvas');
  c.width = w; c.height = h;
  const g = c.getContext('2d');
  g.drawImage(img, 0, 0);
  const id = g.getImageData(0, 0, w, h);
  const d = id.data;
  // 品红判定（含抗锯齿边缘）：R 与 B 都高，G 明显偏低 → 紫红背景
  const isMagenta = i => {
    const r = d[i * 4], gg = d[i * 4 + 1], b = d[i * 4 + 2];
    // 天牛主体是暖色（橙/棕/红），其特征是 B 低；品红背景 B 高。
    // 判断：R>130 且 B>130 且 G < R-50 且 G < B-50（纯品红 & 边缘紫红）
    if (r < 130 || b < 130) return false;
    return gg < r - 50 && gg < b - 50;
  };
  // 洪水填充：从四边向内，删除与边缘连通的品红区域（含抗锯齿过渡像素）
  const visited = new Uint8Array(w * h);
  const stack = [];
  for (let x = 0; x < w; x++) { stack.push(x); stack.push((h - 1) * w + x); }
  for (let y = 0; y < h; y++) { stack.push(y * w); stack.push(y * w + w - 1); }
  while (stack.length) {
    const i = stack.pop();
    if (visited[i] || !isMagenta(i)) continue;
    visited[i] = 1;
    d[i * 4 + 3] = 0;
    const x = i % w, y = (i / w) | 0;
    if (x > 0 && !visited[i - 1]) stack.push(i - 1);
    if (x < w - 1 && !visited[i + 1]) stack.push(i + 1);
    if (y > 0 && !visited[i - w]) stack.push(i - w);
    if (y < h - 1 && !visited[i + w]) stack.push(i + w);
  }
  g.putImageData(id, 0, 0);
  // 裁剪到非透明主体
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
  if (n >= 1 && n <= ownedTools.length) selTool = ownedTools[n - 1];
  // 滚轮已处理；这里也允许用 Q 切换
  if (k === 'q') {
    const idx = ownedTools.indexOf(selTool);
    selTool = ownedTools[(idx + 1) % ownedTools.length];
  }
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

// ---------------- 挖掘 / 放置 / 工具使用 ----------------
const REACH = 8 * TILE;   // 挖掘/放置可达距离（更宽松）
const mining = { tx: -1, ty: -1, progress: 0 };
let placeCooldown = 0;
let remoteCooldown = 0;
let summonCooldown = 0;

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

// 切换遥控器：召唤/收起无人机
function toggleDrone() {
  if (!remoteGiven) return;
  drone.deployed = !drone.deployed;
  if (drone.deployed) {
    drone.x = player.cx;
    drone.y = player.y - 60;
    sfxPickup();
  } else {
    sfxPlace();
  }
}

function updateTools(dt) {
  placeCooldown -= dt;
  remoteCooldown -= dt;
  const { tx, ty } = mouseTile();
  const target = getTile(tx, ty);
  const canReach = inReach(tx, ty);

  if (selTool === TOOL_REMOTE) {
    // 遥控器：右键召唤/收起无人机
    if (mouse.right && remoteCooldown <= 0 && !dead) {
      toggleDrone();
      remoteCooldown = 0.3;
    }
    return;
  }

  if (selTool === TOOL_SUMMONER) {
    // 召唤器：按 F 键召唤天牛 Boss（无视 purified 阈值）
    if (keys['f'] && summonCooldown <= 0 && !dead && !victory) {
      if (bossActive) {
        // 已有 Boss 时则不重复召唤
        summonCooldown = 0.5;
      } else {
        spawnBoss();
        summonCooldown = 2.0;
      }
      keys['f'] = false;
    }
    return;
  }

  // 稿子：左键挖掘
  if (mouse.left && canReach && target !== T.AIR && !dead) {
    if (mining.tx !== tx || mining.ty !== ty) {
      mining.tx = tx; mining.ty = ty; mining.progress = 0;
    }
    const def = TILE_DEF[target];
    mining.progress += dt * 2.5 / def.hard;
    if (Math.random() < dt * 14) sfxDig();
    if (Math.random() < dt * 30) {
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
      inv[target] = (inv[target] || 0) + 1;  // 挖下的方块进背包
      spawnBreakParticles(tx, ty, target);
      sfxDig();
      mining.progress = 0;
      mining.tx = -1;
    }
  } else {
    mining.progress = 0;
    mining.tx = -1;
  }

  // 稿子：右键放置背包中的方块
  if (mouse.right && canReach && target === T.AIR && placeCooldown <= 0 && !dead) {
    // 选一个背包里有数量的方块放置
    const type = HOTBAR_ORDER.find(t => inv[t] > 0);
    if (type !== undefined) {
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
    // 靠近守林人：交付遥控器与初始益生菌，开始任务
    if (!missionStarted && distP >= -TILE * 2) {
      missionStarted = true;
      remoteGiven = true;
      if (!ownedTools.includes(TOOL_REMOTE)) ownedTools.push(TOOL_REMOTE);
      if (proBiotic < MAX_PROBIOTIC) proBiotic = Math.max(proBiotic, 3); // 初始益生菌
      sfxPickup();
      updateHotbarDOM();
      refreshHotbarIcons();
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

// ---------------- 向导对话 ----------------
function guideDialogKey() {
  if (victory) return 'victory';
  if (bossActive) return 'boss';
  if (missionStarted) return 'ready';
  return 'intro';
}

function guideNearPlayer() {
  const dx = guide.cx - player.cx;
  const dy = (guide.y + guide.h / 2) - (player.y + player.h / 2);
  return dx * dx + dy * dy < TILE * TILE * 4;
}

function updateDialog(dt) {
  dialogCooldown -= dt;
  talkHint = Math.max(0, talkHint - dt);

  if (!dialogOpen) {
    // 靠近向导时显示提示
    if (guideNearPlayer() && !dead) {
      talkHint = 0.12; // 保持闪烁计时（每帧重置，用于闪烁）
      if (keys['e'] && dialogCooldown <= 0 && !victory) {
        openDialog();
      }
    }
    return;
  }

  // 对话打开中：按住E/Esc推进
  if (keys['e'] || keys['escape']) {
    const lines = DIALOG[guideDialogKey()];
    if (dialogTypewriter < lines[dialogLine].length) {
      dialogTypewriter = lines[dialogLine].length; // 立刻显示整句
    } else if (dialogCooldown <= 0) {
      dialogLine++;
      if (dialogLine >= lines.length) {
        dialogOpen = false;
        dialogLine = 0;
      } else {
        dialogTypewriter = 0;
        dialogCooldown = 0.3;
      }
    }
    keys['e'] = false; // 避免按住连跳
    keys['escape'] = false;
  }
}

function openDialog() {
  dialogOpen = true;
  dialogLine = 0;
  dialogTypewriter = 0;
  dialogCooldown = 0.35;
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

// ---------------- 天牛 Boss（蜂后式多模式） ----------------
const bossShots = []; // 天牛的毒素弹
class Longicorn extends Entity {
  constructor(cx, y) {
    super(cx - 75, y - 52, 150, 52);
    this.maxHp = 380;
    this.hp = this.maxHp;
    this.phase = 0;
    this.mode = 'chase';         // chase 追袭 / dash 冲锋 / volley 弹幕
    this.modeTimer = 3;
    this.attackTimer = 2.5;
    this.dashTimer = 0;
    this.dashVX = 0;
    this.speed = 2.4;
    this.baseSpeed = 2.4;
    this.dir = Math.random() < 0.5 ? -1 : 1;
    this.animT = 0;
    this.enraged = false;
    this.flash = 0;
    this.hoverY = y;
    this.pendingDash = null;
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

// 天牛撞击摧毁其身体经过的方块（留出通道）
function bossSmashBlocks(b) {
  const x0 = Math.max(0, Math.floor((b.x + b.w * 0.2) / TILE));
  const x1 = Math.min(WORLD_W - 1, Math.floor((b.x + b.w * 0.8) / TILE));
  const y0 = Math.max(0, Math.floor((b.y + b.h * 0.3) / TILE));
  const y1 = Math.min(WORLD_H - 1, Math.floor((b.y + b.h * 0.85) / TILE));
  for (let ty = y0; ty <= y1; ty++) {
    for (let tx = x0; tx <= x1; tx++) {
      const v = getTile(tx, ty);
      if (v === T.AIR || v === T.LEAVES) continue;
      setTile(tx, ty, T.AIR);
      spawnBreakParticles(tx, ty, v);
      if (Math.random() < 0.5) sfxDig();
    }
  }
}

function updateBoss(dt) {
  if (!bossActive || !longicorn) return;
  const b = longicorn;
  b.flash = Math.max(0, b.flash - dt);
  b.animT += dt;
  b.phase += dt * 4;
  b.attackTimer -= dt;
  b.modeTimer -= dt;

  const dx = player.cx - b.cx;
  const dy = player.cy - b.cy;
  const dist = Math.hypot(dx, dy) || 1;

  // 半血狂暴
  if (!b.enraged && b.hp <= b.maxHp / 2) {
    b.enraged = true;
    b.baseSpeed = 3.2;
    sfxBoss();
  }
  b.speed = b.baseSpeed;

  // 触碰伤害
  if (overlap(b, player) && invuln <= 0 && !dead) {
    hurtPlayer(18, dx > 0 ? 7 : -7);
  }

  // 切换攻击模式
  if (b.modeTimer <= 0) {
    const modes = ['dash', 'volley', 'chase'];
    // 非狂暴时偏好追袭+冲锋；狂暴后更频繁弹幕
    const pick = b.enraged
      ? ['volley', 'dash', 'volley', 'chase']
      : ['chase', 'dash', 'chase', 'volley'];
    b.mode = pick[(Math.random() * pick.length) | 0];
    b.modeTimer = b.mode === 'volley' ? 2.5 : (b.enraged ? 2.6 : 3.4);
    if (b.mode === 'dash') {
      // 锁定玩家位置并冲锋
      b.pendingDash = { vx: (dx / dist) * (b.speed * 3.2), vy: (dy / dist) * (b.speed * 3.2) };
      b.dashTimer = 0.55;
    }
  }

  switch (b.mode) {
    case 'chase': {
      // 追袭：缓慢贴近玩家
      b.dir = dx > 0 ? 1 : -1;
      b.vx = lerp(b.vx, b.dir * b.speed * 0.7, 0.06);
      b.vy = lerp(b.vy, (dy / dist) * b.speed * 0.6, 0.06);
      // 追袭中偶发释放线虫
      if (b.attackTimer <= 0) {
        for (let i = 0; i < 1 + (b.enraged ? 1 : 0); i++) spawnWorm(b.cx, b.cy + b.h / 2);
        sfxBoss();
        b.attackTimer = 2.6 + (b.enraged ? 1 : 2);
      }
      break;
    }
    case 'dash': {
      // 冲锋：锁定方向快速冲刺
      if (b.dashTimer > 0) {
        b.dashTimer -= dt;
        b.vx = lerp(b.vx, b.pendingDash.vx, 0.25);
        b.vy = lerp(b.vy, b.pendingDash.vy, 0.25);
      } else {
        b.vx = lerp(b.vx, 0, 0.1);
        b.vy = lerp(b.vy, 0, 0.1);
      }
      break;
    }
    case 'volley': {
      // 弹幕：向玩家发射毒素弹
      b.vx = lerp(b.vx, 0, 0.08);
      b.vy = lerp(b.vy, 0, 0.08);
      if (b.attackTimer <= 0) {
        const n = b.enraged ? 5 : 3;
        for (let i = 0; i < n; i++) {
          const ang = Math.atan2(dy, dx) + (i - (n - 1) / 2) * 0.22;
          bossShots.push({
            x: b.cx, y: b.cy + b.h / 2,
            vx: Math.cos(ang) * 5.2, vy: Math.sin(ang) * 5.2,
            life: 3.5,
          });
        }
        sfxBoss();
        b.attackTimer = b.enraged ? 0.9 : 1.5;
      }
      break;
    }
  }

  b.physics();

  // ---- 天牛撞击摧毁方块 ----
  bossSmashBlocks(b);

  // 毒素弹
  for (let i = bossShots.length - 1; i >= 0; i--) {
    const s = bossShots[i];
    s.x += s.vx; s.y += s.vy;
    s.life -= dt;
    let used = false;
    if (s.life <= 0) used = true;
    const tx = Math.floor(s.x / TILE), ty = Math.floor(s.y / TILE);
    if (isSolidType(getTile(tx, ty))) used = true;
    if (!used && s.x > player.x - 4 && s.x < player.x + player.w + 4 && s.y > player.y - 4 && s.y < player.y + player.h + 4) {
      hurtPlayer(10, s.vx > 0 ? 4 : -4);
      used = true;
    }
    if (used) {
      for (let j = 0; j < 5; j++) {
        particles.push({
          x: s.x, y: s.y,
          vx: (Math.random() - 0.5) * 3, vy: (Math.random() - 0.5) * 3,
          life: 0.3, t: 0, color: '#b06a3a', size: 3 + Math.random() * 3,
          spin: 0, rot: 0, rect: true,
        });
      }
      bossShots.splice(i, 1);
    }
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
  bossShots.length = 0;
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

  if (!remoteGiven) {
    // 尚未获得遥控器：无人机待命在向导旁（展示用）
    drone.x = guide.cx;
    drone.y = guide.y - 60;
    drone.rot = Math.sin(performance.now() * 0.002) * 0.1;
    return;
  }

  if (!drone.deployed) {
    // 已收起：无人机隐藏，仅记录位置
    drone.rot = Math.sin(performance.now() * 0.002) * 0.1;
    return;
  }

  // 召唤中：跟随玩家，悬浮在玩家头顶
  const tx = player.cx;
  const ty = player.y + player.h * 0.18 - 60;
  drone.vx = lerp(drone.vx, (tx - drone.x) * 0.1, 0.1);
  drone.vy = lerp(drone.vy, (ty - drone.y) * 0.08, 0.1);
  drone.x += drone.vx * dt;
  drone.y += drone.vy * dt;
  drone.rot = clamp((tx - drone.x) * 0.01, -0.25, 0.25);

  // 发射益生菌（鼠标左键，仅遥控器模式下无人机已召唤）
  if (selTool === TOOL_REMOTE && mouse.left && drone.cd <= 0 && proBiotic > 0 && !dead) {
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
}

// 益生菌弹碰撞（玩家无人机与守卫无人机共用）
function updateProbioticShots(dt) {
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
}

// ---------------- 守卫无人机（向导身边，自动攻击线虫） ----------------
function updateGuardDrone(dt) {
  const g = guardDrone;
  g.rotor += dt * 40;
  g.cd -= dt;
  if (!missionStarted) {
    // 任务未开始：在向导旁待机
    g.x = guide.cx;
    g.y = guide.y - 70;
    g.rot = Math.sin(performance.now() * 0.002) * 0.1;
    return;
  }
  // 跟随向导，悬浮在向导头顶
  const tx = guide.cx;
  const ty = guide.y + guide.h * 0.15 - 78;
  g.vx = lerp(g.vx, (tx - g.x) * 0.12, 0.1);
  g.vy = lerp(g.vy, (ty - g.y) * 0.09, 0.1);
  g.x += g.vx * dt;
  g.y += g.vy * dt;
  g.rot = clamp((tx - g.x) * 0.01, -0.25, 0.25);

  // 寻找最近的线虫目标
  let best = null, bestD = Infinity;
  for (const w of WORMS) {
    const d = (w.cx - g.x) ** 2 + (w.cy - g.y) ** 2;
    if (d < bestD && d < TILE * TILE * 30 * 30) { // 射程
      bestD = d;
      best = w;
    }
  }
  // 若有天牛Boss，也优先锁定（天牛更优先）
  if (bossActive && longicorn) {
    const d = (longicorn.cx - g.x) ** 2 + (longicorn.cy - g.y) ** 2;
    if (d < TILE * TILE * 30 * 30 && d < bestD * 1.2) {
      best = longicorn;
    }
  }
  g.target = best;

  // 自动攻击
  if (g.target && g.cd <= 0) {
    const t = g.target;
    const dx = t.cx - g.x, dy = t.cy - g.y;
    const len = Math.hypot(dx, dy) || 1;
    probioticShots.push({
      x: g.x, y: g.y,
      vx: (dx / len) * 9, vy: (dy / len) * 9,
      life: 1.2,
    });
    g.cd = 0.45;
    sfxDrone();
    if (Math.random() < 0.4) sfxProbiotic();
  }
}

// 益生菌菌落拾取（无论无人机是否召唤都可用）
function updateProbioticPickup(dt) {
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

// 程序化人物绘制（含走路摆腿）
// cfg: { skin, shirt, pants, hair, hat, hatColor, beard }
function drawCharacter(e, parts) {
  const x = e.cx - cam.x, y = e.y + e.h - cam.y; // 脚底
  const h = e.h;
  const walking = e.onGround && Math.abs(e.vx) > 0.5;
  // 缩放：实体高 / sprite原高
  const scale = h / parts.fullH;
  const dw = parts.fullW * scale;
  // 髋部到脚底的距离（像素→世界）
  const legH = (parts.fullH - parts.hipY) * scale;   // 腿高（世界）
  const upperH = h - legH;                           // 上半身高（世界）
  const legWW = parts.legW * scale;

  const ph = walking ? e.walkPhase : 0;
  const legSwing = walking ? Math.sin(ph) : 0;
  const bob = walking ? Math.abs(Math.sin(ph)) * 3 : 0;

  ctx.save();
  // 锚点 = 脚底中点，向上为负Y
  ctx.translate(x, y - bob);
  ctx.scale(e.face, 1);
  ctx.translate(-dw / 2, 0);

  // ---- 左腿：髋部锚点 ----
  ctx.save();
  ctx.translate(parts.leftLegX * scale, -legH);
  ctx.rotate(-legSwing * 0.5);
  ctx.drawImage(parts.leftLeg, 0, 0, legWW, legH);
  ctx.restore();

  // ---- 右腿 ----
  ctx.save();
  ctx.translate(parts.rightLegX * scale, -legH);
  ctx.rotate(legSwing * 0.5);
  ctx.drawImage(parts.rightLeg, 0, 0, legWW, legH);
  ctx.restore();

  // ---- 上半身：从头顶(-h)画到髋部(-legH) ----
  ctx.drawImage(parts.upper, 0, -h, parts.upperW * scale, upperH);

  ctx.restore();
}

function drawGuideName() {
  ctx.save();
  ctx.font = 'bold 13px "Microsoft YaHei", sans-serif';
  ctx.textAlign = 'center';
  ctx.fillStyle = 'rgba(0,0,0,0.45)';
  ctx.fillText('守林人', guide.cx - cam.x + 1, guide.y - cam.y - 9);
  ctx.fillStyle = '#ffe98a';
  ctx.fillText('守林人', guide.cx - cam.x, guide.y - cam.y - 10);
  ctx.restore();
}

// 靠近时的"按E交谈"气泡
function drawTalkHint() {
  if (dialogOpen || victory) return;
  if (!guideNearPlayer() || dead) return;
  const blink = Math.floor(performance.now() / 300) % 2 === 0;
  const gx = guide.cx - cam.x, gy = guide.y - cam.y - 44;
  ctx.save();
  ctx.font = 'bold 13px "Microsoft YaHei", sans-serif';
  ctx.textAlign = 'center';
  ctx.globalAlpha = blink ? 1 : 0.45;
  ctx.fillStyle = 'rgba(0,0,0,0.5)';
  roundRectPath(ctx, gx - 46, gy - 16, 92, 24, 12);
  ctx.fill();
  ctx.fillStyle = '#fff';
  ctx.fillText('[ E ] 交谈', gx, gy);
  ctx.restore();
}

// 对话框面板
function drawDialog() {
  if (!dialogOpen) return;
  const lines = DIALOG[guideDialogKey()];
  const line = lines[dialogLine];
  const showText = line.substring(0, Math.ceil(dialogTypewriter));
  // 打字机推进
  if (dialogTypewriter < line.length) {
    dialogTypewriter += 2;
  }

  const boxW = Math.min(VW * 0.82, 860);
  const boxH = 190;
  const bx = VW / 2 - boxW / 2, by = VH - boxH - 22;
  ctx.save();
  ctx.fillStyle = 'rgba(14,20,32,0.9)';
  roundRectPath(ctx, bx, by, boxW, boxH, 18);
  ctx.fill();
  ctx.strokeStyle = 'rgba(155,230,106,0.75)';
  ctx.lineWidth = 4;
  roundRectPath(ctx, bx, by, boxW, boxH, 18);
  ctx.stroke();

  // 头像框
  const avR = 46;
  ctx.fillStyle = '#2a3a28';
  ctx.beginPath();
  ctx.arc(bx + 62, by + boxH / 2, avR, 0, 6.29);
  ctx.fill();
  ctx.strokeStyle = '#9ae66a';
  ctx.lineWidth = 4;
  ctx.beginPath();
  ctx.arc(bx + 62, by + boxH / 2, avR, 0, 6.29);
  ctx.stroke();
  // 头像（守林人简笔画）
  ctx.fillStyle = '#e8b57a';
  ctx.beginPath();
  ctx.arc(bx + 62, by + boxH / 2 - 6, 19, 0, 6.29);
  ctx.fill();
  ctx.fillStyle = '#5a3a22';
  ctx.fillRect(bx + 51, by + boxH / 2 - 19, 22, 14);
  ctx.fillStyle = '#3a2a18';
  ctx.fillRect(bx + 43, by + boxH / 2 + 8, 38, 5);

  // 名字
  ctx.textAlign = 'left';
  ctx.font = 'bold 20px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#ffe98a';
  ctx.fillText('守林人', bx + 130, by + 40);
  // 对话文本（打字机）
  ctx.font = '19px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#eef2ff';
  wrapText(showText, bx + 130, by + 78, boxW - 160, 34);
  // 提示继续
  if (dialogTypewriter >= line.length) {
    const t = Math.floor(performance.now() / 400) % 2 === 0;
    ctx.fillStyle = t ? '#9ae66a' : '#3a4a3a';
    ctx.font = '16px "Microsoft YaHei", sans-serif';
    ctx.textAlign = 'right';
    ctx.fillText('▼ 按 E / Esc 继续', bx + boxW - 24, by + boxH - 16);
  }
  ctx.restore();
}

// 换行文本
function wrapText(text, x, y, maxW, lineH) {
  ctx.textAlign = 'left';
  let line = '';
  let curY = y;
  for (const ch of text) {
    const test = line + ch;
    if (ctx.measureText(test).width > maxW && line) {
      ctx.fillText(line, x, curY);
      line = ch;
      curY += lineH;
    } else {
      line = test;
    }
  }
  if (line) ctx.fillText(line, x, curY);
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
  // 飞行帧切换：两张图按 animT 高速交替，模拟翅膀上下扇动
  const frames = sprites.longicornFrames;
  const spr = frames
    ? frames[Math.floor((b.animT * 18) % frames.length)]
    : sprites.longicorn;
  const x = b.x - cam.x, y = b.y - cam.y;
  const w = b.w, h = b.h;
  const flash = b.flash > 0;
  const face = b.dir > 0 ? 1 : -1;
  // 悬停轻微浮动
  const hover = Math.sin(b.animT * 3.5) * 2.5;

  // 缩放：保持 sprite 比例，适配天牛碰撞体
  let dw, dh;
  if (spr) {
    const ar = spr.width / spr.height;
    dw = h * 2.4;         // 比碰撞体更高大，更威压
    dh = dw / ar;
    if (dh < h * 1.9) { dh = h * 1.9; dw = dh * ar; }
  }

  ctx.save();
  // 关闭平滑：像素风放大时保持锐利
  ctx.imageSmoothingEnabled = false;
  ctx.translate(x + w / 2, y + h / 2 + hover);
  ctx.scale(face, 1);

  // ---- 狂暴光晕 ----
  if (b.enraged && !flash) {
    const auraPulse = 0.6 + 0.4 * Math.sin(b.animT * 8);
    ctx.save();
    ctx.globalAlpha = 0.5 * auraPulse;
    ctx.shadowColor = '#ff3a1a';
    ctx.shadowBlur = 26;
    ctx.beginPath();
    ctx.ellipse(0, 0, w * 0.8, h * 1.0, 0, 0, 6.29);
    ctx.fillStyle = '#ff4a1a';
    ctx.fill();
    ctx.restore();
  }

  if (spr) {
    // ---- 绘制图片天牛 ----
    if (flash) {
      // 受击闪白：白色叠加
      ctx.save();
      ctx.globalAlpha = 0.85;
      ctx.drawImage(spr, -dw / 2, -dh / 2, dw, dh);
      ctx.globalCompositeOperation = 'source-atop';
      ctx.fillStyle = '#fff';
      ctx.fillRect(-dw / 2, -dh / 2, dw, dh);
      ctx.restore();
    } else if (b.enraged) {
      // 狂暴红色调
      ctx.save();
      ctx.drawImage(spr, -dw / 2, -dh / 2, dw, dh);
      ctx.globalCompositeOperation = 'multiply';
      ctx.fillStyle = '#ff6a3a';
      ctx.globalAlpha = 0.4;
      ctx.fillRect(-dw / 2, -dh / 2, dw, dh);
      ctx.globalCompositeOperation = 'source-over';
      ctx.restore();
    } else {
      ctx.drawImage(spr, -dw / 2, -dh / 2, dw, dh);
    }
  }
  ctx.restore();

  // 阴影
  ctx.save();
  ctx.fillStyle = 'rgba(0,0,0,0.32)';
  ctx.beginPath();
  ctx.ellipse(x + w / 2, y + h - 4, w * 0.5, 6, 0, 0, 6.29);
  ctx.fill();
  ctx.restore();
}

// ---------------- 无人机绘制 ----------------
function drawDrone() {
  const x = drone.x - cam.x, y = drone.y - cam.y;
  const now = performance.now() * 0.001;
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(drone.rot);

  // 四条机械臂
  ctx.strokeStyle = '#8fa3b8';
  ctx.lineWidth = 3;
  ctx.lineCap = 'round';
  ctx.beginPath();
  ctx.moveTo(-10, 0); ctx.lineTo(-24, -12);
  ctx.moveTo(10, 0); ctx.lineTo(24, -12);
  ctx.moveTo(-10, 0); ctx.lineTo(-24, 8);
  ctx.moveTo(10, 0); ctx.lineTo(24, 8);
  ctx.stroke();

  // 四个旋翼电机 + 螺旋桨（旋转动画）
  const rotorSpin = now * 40;
  const props = [
    { px: -24, py: -12 }, { px: 24, py: -12 },
    { px: -24, py: 8 }, { px: 24, py: 8 },
  ];
  for (const p of props) {
    ctx.fillStyle = '#c9d6e4';
    ctx.beginPath();
    ctx.arc(p.px, p.py, 4, 0, 6.29);
    ctx.fill();
    // 旋转桨叶（椭圆扫出，产生模糊感）
    ctx.strokeStyle = 'rgba(200,220,255,0.65)';
    ctx.lineWidth = 2.5;
    for (let i = 0; i < 2; i++) {
      const a = rotorSpin + i * Math.PI;
      ctx.beginPath();
      ctx.moveTo(p.px + Math.cos(a) * 12, p.py + Math.sin(a) * 12);
      ctx.lineTo(p.px - Math.cos(a) * 12, p.py - Math.sin(a) * 12);
      ctx.stroke();
    }
  }

  // 机身主体
  ctx.fillStyle = '#5b7186';
  roundRectPath(ctx, -16, -5, 32, 16, 6);
  ctx.fill();
  // 机身上壳高光
  ctx.fillStyle = '#7d96ad';
  roundRectPath(ctx, -16, -5, 32, 6, 4);
  ctx.fill();
  // 机身中线暗槽
  ctx.fillStyle = '#3a4a5a';
  roundRectPath(ctx, -16, 1, 32, 2, 1);
  ctx.fill();

  // 前方指示灯（青蓝）
  const blink = Math.floor(now * 3) % 2 === 0;
  ctx.fillStyle = blink ? '#4dd8ff' : '#2a7a94';
  ctx.beginPath();
  ctx.arc(14, 0, 3, 0, 6.29);
  ctx.fill();
  ctx.fillStyle = 'rgba(77,216,255,0.35)';
  ctx.beginPath();
  ctx.arc(14, 0, 6, 0, 6.29);
  ctx.fill();

  // 尾部推进器 + 尾焰
  ctx.fillStyle = '#39495c';
  ctx.beginPath();
  ctx.moveTo(-16, -2); ctx.lineTo(-22, -3); ctx.lineTo(-22, 3); ctx.lineTo(-16, 2);
  ctx.closePath();
  ctx.fill();
  ctx.fillStyle = 'rgba(120,220,255,0.6)';
  ctx.beginPath();
  ctx.moveTo(-22, -2); ctx.lineTo(-30, 0); ctx.lineTo(-22, 2);
  ctx.closePath();
  ctx.fill();

  // 底部益生菌舱（发光）+ 喷嘴
  const glow = 0.5 + 0.5 * Math.sin(now * 5);
  ctx.fillStyle = '#26323f';
  roundRectPath(ctx, -8, 7, 16, 7, 3);
  ctx.fill();
  ctx.fillStyle = `rgba(155,230,106,${0.6 + glow * 0.4})`;
  ctx.beginPath();
  ctx.arc(0, 8, 4.5 + glow * 1.2, 0, 6.29);
  ctx.fill();
  // 舱内益生菌颗粒
  if (proBiotic > 0) {
    ctx.fillStyle = '#c8ff7a';
    ctx.beginPath();
    ctx.arc(0, 8, 2.5, 0, 6.29);
    ctx.fill();
  }
  // 底舱辉光
  ctx.fillStyle = `rgba(183,255,94,${0.25 + glow * 0.25})`;
  ctx.beginPath();
  ctx.arc(0, 12, 8, 0, 6.29);
  ctx.fill();

  // 降落架（两条短腿）
  ctx.strokeStyle = '#6b8298';
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(-7, 12); ctx.lineTo(-9, 17);
  ctx.moveTo(7, 12); ctx.lineTo(9, 17);
  ctx.stroke();

  ctx.restore();
}

// ---------------- 守卫无人机绘制（向导身边） ----------------
function drawGuardDrone() {
  const g = guardDrone;
  const x = g.x - cam.x, y = g.y - cam.y;
  const now = performance.now() * 0.001;
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(g.rot);
  ctx.globalAlpha = 0.92;

  // 两条机械臂（更短小）
  ctx.strokeStyle = '#7a8f66';
  ctx.lineWidth = 2.5;
  ctx.lineCap = 'round';
  ctx.beginPath();
  ctx.moveTo(-8, 0); ctx.lineTo(-18, -9);
  ctx.moveTo(8, 0); ctx.lineTo(18, -9);
  ctx.stroke();

  // 双旋翼
  const rotorSpin = now * 45;
  for (const p of [{ px: -18, py: -9 }, { px: 18, py: -9 }]) {
    ctx.fillStyle = '#b8c6d4';
    ctx.beginPath();
    ctx.arc(p.px, p.py, 3.5, 0, 6.29);
    ctx.fill();
    ctx.strokeStyle = 'rgba(200,240,180,0.7)';
    ctx.lineWidth = 2;
    for (let i = 0; i < 2; i++) {
      const a = rotorSpin + i * Math.PI;
      ctx.beginPath();
      ctx.moveTo(p.px + Math.cos(a) * 10, p.py + Math.sin(a) * 10);
      ctx.lineTo(p.px - Math.cos(a) * 10, p.py - Math.sin(a) * 10);
      ctx.stroke();
    }
  }

  // 机身（守卫绿）
  ctx.fillStyle = '#5a7a4a';
  roundRectPath(ctx, -12, -4, 24, 13, 5);
  ctx.fill();
  ctx.fillStyle = '#7aa866';
  roundRectPath(ctx, -12, -4, 24, 5, 4);
  ctx.fill();
  // 守卫标记（叶片徽章）
  ctx.fillStyle = '#c8ff7a';
  ctx.beginPath();
  ctx.arc(0, 1, 3, 0, 6.29);
  ctx.fill();
  ctx.strokeStyle = '#e8ffd0';
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  ctx.arc(0, 1, 5.5, 0, 6.29);
  ctx.stroke();

  // 尾部小推进器
  ctx.fillStyle = '#4a5a3a';
  ctx.beginPath();
  ctx.moveTo(-12, 0); ctx.lineTo(-17, 0);
  ctx.strokeStyle = 'rgba(180,255,140,0.6)';
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.moveTo(-17, 0); ctx.lineTo(-21, 0);
  ctx.stroke();

  // 底部益生菌舱（发光）
  const glow = 0.5 + 0.5 * Math.sin(now * 6);
  ctx.fillStyle = `rgba(155,230,106,${0.6 + glow * 0.4})`;
  ctx.beginPath();
  ctx.arc(0, 6, 3.5 + glow * 1, 0, 6.29);
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

// 天牛毒素弹绘制
function drawBossShots() {
  for (const s of bossShots) {
    ctx.save();
    ctx.fillStyle = 'rgba(176,58,42,0.35)';
    ctx.beginPath();
    ctx.arc(s.x - cam.x, s.y - cam.y, 8, 0, 6.29);
    ctx.fill();
    ctx.fillStyle = '#d36a2a';
    ctx.beginPath();
    ctx.arc(s.x - cam.x, s.y - cam.y, 4.5, 0, 6.29);
    ctx.fill();
    ctx.fillStyle = '#ffb25a';
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

  // 当前工具 + 无人机状态
  ctx.font = 'bold 14px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#cfd6ff';
  ctx.fillText('工具：' + (TOOL_DEFS[selTool] ? TOOL_DEFS[selTool].name : selTool), X + 6, Y + 76);
  if (remoteGiven) {
    ctx.fillStyle = drone.deployed ? '#b7ff5e' : '#8a94a8';
    ctx.fillText('无人机：' + (drone.deployed ? '召唤中' : '已收起'), X + 6, Y + 96);
  }
  // 背包方块
  ctx.font = '13px "Microsoft YaHei", sans-serif';
  ctx.fillStyle = '#eef2ff';
  let itemText = '';
  for (const t of HOTBAR_ORDER) {
    if (inv[t] > 0) itemText += `${TILE_DEF[t].name}×${inv[t]}  `;
  }
  if (!itemText) itemText = '背包：空（用稿子挖掘收集方块）';
  else itemText = '背包：' + itemText;
  ctx.fillText(itemText, X + 6, Y + 120);
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
  if (dialogOpen) {
    // 对话打开时隐藏
  } else if (!missionStarted) {
    ctx.fillText('靠近守林人领取遥控器与益生菌', VW / 2, VH - 80);
  } else if (selTool === TOOL_REMOTE && !drone.deployed) {
    ctx.fillText('拿遥控器按右键召唤无人机', VW / 2, VH - 80);
  } else if (selTool === TOOL_REMOTE && drone.deployed && !victory) {
    ctx.fillText('按住鼠标左键喷洒益生菌净化线虫', VW / 2, VH - 80);
  } else if (selTool === TOOL_PICKAXE) {
    ctx.fillText('左键挖掘方块，右键放置背包中的方块', VW / 2, VH - 80);
  } else if (selTool === TOOL_SUMMONER) {
    ctx.fillText('按 F 召唤松墨天牛 Boss', VW / 2, VH - 80);
  }
  // 调试信息（临时，仅排查用）
  if (window.__debug) {
    const mt = mouseTile();
    ctx.textAlign = 'left';
    ctx.font = '12px monospace';
    ctx.fillStyle = '#ff5';
    ctx.fillText(`tool=${selTool} L=${mouse.left} R=${mouse.right}`, 12, VH - 60);
    ctx.fillText(`cell=${mt.tx},${mt.ty} reach=${inReach(mt.tx, mt.ty)} prog=${mining.progress.toFixed(2)}`, 12, VH - 42);
  }
  ctx.restore();
}

// ---------------- 热键栏 UI（工具） ----------------
const hotbarEl = document.getElementById('hotbar');
const slotEls = [];
function buildHotbar() {
  // 工具槽由 DOM 动态重建（随拥有的工具变化）
  updateHotbarDOM();
}
function updateHotbarDOM() {
  hotbarEl.innerHTML = '';
  slotEls.length = 0;
  ownedTools.forEach((tool, i) => {
    const slot = document.createElement('div');
    slot.className = 'slot';
    const num = document.createElement('span');
    num.className = 'num'; num.textContent = i + 1;
    const cv = document.createElement('canvas');
    cv.width = cv.height = 64;
    slot.appendChild(num); slot.appendChild(cv);
    hotbarEl.appendChild(slot);
    slotEls.push({ slot, cv, tool });
  });
}
// 绘制工具图标
function drawToolIcon(g, tool) {
  g.clearRect(0, 0, 64, 64);
  g.imageSmoothingEnabled = false;
  if (tool === TOOL_PICKAXE) {
    // 稿子：棕色柄 + 金属头
    g.fillStyle = '#8a5a2b';
    g.fillRect(16, 28, 8, 30);
    g.fillStyle = '#6e4520';
    g.fillRect(16, 30, 8, 3);
    g.fillStyle = '#9aa3ad';
    g.fillRect(8, 18, 24, 8);
    g.fillRect(8, 18, 5, 16);
    g.fillRect(27, 18, 5, 16);
    g.fillStyle = '#c7ccd4';
    g.fillRect(8, 18, 24, 4);
  } else if (tool === TOOL_REMOTE) {
    // 遥控器：长方形机身 + 按钮 + 天线
    g.fillStyle = '#2b3a4a';
    g.fillRect(16, 14, 32, 40);
    g.fillStyle = '#3f5a72';
    g.fillRect(16, 14, 32, 8);
    g.fillStyle = '#d34d4d';
    g.beginPath(); g.arc(26, 32, 5, 0, 6.29); g.fill();
    g.fillStyle = '#4dd84d';
    g.beginPath(); g.arc(38, 32, 5, 0, 6.29); g.fill();
    g.fillStyle = '#8aa0b5';
    g.fillRect(24, 46, 16, 4);
    g.fillStyle = '#b7ff5e';
    g.fillRect(43, 8, 3, 12);
    g.fillStyle = '#9ae66a';
    g.beginPath(); g.arc(44.5, 8, 3, 0, 6.29); g.fill();
  } else if (tool === TOOL_SUMMONER) {
    // 召唤器：天牛图标的物品（带翅膀的橙红色甲虫）
    g.fillStyle = '#2a1a14';
    g.beginPath(); g.arc(32, 36, 16, 0, 6.29); g.fill();
    g.fillStyle = '#c98a4a';
    g.beginPath(); g.arc(32, 32, 12, 0, 6.29); g.fill();
    g.fillStyle = '#8a5a2b';
    g.fillRect(20, 30, 24, 6);
    g.fillStyle = '#fff8d8';
    g.beginPath(); g.arc(38, 30, 2, 0, 6.29); g.fill();
    // 翅膀
    g.fillStyle = 'rgba(216,180,140,0.7)';
    g.beginPath(); g.ellipse(20, 22, 10, 7, -0.3, 0, 6.29); g.fill();
    g.beginPath(); g.ellipse(44, 22, 10, 7, 0.3, 0, 6.29); g.fill();
    // 触角
    g.strokeStyle = '#2a1a14';
    g.lineWidth = 2;
    g.beginPath();
    g.moveTo(28, 22); g.quadraticCurveTo(22, 10, 14, 8);
    g.moveTo(36, 22); g.quadraticCurveTo(42, 10, 50, 8);
    g.stroke();
  }
}
function refreshHotbarIcons() {
  for (const s of slotEls) {
    drawToolIcon(s.cv.getContext('2d'), s.tool);
  }
}
function updateHotbar() {
  // 同步工具列表（遥控器可能刚获得）
  let changed = false;
  if (!remoteGiven && ownedTools.includes(TOOL_REMOTE)) { /* 不应发生 */ }
  if (remoteGiven && !ownedTools.includes(TOOL_REMOTE)) {
    ownedTools.push(TOOL_REMOTE);
    changed = true;
  }
  if (changed) {
    updateHotbarDOM();
    refreshHotbarIcons();
    if (!ownedTools.includes(selTool)) selTool = ownedTools[0];
  }
  for (let i = 0; i < slotEls.length; i++) {
    const s = slotEls[i];
    s.slot.classList.toggle('sel', s.tool === selTool);
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
  try {
    frame(dt, ts);
  } catch (e) {
    console.error('frame error:', e);
    if (window.__errCount === undefined) window.__errCount = 0;
    window.__errCount++;
    ctx.save();
    ctx.font = '14px monospace';
    ctx.fillStyle = '#f44';
    ctx.fillText('ERR: ' + e.message, 10, 30);
    ctx.restore();
  }
}

function frame(dt, ts) {

  timeOfDay = (timeOfDay + dt / DAY_LENGTH) % 1;
  bossAlertShown = Math.max(0, bossAlertShown - dt);
  shake = Math.max(0, shake - dt * 1.6);

  updatePlayer(dt);
  updateGuide(dt);
  updateDialog(dt);
  updateTools(dt);
  updateWorms(dt);
  updateBoss(dt);
  updateDrone(dt);
  updateGuardDrone(dt);
  updateProbioticShots(dt);
  updateProbioticPickup(dt);
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
  drawBossShots();
  drawCharacter(guide, sprites.guide);
  drawGuideName();
  drawCharacter(player, sprites.player);
  drawDrone();
  drawGuardDrone();
  drawProbioticShots();
  drawProbioticPickups();
  drawParticles();
  drawMiningCrack();
  drawNightOverlay(s);
  ctx.restore();
  drawTalkHint();
  drawHurtFlash();
  drawDeathScreen();
  drawVictoryScreen();
  drawBossAlert();
  drawBossBar();
  drawHpUI();
  drawObjective();
  drawDialog();
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
    // tiles 只需 40px 格子显示，缩小到 128px 大幅减小文件体积，避免 GitHub 上大图 HTTP/2 错误
    tileTypes.forEach((t, i) => { tex[t] = makeTile(downscaleImage(tileImgs[i], 128), TILE_DEF[t].cropTop || 0); });
    setP(0.4, '处理角色素材…');

    const [pImg, gImg, pWalkImg, gWalkImg, mImg, bossImg, bossImg2] = await Promise.all([
      loadImage('assets/sprites/player.png'),
      loadImage('assets/sprites/guide.png'),
      loadImage('assets/sprites/player_walk.png'),
      loadImage('assets/sprites/guide_walk.png'),
      loadImage('assets/bg/mountains.png'),
      loadImage('assets/boss/longicorn.png'),
      loadImage('assets/boss/longicorn-1.png'),
    ]);
    setP(0.6, '处理角色动画…');
    // 先缩小大图再抠图，避免同步处理 1536×1024 等大图导致主线程卡死
    sprites.player = splitSpriteParts(removeWhiteBG(downscaleImage(pImg, 300)), 0.64, 0.50, 0.30);
    setP(0.72);
    sprites.guide = splitSpriteParts(removeWhiteBG(downscaleImage(gImg, 300)), 0.68, 0.50, 0.34);
    setP(0.82, '召唤天牛…');
    // 天牛两张飞行帧（白底，removeWhiteBG 抠图），按 animT 切换产生翅膀扇动效果
    const frameA = removeWhiteBG(downscaleImage(bossImg, 420));
    const frameB = removeWhiteBG(downscaleImage(bossImg2, 420));
    sprites.longicorn = frameA;                  // 兼容旧引用
    sprites.longicornFrames = [frameA, frameB]; // 飞行帧序列
    setP(0.9, '生成松林…');
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
    window.__debug = true; // 临时开启调试诊断
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
