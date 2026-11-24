# csTimer 逆向笔记（含可运行源码）

对 [csTimer](https://cstimer.net/) 线上发布包的静态分析，以及一份**不依赖浏览器、可直接 `require` 的算法提取件**。

- 分析对象：`CSTIMER_VERSION = 2026.11.01`（抓取于 2026-11-24）
- 线上产物：单文件 `js/cstimer.js`，634,417 字节 / 1,167 行（Closure 压缩）
- 美化后：26,451 行，下文行号都指美化版

---

## 0. 这个文件里有什么

1. 站点结构与算法分析（§1–§9）
2. 关键代码摘录（打乱核心 `b()`、Worker 接口）
3. **完整可运行源码**（§11：`csmin.js` / `min2phase.js` / `demo.js`，三个代码块，复制成文件即可跑）
4. 复现步骤（§10：从抓包到提取的完整命令）

> 体积大的原始文件不放进仓库：`raw/cstimer.js`（634 KB）与 `cstimer.pretty.js`（925 KB），
> 按 §10 的命令可以自行生成，对应 `.gitignore` 已忽略。

---

## 1. 站点结构

```
index.html            58 KB，只有一个 <script src="js/cstimer.js">
js/cstimer.js        634 KB / 1167 行，所有模块打在一个文件里
                     CSTIMER_VERSION = 2026.11.01
cache.manifest        AppCache 离线缓存（老派但有效）
/src/                 开发页：列了 97 个 js 开发文件路径（js/scramble/*.js、
                      js/timer/*.js、js/hardware/*.js …）——线上这些文件 404，
                      但等于免费给了一张源码地图
```

运行时结构：

| 行 | 模块 | 作用 |
|---|---|---|
| 936 | `execMain/execWorker/execBoth` | 同一份代码分别跑在主线程 / Worker |
| 1369 | `isaac` | ISAAC CSPRNG（种子可复现） |
| 1479 | `mathlib` | CubieCube（块模型）、组合数、AES/SHA256、PRNG 封装 |
| 2424 | `grouplib` | 群论工具（2gen / Roux 等子集打乱要用） |
| 4659 | `min2phase` | Kociemba 两阶段求解器（`module.exports` 可用） |
| 9912 | `scrMgr` | 打乱注册表 + `$333(...)` 模板语法 + 随机状态分配 |
| 10846 | `scramble_333` | 3x3 及 40+ 个 3x3 子集打乱 |
| 11673 | `scramble_444` | 4x4 归约法打乱 |
| 14994 / 15499 / 14039 / 14579 | `scramble_222` / `clock` / `sq1` / `pyr` | 其它项目 |
| 26360 | `csTimerWorker` | Worker 接口：scrtype / scramble / seed / image |

---

## 2. 3x3 打乱是 random-state，不是「随机走 N 步」

全部 3x3 打乱都经过同一个内部函数 `b()`（`scramble_333` 私有）：

```js
  function b(U, fa, ea, la, pa, qa, Fa, Da, Oa) {
    qa = qa || H;
    Fa = Fa || H;
    U = k(U, 12);
    fa = k(fa, 12);
    ea = k(ea, 8);
    la = k(la, 8);
    var bb = "";
    do {
      var fb = fa.slice(),
        Ta = U.slice(),
        eb = la.slice(),
        Na = ea.slice(),
        Ra = n(fb, c(fb), 2),
        cb = n(eb, c(eb), 3);
      var $a = c(Ta);
      var Ya = c(Na);
      1 == $a && (h(Ta, $a, -1), $a = 0);
      1 == Ya && (h(Na, Ya, -1), Ya = 0);
      0 == $a && 0 == Ya ? ($a = a(Ta, 12), Ya = a(Na, 8)) : 0 != $a && 0 == Ya ? (Ya = a(Na, 8), $a = h(Ta, $a, t(Ya, 8))) : ($a = 0 == $a && 0 != Ya ? a(Ta, 12) : h(Ta, $a, -1), Ya = h(Na, Ya, t($a, 12)));
      if (0 != Ya + cb + $a + Ra) {
        bb = r(Fa);
        Ra = r(qa);
        cb = new mathlib.CubieCube;
        $a = new mathlib.CubieCube;
        for (Ya = 0; 12 > Ya; Ya++) cb.ea[Ya] = Ta[Ya] << 1 | fb[Ya],
          8 > Ya && (cb.ca[Ya] = eb[Ya] << 3 | Na[Ya]);
        for (Ya = 0; Ya < bb.length; Ya++) mathlib.CubieCube.CubeMult(mathlib.CubieCube.moveCube[bb[Ya]], cb, $a), cb.init($a.ca, $a.ea);
        for (Ya = 0; Ya < Ra.length; Ya++) mathlib.CubieCube.CubeMult(cb, mathlib.CubieCube.moveCube[Ra[Ya]], $a), cb.init($a.ca, $a.ea);
        pa && (cb.ori = mathlib.rn([1, 4, 8, 1, 1, 1, 24][pa]), cb.selfConj(), cb.ori = 0);
        fb = cb.toFaceCube();
        bb = f.solution(fb, 21, 1E9, 50, 2, Oa, Da)
      }
    } while (3 >= bb.length);
    return bb.replace(/ +/g, " ")
  }
```

要点：

1. 四个参数是**十六进制位掩码**，每 4 bit 一个块，`15 = 该块随机`，其它值 = 固定为第几块；
   顺序是「棱位置(12) / 棱朝向(12) / 角位置(8) / 角朝向(8)」。
2. `n(..., 2)` 随机填棱朝向并保证和为偶，`n(..., 3)` 随机填角朝向并保证和为 3 的倍数；
   `h()` 负责位置置换，并把棱/角置换的奇偶性配平。
3. 装成 `CubieCube`，用 min2phase 求一个解：`f.solution(facelet, 21, 1E9, 50, 2)`；
4. `do…while (3 >= bb.length)` 丢掉「3 步就能解」的送分状态；
5. 输出的解就是打乱公式，因此长度不固定（实测 16–21 步）。

---

## 3. 一套掩码撑起 73 种打乱

`scrMgr.scramblers` 里注册了 73 个 key。`pll / oll / coll / zbll(493 case) / vls / wvls / ttll /
eoline / eocross / cmll / lse / roux / 2gen / half / easyc …` 都是同一套 `b()` 换掩码：
固定哪些块，就得到哪种训练局面。

例子（只乱顶层 = 下两层 4 角 8 棱全固定）：

```js
// 棱位置 nibble: [15,15,15,15, 4,5,6,7, 8,9,10,11]   ← 前 4 个随机，其余钉死
// 棱朝向:        [15,15,15,15, 0,0,0,0, 0,0,0,0]
// 角位置:        [15,15,15,15, 4,5,6,7]
// 角朝向:        [15,15,15,15, 0,0,0,0]
cs.scramble_333.getAnyScramble(edgePos, edgeOri, cornerPos, cornerOri);
// → 平均 14.7 步（9–18）
```

底层归位（只乱上两层）同理，平均 18.6 步；整颗 20.1 步。

---

## 4. 4x4：归约法

`444wca` 不用 4x4 的完整状态搜索：

1. 随机生成 4x4 块状态；
2. 归约搜索配中心块 + 配棱（失败会打印 `[scramble 444] Reduction Error!`）；
3. 归约完交给 `scramble_333.solvFacelet()` 用 min2phase 解 3x3 部分；
4. 输出 WCA 记号（`Rw2` / `Uw'`），44–47 步。

单线程 1.1 s/个，所以在浏览器里必须放 Worker 里跑。

---

## 5. 随机数与 syncseed

```js
isaac.seed(256, seedStr);                       // ISAAC CSPRNG，256 轮播种
crypto.getRandomValues(new Uint16Array(256))    // 默认种子（真随机）
mathlib.setSeed(256, "syncseed" + 用户口令);      // 可复现
```

同口令 → 两台设备生成的打乱序列**逐字相同**。远程对战、同题比赛、直播复现都靠这个。

---

## 6. 计时侧

**WCA 观察规则**直接硬编码（美化版 7551 行）：

```js
Y = 17E3 < ka ? "DNF" : 15E3 < ka ? "+2" : 15 - Math.floor(ka / 1E3);
```

即：`>15s` 记 +2，`>17s` 记 DNF；8 秒语音「8s!」、12 秒「Go!!!」。

**Stackmat 计时器**（24345 行起）：不买专用线也能连——把计时器音频输出接麦克风，
Web Audio 采方波解 1200 bps 串口帧：

```
帧长 9 或 10 字符；首字符是状态 [ SILRCA ]
（S=停止 I=观察 L/R=左手/右手 C=运行 A=复位）
校验：64 + 各位数字和 == 倒数第 3 字节
时间 = 分*60000 + 秒*1000 + 毫秒
```

**蓝牙魔方**：`js/hardware/` 下 10 个驱动（GAN / MoYu / Moyu32 / QiYi / GoCube / Giiker …），
GAN 协议套了一层 AES-128-CBC 混淆（`$.aes128` 在 1365 行，`createAesCbcCodec` 在 24811 行）。

---

## 7. 数据层

- 全部 `localStorage`；大对象用 `LZString.compressToUTF16` 压缩；
- 导出带 `sha256` 校验 + `LZString` 打包；
- 「云同步」不是官方后端，而是让用户填自己的 URL（`gglData` / `wcaData` / `locData`）；
- 打乱预生成进 `localStorage.cachedScr`，Worker 异步补货。

**Worker 接口摘录**（26360 行起）：

```js
    }
  };
  self.onmessage = function(G) {
    var r = G.data;
    G = r[0];
    var y = r[1];
    r = r[2];
    var c = void 0;
    switch (y) {
      case "scrtype":
        c = t.getScrambleTypes();
        break;
      case "scramble":
        c = t.getScramble.apply(null, r);
        break;
```

---

## 8. 实测数据

3x3 随机状态打乱，1000 次（Node 22，单线程）：

```
平均 20.12 步
长度分布 {16:1, 17:9, 18:32, 19:163, 20:414, 21:381}
首步分布 U185 L151 B144 F180 R172 D168
相邻同面 0 次
5.02 ms/个（热身）
```

合法性：100/100 打乱态都能在 21 步内解出（确认是合法可达状态）。

| 项目 | 数据 |
|---|---|
| 3x3 random-state | 20.12 步 / 5 ms |
| 底层归位（只乱上两层） | 18.6 步 / 3.6 ms |
| 只乱顶层（下两层完好） | 14.7 步 / 0.6 ms |
| 4x4 归约法 | 44–47 步 / 1.1 s |
| min2phase 建表 | 75 ms（Chromium） |
| min2phase 单次求解 | 12 ms |

---

## 9. 代码地图（美化版行号）

| 模块 | 行号范围 | 备注 |
|---|---|---|
| `isaac` | 1369–1478 | 110 行，独立 |
| `mathlib` | 1479–2423 | CubieCube / `getNPerm` / `setNPerm` / `rn` / `rndEl` |
| `grouplib` | 2424–2963 | 2gen / Roux 依赖 |
| `min2phase` | 4659–5450 | 结尾 `module.exports = min2phase` |
| `scrMgr` | 9912–10000 | 结尾是 `}(mathlib.rn, mathlib.rndEl),`（原来是逗号，拼接时要补分号） |
| `scramble_333` | 10846–11672 | 结尾 `}(mathlib.getNPerm, ...)` |
| `scramble_222` | 14994–15380 | 依赖 `mathlib.rn` |
| `scramble_444` | 11673–14038 | 依赖 `Cnk` / `circle`，以及 `scramble_333.solvFacelet` |

---

## 10. 复现步骤

```bash
# 1) 抓包
curl -sL https://cstimer.net/js/cstimer.js -o cstimer.js

# 2) 美化（26k 行，便于按行号截取）
npm i js-beautify
npx js-beautify -s 2 -f cstimer.js -o cstimer.pretty.js

# 3) 按 §9 的行号截取，拼接顺序：
#    isaac → mathlib → grouplib → min2phase → scrMgr → scramble_333 → scramble_222 → scramble_444
#    注意 scrMgr 结尾的逗号要改成分号，否则语法错误

# 4) 加最小桩（约 4 行）
cat > head.js <<'EOF'
var DEBUG = false, ISCSTIMER = false;
var $ = { isArray: Array.isArray, now: function(){return Date.now();}, noop: function(){} };
var image = { face3Image: function(){}, llImage: { drawImage: function(){} } };
var kernel = { getProp: function(){ return undefined; }, pushSignal: function(){} };
EOF

# 5) 跑
cat head.js segments/*.js > csmin.js && node -e "console.log(require('./csmin.js').scramble_333.getRandomScramble())"
```

`scramble_222` 在最小桩下调用会挂（依赖 UI 侧对象），去掉它不影响 3x3/4x4。

---

## 11. 完整提取件源码

三个代码块，分别存成 `csmin.js` / `min2phase.js` / `demo.js` 即可运行：

```bash
mkdir -p src && cd src
# 把下面三段分别存盘，然后：
node demo.js
```

### 11.1 `csmin.js`

（isaac + mathlib + grouplib + min2phase + scrMgr + scramble_333 + scramble_222 + scramble_444，
最小桩已包含。CommonJS 导出 `mathlib / grouplib / min2phase / scrMgr / scramble_333 / scramble_222 / scramble_444`。）

````js
var DEBUG = false, ISCSTIMER = false;
var $ = { isArray: Array.isArray, now: function(){return Date.now();}, noop: function(){} };
var image = { face3Image: function(){}, llImage: { drawImage: function(){} } };
var kernel = { getProp: function(){ return undefined; }, pushSignal: function(){} };

var isaac = function() {
  function a(d, e) {
    var l = (d & 65535) + (e & 65535);
    return (d >>> 16) + (e >>> 16) + (l >>> 16) << 16 | l & 65535
  }

  function J() {
    for (var d = c = n = h = 0; 256 > d; ++d) y[d] = k[d] = 0;
    b = 0
  }

  function t(d) {
    function e() {
      L ^= l << 11;
      g = a(g, L);
      l = a(l, q);
      l ^= q >>> 2;
      p = a(p, l);
      q = a(q, g);
      q ^= g << 8;
      x = a(x, q);
      g = a(g, p);
      g ^= p >>> 16;
      u = a(u, g);
      p = a(p, x);
      p ^= x << 10;
      M = a(M, p);
      x = a(x, u);
      x ^= u >>> 4;
      L = a(L, x);
      u = a(u, M);
      u ^= M << 8;
      l = a(l, u);
      M = a(M, L);
      M ^= L >>> 9;
      q = a(q, M);
      L = a(L, l)
    }
    var l, q, g, p, x, u, M, T;
    var L = l = q = g = p = x = u = M = 2654435769;
    d && "number" === typeof d && (d = [d]);
    if (d instanceof Array)
      for (J(), T = 0; T < d.length; T++) k[T & 255] += "number" === typeof d[T] ? d[T] : 0;
    for (T = 0; 4 > T; T++) e();
    for (T = 0; 256 > T; T += 8) d && (L = a(L, k[T + 0]), l = a(l, k[T + 1]), q = a(q, k[T + 2]), g = a(g, k[T + 3]), p = a(p, k[T + 4]), x = a(x, k[T + 5]), u = a(u, k[T + 6]), M = a(M, k[T + 7])), e(), y[T + 0] = L, y[T + 1] = l, y[T + 2] = q, y[T + 3] = g, y[T + 4] = p, y[T + 5] = x, y[T + 6] = u, y[T + 7] = M;
    if (d)
      for (T = 0; 256 > T; T += 8) L = a(L, y[T + 0]), l = a(l, y[T + 1]), q = a(q, y[T + 2]), g = a(g, y[T + 3]), p = a(p, y[T + 4]), x = a(x, y[T + 5]), u = a(u, y[T + 6]), M = a(M, y[T + 7]), e(), y[T + 0] = L, y[T + 1] = l, y[T + 2] = q, y[T + 3] = g, y[T + 4] = p, y[T + 5] = x, y[T +
        6] = u, y[T + 7] = M;
    G();
    b = 256
  }

  function G(d) {
    var e, l;
    for (d = d && "number" === typeof d ? Math.abs(Math.floor(d)) : 1; d--;)
      for (h = a(h, 1), n = a(n, h), e = 0; 256 > e; e++) {
        switch (e & 3) {
          case 0:
            c ^= c << 13;
            break;
          case 1:
            c ^= c >>> 6;
            break;
          case 2:
            c ^= c << 2;
            break;
          case 3:
            c ^= c >>> 16
        }
        c = a(y[e + 128 & 255], c);
        var q = y[e];
        y[e] = l = a(y[q >>> 2 & 255], a(c, n));
        k[e] = n = a(y[l >>> 10 & 255], q)
      }
  }

  function r() {
    b-- || (G(), b = 255);
    return k[b]
  }
  var y = Array(256),
    c = 0,
    n = 0,
    h = 0,
    k = Array(256),
    b = 0;
  t(4294967295 * Math.random());
  return {
    reset: J,
    seed: t,
    prng: G,
    rand: r,
    random: function() {
      return (67108864 *
        (r() >>> 5) + (r() >>> 6)) / 9007199254740992
    },
    internals: function(d) {
      var e = {
        a: c,
        b: n,
        c: h,
        m: y.slice(),
        r: k.slice(),
        g: b
      };
      d && (c = d.a, n = d.b, h = d.c, y = d.m.slice(), k = d.r.slice(), b = d.g);
      return e
    }
  }
}();
var mathlib = function() {
  function a(f, m, D, z, H, F) {
    var P = f[m];
    f[m] = f[H] ^ F;
    f[H] = f[z] ^ F;
    f[z] = f[D] ^ F;
    f[D] = P ^ F
  }

  function J(f) {
    for (var m = arguments.length - 1, D = f[arguments[m]]; 1 < m; m--) f[arguments[m]] = f[arguments[m - 1]];
    f[arguments[1]] = D;
    return J
  }

  function t(f, m, D, z) {
    D = D || 1;
    for (var H = m.length, F = [], P = 0; P < H; P++) F[P] = f[m[P]];
    for (P = 0; P < H; P++) {
      var C = (P + D) % H;
      f[m[C]] = F[P];
      z && (f[m[C]] += z[C] - z[P] + z.at(-1))
    }
    return t
  }

  function G(f, m) {
    return f[m >> 3] >> ((m & 7) << 2) & 15
  }

  function r(f, m, D, z) {
    var H = 0;
    0 > z && (m <<= 1);
    if (16 <= D) {
      f[D - 1] = 0;
      for (var F = D - 2; 0 <= F; F--) {
        f[F] = m % (D - F);
        H ^= f[F];
        m = ~~(m / (D - F));
        for (var P = F + 1; P < D; P++) f[P] >= f[F] && f[P]++
      }
      0 > z && 0 != (H & 1) && (m = f[D - 1], f[D - 1] = f[D - 2], f[D - 2] = m);
      return f
    }
    P = 1985229328;
    var C = 4275878552;
    for (F = 0; F < D - 1; F++) {
      var E = T[D - 1 - F],
        O = m / E;
      m %= E;
      H ^= O;
      O <<= 2;
      32 <= O ? (O -= 32, f[F] = C >> O & 15, E = (1 << O) - 1, C = (C & E) + (C >> 4 & ~E)) : (f[F] = P >> O & 15, E = (1 << O) - 1, P = (P & E) + (P >>> 4 & ~E) + (C << 28), C >>= 4)
    }
    0 > z && 0 != (H & 1) ? (f[D - 1] = f[D - 2], f[D - 2] = P & 15) : f[D - 1] = P & 15;
    return f
  }

  function y(f, m, D) {
    m = m || f.length;
    var z = 0;
    if (16 <= m) {
      for (var H = 0; H < m - 1; H++) {
        z *= m - H;
        for (var F = H + 1; F < m; F++) f[F] < f[H] && z++
      }
      return 0 > D ? z >> 1 : z
    }
    F = 1985229328;
    var P = 4275878552;
    for (H = 0; H < m - 1; H++) {
      var C = f[H] << 2;
      z *= m - H;
      32 <= C ? (z += P >> C - 32 & 15, P -= 286331152 << C - 32) : (z += F >> C & 15, P -= 286331153, F -= 286331152 << C)
    }
    return 0 > D ? z >> 1 : z
  }

  function c(f, m) {
    var D;
    var z = 0;
    for (D = m - 2; 0 <= D; --D) z ^= f % (m - D), f = ~~(f / (m - D));
    return z & 1
  }

  function n(f, m, D) {
    var z = Math.abs(D);
    D = 0 > D ? 0 : f[0] % z;
    for (--m; 0 < m; m--) D = D * z + f[m] % z;
    return D
  }

  function h(f, m, D, z) {
    for (var H = Math.abs(z), F = H * D, P = 1; P < D; P++) f[P] = m % H, F -= f[P], m = ~~(m / H);
    f[0] = (0 > z ? F : m) %
      H;
    return f
  }

  function k(f) {
    f -= f >> 1 & 1431655765;
    f = (f & 858993459) + (f >> 2 & 858993459);
    return 16843009 * (f + (f >> 4) & 252645135) >> 24
  }

  function b(f, m, D) {
    this.length = m;
    this.evenbase = D;
    if ("p" == f) this.get = function(F) {
      return y(F, this.length, this.evenbase)
    }, this.set = function(F, P) {
      return r(F, P, this.length, this.evenbase)
    };
    else if ("o" == f) this.get = function(F) {
      return n(F, this.length, this.evenbase)
    }, this.set = function(F, P) {
      return h(F, P, this.length, this.evenbase)
    };
    else if ("c" == f) {
      this.cnts = D.slice();
      this.cntn = this.cnts.length;
      this.cums = [0];
      for (f = 1; f <= this.cntn; f++) this.cums[f] = this.cums[f - 1] + D[f - 1];
      m = this.n = this.cums[this.cntn];
      var z = 1;
      for (f = 0; f < this.cntn; f++)
        for (var H = 1; H <= D[f]; H++, m--) z *= m / H;
      this.x = Math.round(z);
      this.get = function(F) {
        for (var P = this.n, C = this.cnts.slice(), E = this.cums, O = -1, Q = 0, ba = 1, ja = 0; ja < P; ja++) {
          var wa = F[ja];
          Q = Q * (P - ja) + k(O & (1 << E[wa]) - 1) * ba;
          ba *= C[wa]--;
          O &= ~(1 << E[wa] + C[wa])
        }
        return Math.round(Q / ba)
      };
      this.set = function(F, P) {
        for (var C = this.n, E = this.cnts.slice(), O = this.x, Q = 0; Q < C; Q++)
          for (var ba = 0; ba < E.length; ba++)
            if (0 !=
              E[ba]) {
              var ja = ~~(O * E[ba] / (C - Q));
              if (P < ja) {
                E[ba]--;
                F[Q] = ba;
                O = ja;
                break
              }
              P -= ja
            } return F
      }
    } else debugger
  }

  function d(f, m, D, z) {
    z = z || 6;
    if ($.isArray(D)) {
      var H = new b(D[1], D[2], D[3]);
      D = D[0];
      for (var F = 0; F < z; F++) {
        f[F] = [];
        for (var P = 0; P < m; P++) {
          var C = H.set([], P);
          D(C, F);
          f[F][P] = H.get(C)
        }
      }
    } else
      for (F = 0; F < z; F++)
        for (f[F] = [], P = 0; P < m; P++) f[F][P] = D(P, F)
  }

  function e() {
    this.ca = [0, 1, 2, 3, 4, 5, 6, 7];
    this.ea = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22];
    this.ori = 0
  }

  function l(f, m, D, z, H, F, P, C) {
    var E = $.isArray(H);
    F = F || 6;
    P = P || 3;
    C = C || 256;
    z = z || 256;
    for (var O = 0, Q = D + 7 >>> 3; O < Q; O++) f[O] = -1;
    $.isArray(m) || (m = [m]);
    for (O = 0; O < m.length; O++) f[m[O] >> 3] ^= 15 << ((m[O] & 7) << 2);
    for (O = m = 0; O <= z; O++) {
      Q = 0;
      var ba = O >= C,
        ja = O + 1 ^ 15,
        wa = ba ? 15 : O,
        Ca = ba ? O : 15,
        sa = 0;
      a: for (; sa < D; sa++, m >>= 4) {
        if (0 == (sa & 7) && (m = f[sa >> 3], !ba && -1 == m)) {
          sa += 7;
          continue
        }
        if ((m & 15) == wa)
          for (var ua = 0; ua < F; ua++)
            for (var Ga = sa, Ha = 0; Ha < P; Ha++) {
              Ga = E ? H[ua][Ga] : H(Ga, ua);
              if (0 > Ga) break;
              if (G(f, Ga) == Ca) {
                ++Q;
                if (ba) {
                  f[sa >> 3] ^= ja << ((sa & 7) << 2);
                  continue a
                }
                f[Ga >> 3] ^= ja << ((Ga & 7) << 2)
              }
            }
      }
      if (0 == Q) break;
      DEBUG && console.log("[prun]",
        Q)
    }
  }

  function q(f, m, D) {
    this.N_STATES = D.length;
    this.N_MOVES = f;
    this.N_POWER = m;
    this.stateParams = D;
    this.coords = [];
    for (f = 0; f < this.N_STATES; f++) m = D[f][1], $.isArray(m) && (this.coords[f] = new b(m[1], m[2], m[3]));
    this.inited = !1
  }

  function g(f, m, D, z, H, F) {
    this.isSolved = f || function() {
      return !0
    };
    this.getPrun = m;
    this.doMove = D;
    this.N_AXIS = z;
    this.N_POWER = H;
    this.ckmv = F || u(z, function(P) {
      return 1 << P
    })
  }

  function p(f, m, D) {
    this.solvedStates = f;
    this.doMove = m;
    this.movesList = [];
    for (var z in D) this.movesList.push([z, D[z]]);
    this.prunTable = {};
    this.toUpdateArr = null;
    this.prunTableSize = 0;
    this.prunDepth = -1;
    this.cost = 0;
    this.MAX_PRUN_SIZE = 1E5
  }

  function x(f) {
    return ~~(X.random() * f)
  }

  function u(f, m) {
    for (var D = [], z = "function" == typeof m, H = 0; H < f; H++) D[H] = z ? m(H) : m;
    return D
  }
  for (var M = [], T = [1], L = 0; 32 > L; ++L) {
    M[L] = [];
    for (var K = 0; 32 > K; ++K) M[L][K] = 0
  }
  for (L = 0; 32 > L; ++L)
    for (M[L][0] = M[L][L] = 1, T[L + 1] = T[L] * (L + 1), K = 1; K < L; ++K) M[L][K] = M[L - 1][K - 1] + M[L - 1][K];
  var I = [];
  for (L = 0; 24 > L; L++) {
    var w = [],
      B = [],
      A = [];
    I[L] = [];
    r(w, L, 4);
    for (K = 0; 24 > K; K++) {
      r(B, K, 4);
      for (var N = 0; 4 > N; N++) A[N] =
        w[B[N]];
      I[L][K] = y(A, 4)
    }
  }
  e.SOLVED = new e;
  e.EdgeMult = function(f, m, D) {
    for (var z = 0; 12 > z; z++) D.ea[z] = f.ea[m.ea[z] >> 1] ^ m.ea[z] & 1
  };
  e.CornMult = function(f, m, D) {
    for (var z = 0; 8 > z; z++) D.ca[z] = f.ca[m.ca[z] & 7] & 7 | ((f.ca[m.ca[z] & 7] >> 3) + (m.ca[z] >> 3)) % 3 << 3
  };
  e.CubeMult = function(f, m, D) {
    e.CornMult(f, m, D);
    e.EdgeMult(f, m, D)
  };
  e.CentMult = function(f, m, D) {
    D.ct = [];
    for (var z = 0; 6 > z; z++) D.ct[z] = f.ct[m.ct[z]]
  };
  e.prototype.init = function(f, m) {
    this.ca = f.slice();
    this.ea = m.slice();
    return this
  };
  e.prototype.hashCode = function() {
    for (var f =
        0, m = 0; 20 > m; m++) f = 0 | 31 * f + (12 > m ? this.ea[m] : this.ca[m - 12]);
    return f
  };
  e.prototype.isEqual = function(f) {
    f = f || e.SOLVED;
    for (var m = 0; 8 > m; m++)
      if (this.ca[m] != f.ca[m]) return !1;
    for (m = 0; 12 > m; m++)
      if (this.ea[m] != f.ea[m]) return !1;
    return !0
  };
  e.cFacelet = [
    [8, 9, 20],
    [6, 18, 38],
    [0, 36, 47],
    [2, 45, 11],
    [29, 26, 15],
    [27, 44, 24],
    [33, 53, 42],
    [35, 17, 51]
  ];
  e.eFacelet = [
    [5, 10],
    [7, 19],
    [3, 37],
    [1, 46],
    [32, 16],
    [28, 25],
    [30, 43],
    [34, 52],
    [23, 12],
    [21, 41],
    [50, 39],
    [48, 14]
  ];
  e.ctFacelet = [4, 13, 22, 31, 40, 49];
  e.faceMap = function() {
    for (var f = [], m = 0; 8 > m; m++)
      for (var D =
          0; 3 > D; D++) f[e.cFacelet[m][D]] = [0, m, D];
    for (m = 0; 12 > m; m++)
      for (D = 0; 2 > D; D++) f[e.eFacelet[m][D]] = [1, m, D];
    return f
  }();
  e.prototype.toPerm = function(f, m, D, z) {
    f = f || e.cFacelet;
    m = m || e.eFacelet;
    D = D || e.ctFacelet;
    for (var H = [], F = 0; 54 > F; F++) H[F] = F;
    var P = this;
    if (z && P.ori)
      for (P = new e, z = e.rotCube[e.rotMulI[0][this.ori]], e.CubeMult(this, z, P), F = 0; 6 > F; F++) H[D[F]] = D[z.ct[F]];
    for (var C = 0; 8 > C; C++)
      for (D = P.ca[C] & 7, F = P.ca[C] >> 3, z = 0; 3 > z; z++) H[f[C][(z + F) % 3]] = f[D][z];
    for (f = 0; 12 > f; f++)
      for (D = P.ea[f] >> 1, F = P.ea[f] & 1, z = 0; 2 > z; z++) H[m[f][(z +
        F) % 2]] = m[D][z];
    return H
  };
  e.prototype.toFaceCube = function(f, m, D, z) {
    f = this.toPerm(f, m, D, z);
    m = [];
    for (D = 0; 54 > D; D++) m[D] = "URFDLB" [~~(f[D] / 9)];
    return m.join("")
  };
  e.prototype.prettyString = function(f) {
    var m = this.toFaceCube(null, null, null, f);
    return "        U0U1U2\n        U3U4U5\n        U6U7U8\nL0L1L2  F0F1F2  R0R1R2  B0B1B2\nL3L4L5  F3F4F5  R3R4R5  B3B4B5\nL6L7L8  F6F7F8  R6R7R8  B6B7B8\n        D0D1D2\n        D3D4D5\n        D6D7D8\n".replace(/[URFDLB][0-8]/g, function(D) {
      var z = "URFDLB".indexOf(D[0]);
      return m[9 *
        z + ~~D[1]] + " "
    })
  };
  e.prototype.invFrom = function(f) {
    for (var m = 0; 12 > m; m++) this.ea[f.ea[m] >> 1] = m << 1 | f.ea[m] & 1;
    for (m = 0; 8 > m; m++) this.ca[f.ca[m] & 7] = m | 32 >> (f.ca[m] >> 3) & 24;
    return this
  };
  e.prototype.fromFacelet = function(f, m, D) {
    m = m || e.cFacelet;
    D = D || e.eFacelet;
    for (var z = 0, H = [], F = f[4] + f[13] + f[22] + f[31] + f[40] + f[49], P = 0; 54 > P; ++P) {
      H[P] = F.indexOf(f[P]);
      if (-1 == H[P]) return -1;
      z += 1 << (H[P] << 2)
    }
    if (10066329 != z) return -1;
    var C;
    for (P = 0; 8 > P; ++P) {
      for (C = 0; 3 > C && 0 != H[m[P][C]] && 3 != H[m[P][C]]; ++C);
      f = H[m[P][(C + 1) % 3]];
      z = H[m[P][(C + 2) %
        3
      ]];
      for (F = 0; 8 > F; ++F)
        if (f == ~~(m[F][1] / 9) && z == ~~(m[F][2] / 9)) {
          this.ca[P] = F | C % 3 << 3;
          break
        }
    }
    for (P = 0; 12 > P; ++P)
      for (F = 0; 12 > F; ++F) {
        if (H[D[P][0]] == ~~(D[F][0] / 9) && H[D[P][1]] == ~~(D[F][1] / 9)) {
          this.ea[P] = F << 1;
          break
        }
        if (H[D[P][0]] == ~~(D[F][1] / 9) && H[D[P][1]] == ~~(D[F][0] / 9)) {
          this.ea[P] = F << 1 | 1;
          break
        }
      }
    return this
  };
  e.prototype.verify = function() {
    for (var f = 0, m = 0, D = [], z = 0; 12 > z; z++) f |= 256 << (this.ea[z] >> 1), m ^= this.ea[z] & 1, D.push(this.ea[z] >> 1);
    z = [];
    for (var H = 0; 8 > H; H++) f |= 1 << (this.ca[H] & 7), m += this.ca[H] >> 3 << 1, z.push(this.ca[H] &
      7);
    return 1048575 != f || 0 != m % 6 || c(y(D, 12), 12) != c(y(z, 8), 8) ? -1 : 0
  };
  e.moveCube = function() {
    for (var f = [], m = 0; 18 > m; m++) f[m] = new e;
    f[0].init([3, 0, 1, 2, 4, 5, 6, 7], [6, 0, 2, 4, 8, 10, 12, 14, 16, 18, 20, 22]);
    f[3].init([20, 1, 2, 8, 15, 5, 6, 19], [16, 2, 4, 6, 22, 10, 12, 14, 8, 18, 20, 0]);
    f[6].init([9, 21, 2, 3, 16, 12, 6, 7], [0, 19, 4, 6, 8, 17, 12, 14, 3, 11, 20, 22]);
    f[9].init([0, 1, 2, 3, 5, 6, 7, 4], [0, 2, 4, 6, 10, 12, 14, 8, 16, 18, 20, 22]);
    f[12].init([0, 10, 22, 3, 4, 17, 13, 7], [0, 2, 20, 6, 8, 10, 18, 14, 16, 4, 12, 22]);
    f[15].init([0, 1, 11, 23, 4, 5, 18, 14], [0, 2, 4, 23, 8, 10, 12, 21, 16, 18,
      7, 15
    ]);
    for (m = 0; 18 > m; m += 3)
      for (var D = 0; 2 > D; D++) e.CubeMult(f[m + D], f[m], f[m + D + 1]);
    return f
  }();
  e.rotCube = function() {
    var f = (new e).init([3, 0, 1, 2, 7, 4, 5, 6], [6, 0, 2, 4, 14, 8, 10, 12, 23, 17, 19, 21]);
    f.ct = [0, 5, 1, 3, 2, 4];
    var m = (new e).init([5, 4, 7, 6, 1, 0, 3, 2], [12, 10, 8, 14, 4, 2, 0, 6, 18, 16, 22, 20]);
    m.ct = [3, 4, 2, 0, 1, 5];
    var D = (new e).init([8, 20, 13, 17, 19, 15, 22, 10], [3, 16, 11, 18, 7, 22, 15, 20, 1, 9, 13, 5]);
    D.ct = [2, 0, 1, 5, 3, 4];
    var z = new e;
    z.ct = [0, 1, 2, 3, 4, 5];
    for (var H = new e, F = [], P = 0; 24 > P; P++) F[P] = (new e).init(z.ca, z.ea), F[P].ct = z.ct.slice(),
      e.CubeMult(z, f, H), e.CentMult(z, f, H), z.init(H.ca, H.ea), z.ct = H.ct.slice(), 3 == P % 4 && (e.CubeMult(z, m, H), e.CentMult(z, m, H), z.init(H.ca, H.ea), z.ct = H.ct.slice()), 7 == P % 8 && (e.CubeMult(z, D, H), e.CentMult(z, D, H), z.init(H.ca, H.ea), z.ct = H.ct.slice());
    f = [];
    m = [];
    D = [];
    var C = [],
      E = [];
    for (P = 0; 24 > P; P++) m[P] = F[P].hashCode(), D[P] = [], C[P] = [], E[P] = [];
    for (P = 0; 18 > P; P++) f[P] = e.moveCube[P].hashCode();
    for (P = 0; 24 > P; P++)
      for (var O = 0; 24 > O; O++) {
        e.CubeMult(F[P], F[O], z);
        var Q = m.indexOf(z.hashCode());
        D[P][O] = Q;
        C[Q][O] = P
      }
    for (P = 0; 24 > P; P++)
      for (O =
        0; 18 > O; O++) e.CubeMult(F[C[0][P]], e.moveCube[O], z), e.CubeMult(z, F[P], H), Q = f.indexOf(H.hashCode()), E[P][O] = Q;
    e.rotMult = D;
    e.rotMulI = C;
    e.rotMulM = E;
    e.rot2str = ";y';y2;y;z2;y' z2;y2 z2;y z2;y' x';y2 x';y x';x';y' x;y2 x;y x;x;y z;z;y' z;y2 z;y' z';y2 z';y z';z'".split(";");
    return F
  }();
  e.prototype.edgeCycles = function() {
    for (var f = [], m = [0, 0, 0], D = 0, z = !1, H = 0; 12 > H; ++H)
      if (!f[H]) {
        var F = -1,
          P = !1,
          C = H;
        do f[C] = !0, ++F, P ^= this.ea[C] & 1, C = this.ea[C] >> 1; while (C != H);
        D += F >> 1;
        F & 1 && (z = !z, ++D);
        P && (0 == F ? ++m[0] : F & 1 ? m[2] ^= 1 : ++m[1])
      } m[1] +=
      m[2];
    D = m[0] < m[1] ? D + (m[0] + m[1] >> 1) : D + (m[1] + [0, 2, 3, 5, 6, 8, 9][m[0] - m[1] >> 1]);
    return D - z
  };
  var R = /^\s*([URFDLB]w?|[EMSyxz]|2-2[URFDLB]w)(['2]?)(@\d+)?\s*$/,
    W = new e;
  e.prototype.selfMoveStr = function(f, m) {
    var D = R.exec(f);
    if (D) {
      var z = D[1];
      f = "2'".indexOf(D[2] || "-") + 2;
      m && (f = 4 - f);
      D[3] && (this.tstamp = ~~D[3].slice(1));
      this.ori = this.ori || 0;
      m = "URFDLB".indexOf(z);
      if (-1 != m) return D = e.rotMulM[this.ori][3 * m + f % 4 - 1], e.CubeMult(this, e.moveCube[D], W), this.init(W.ca, W.ea), D;
      m = "UwRwFwDwLwBw".indexOf(z);
      if (-1 != m) {
        m >>= 1;
        D = e.rotMulM[this.ori][(m +
          3) % 6 * 3 + f % 4 - 1];
        e.CubeMult(this, e.moveCube[D], W);
        this.init(W.ca, W.ea);
        m = [3, 15, 17, 1, 11, 23][m];
        for (z = 0; z < f; z++) this.ori = e.rotMult[m][this.ori];
        return D
      }
      m = "2-2Uw 2-2Rw 2-2Fw 2-2Dw 2-2Lw 2-2Bw".split(" ").indexOf(z); - 1 == m && (m = [null, null, "S", "E", "M", null].indexOf(z));
      if (-1 != m) {
        z = (m + 3) % 6 * 3 + f % 4 - 1;
        D = e.rotMulM[this.ori][3 * m + (4 - f) % 4 - 1];
        e.CubeMult(this, e.moveCube[D], W);
        this.init(W.ca, W.ea);
        z = e.rotMulM[this.ori][z];
        e.CubeMult(this, e.moveCube[z], W);
        this.init(W.ca, W.ea);
        m = [3, 15, 17, 1, 11, 23][m];
        for (z = 0; z < f; z++) this.ori =
          e.rotMult[m][this.ori];
        return D + 18
      }
      m = "yxz".indexOf(z);
      if (-1 != m)
        for (m = [3, 15, 17][m], z = 0; z < f; z++) this.ori = e.rotMult[m][this.ori]
    }
  };
  e.prototype.selfConj = function(f) {
    void 0 === f && (f = this.ori);
    0 != f && (e.CubeMult(e.rotCube[f], this, W), e.CubeMult(W, e.rotCube[e.rotMulI[0][f]], this), this.ori = e.rotMulI[this.ori][f] || 0)
  };
  L = function() {
    var f = [11, 8, 9, 10, 6, 7, 4, 5, 1, 2, 3, 0],
      m = [
        [5, 1, 2, 3, 4],
        [10, 6, 2, 0, 5],
        [6, 7, 3, 0, 1],
        [7, 8, 4, 0, 2],
        [8, 9, 5, 0, 3],
        [9, 10, 1, 0, 4],
        [11, 7, 2, 1, 10],
        [11, 8, 3, 2, 6],
        [11, 9, 4, 3, 7],
        [11, 10, 5, 4, 8],
        [11, 6, 1, 5, 9],
        [6,
          10, 9, 8, 7
        ]
      ];
    return {
      doMove: function(D, z, H, F) {
        H = (H % 5 + 5) % 5;
        if (0 != H) {
          for (var P = 11 * z, C = [
              [],
              [],
              [],
              [],
              []
            ], E = 0; 5 > E; E++) {
            var O = m[z][E],
              Q = m[O].indexOf(z);
            0 != F && 1 != F || C[E].push(P + E, P + E + 5, 11 * O + Q % 5 + 5, 11 * O + Q % 5, 11 * O + (Q + 1) % 5);
            if (1 == F || 2 == F) {
              C[E].push(11 * O + 10);
              for (var ba = 1; 5 > ba; ba++) C[E].push(11 * O + (Q + ba) % 5 + 5);
              for (ba = 2; 5 > ba; ba++) C[E].push(11 * O + (Q + ba) % 5);
              ba = 4 - E;
              var ja = f[z];
              O = m[ja][ba];
              Q = m[O].indexOf(ja);
              C[E].push(11 * ja + ba, 11 * ja + ba + 5, 11 * O + 10);
              for (ba = 0; 5 > ba; ba++) C[E].push(11 * O + (Q + ba) % 5 + 5, 11 * O + (Q + ba) % 5)
            }
          }
          for (E = 0; E < C[0].length; E++) mathlib.acycle(D,
            [C[0][E], C[1][E], C[2][E], C[3][E], C[4][E]], H)
        }
      },
      oppFace: f,
      adjFaces: m
    }
  }();
  K = q.prototype;
  K.init = function() {
    var f = this;
    if (!this.inited) {
      this.move = [];
      this.prun = [];
      for (var m = 0; m < this.N_STATES; m++) {
        var D = this.stateParams[m],
          z = D[0],
          H = D[1],
          F = D[2],
          P = D[3];
        D = D[4];
        this.move[m] = [];
        this.prun[m] = [];
        d(this.move[m], F, H, this.N_MOVES);
        l(this.prun[m], z, F, P, this.move[m], this.N_MOVES, this.N_POWER, D)
      }
      this.solv = new g(null, function(C) {
        for (var E = 0, O = 0; O < f.N_STATES; O++) E = Math.max(E, G(f.prun[O], C[O]));
        return E
      }, function(C, E) {
        for (var O =
            0; O < f.N_STATES; O++) C[O] = f.move[O][E][C[O]];
        return C
      }, this.N_MOVES, this.N_POWER);
      this.inited = !0
    }
  };
  K.search = function(f, m, D) {
    D = D || 99;
    this.inited || this.init();
    return this.sol = this.solv.solve(f, m, D)
  };
  K.toStr = function(f, m, D) {
    return f.map(function(z) {
      return m[z[0]] + D[z[1]]
    }).join(" ").replace(/ +/g, " ")
  };
  K = g.prototype;
  K.solve = function(f, m, D, z, H) {
    f = this.solveMulti([f], m, D, z, H);
    return null == f ? null : f[0]
  };
  K.solveMulti = function(f, m, D, z, H) {
    this.sidx = 0;
    this.sol = [];
    this.length = m;
    this.idxs = f;
    return this.nextMulti(D,
      z, H)
  };
  K.next = function(f, m, D) {
    f = this.nextMulti(f, m, D);
    return null == f ? null : f[0]
  };
  K.nextMulti = function(f, m, D) {
    this.cost = (D || 1E9) + 1;
    for (this.callback = m || function() {
        return !0
      }; this.length <= f; this.length++) {
      for (; this.sidx < this.idxs.length; this.sidx++)
        if (0 == this.idaSearch(this.idxs[this.sidx], this.length, 0, -1, this.sol)) return 0 >= this.cost ? null : [this.sol, this.sidx];
      this.sidx = 0
    }
    return null
  };
  K.idaSearch = function(f, m, D, z, H) {
    if (0 >= --this.cost) return 0;
    var F = this.getPrun(f);
    if (F > m) return F > m + 1 ? 2 : 1;
    if (0 == m) return this.isSolved(f) &&
      this.callback(H, this.sidx) ? 0 : 1;
    if (0 == F && 1 == m && this.isSolved(f)) return 1;
    for (F = H.length > D ? H[D][0] : 0; F < this.N_AXIS; F++)
      if (!(this.ckmv[z] >> F & 1))
        for (var P = $.isArray(f) ? f.slice() : f, C = H.length > D ? H[D][1] : 0; C < this.N_POWER; C++) {
          P = this.doMove(P, F, C);
          if (null == P) break;
          H[D] = [F, C];
          var E = this.idaSearch(P, m - 1, D + 1, F, H);
          if (0 == E) return 0;
          H.pop();
          if (2 == E) break
        }
    return 1
  };
  K = p.prototype;
  K.updatePrun = function(f) {
    f = void 0 === f ? this.prunDepth + 1 : f;
    for (var m = this.prunDepth + 1; m <= f; m++) {
      if (this.prevSize >= this.MAX_PRUN_SIZE) {
        DEBUG &&
          console.log("[gSolver] skipPrun", m, this.prunTableSize);
        break
      }
      var D = +new Date;
      if (1 > m)
        for (var z = this.prevSize = 0; z < this.solvedStates.length; z++) {
          var H = this.solvedStates[z];
          H in this.prunTable || (this.prunTable[H] = m, this.prunTableSize++)
        } else this.updatePrunBFS(m - 1);
      if (0 == this.cost) break;
      this.prunDepth = m;
      DEBUG && console.log("[gSolver] updatePrun", m, this.prunTableSize - this.prevSize, +new Date - D);
      this.prevSize = this.prunTableSize
    }
  };
  K.updatePrunBFS = function(f) {
    if (null == this.toUpdateArr) {
      this.toUpdateArr = [];
      for (var m in this.prunTable) this.prunTable[m] == f && this.toUpdateArr.push(m)
    }
    for (; 0 != this.toUpdateArr.length;) {
      m = this.toUpdateArr.pop();
      for (var D = 0; D < this.movesList.length; D++) {
        var z = this.doMove(m, this.movesList[D][0]);
        !z || z in this.prunTable || (this.prunTable[z] = f + 1, this.prunTableSize++)
      }
      if (0 <= this.cost) {
        if (0 == this.cost) return;
        this.cost--
      }
    }
    this.toUpdateArr = null
  };
  K.search = function(f, m, D) {
    this.sol = [];
    this.subOpt = !1;
    this.state = f;
    this.visited = {};
    this.maxl = m || 0;
    return this.searchNext(D)
  };
  K.searchNext = function(f,
    m) {
    f = f + 1 || 99;
    this.prevSolStr = this.solArr ? this.solArr.join(",") : null;
    this.solArr = null;
    for (this.cost = m || -1; this.maxl < f; this.maxl++) {
      this.updatePrun(Math.ceil(this.maxl / 2));
      if (0 == this.cost) return null;
      if (this.idaSearch(this.state, this.maxl, null, 0)) break
    }
    return this.solArr
  };
  K.getPruning = function(f) {
    f = this.prunTable[f];
    return void 0 === f ? this.prunDepth + 1 : f
  };
  K.idaSearch = function(f, m, D, z) {
    var H = this;
    if (this.getPruning(f) > m) return !1;
    if (0 == m) {
      if (-1 == this.solvedStates.indexOf(f)) return !1;
      f = this.sol.map(function(O) {
        return H.movesList[O][0]
      });
      this.subOpt = !0;
      if (f.join(",") == this.prevSolStr) return !1;
      this.solArr = f;
      return !0
    }
    if (!this.subOpt) {
      if (f in this.visited && this.visited[f] < z) return !1;
      this.visited[f] = z
    }
    if (0 <= this.cost) {
      if (0 == this.cost) return !0;
      this.cost--
    }
    var F = null == D ? "" : this.movesList[D][0];
    D = null == D ? -1 : this.movesList[D][1];
    for (var P = this.sol[z] || 0; P < this.movesList.length; P++) {
      var C = this.movesList[P],
        E = C[1] ^ D;
      C = C[0];
      if (!(0 == E || 0 == (E & 15) && C <= F) && (E = this.doMove(f, C)) && E != f) {
        this.sol[z] = P;
        if (this.idaSearch(E, m - 1, P, z + 1)) return !0;
        this.sol.pop()
      }
    }
    return !1
  };
  var X = function() {
      function f(F, P) {
        if (P && (P != z || D > F)) {
          for (var C = [], E = 0; E < P.length; E++) C[E] = P.charCodeAt(E);
          isaac.seed(C);
          m = isaac.random;
          D = 0;
          z = P
        }
        for (; D < F;) m(), D++
      }
      var m, D, z, H = "" + (new Date).getTime();
      "undefined" != typeof crypto && crypto.getRandomValues ? (H = String.fromCharCode.apply(null, crypto.getRandomValues(new Uint16Array(256))), DEBUG && console.log("[mathlib] use crypto seed", H)) : DEBUG && console.log("[mathlib] use datetime seed", H);
      f(256, H);
      return {
        random: function() {
          D++;
          return m()
        },
        getSeed: function() {
          return [D,
            z
          ]
        },
        setSeed: f
      }
    }(),
    S = /^\s*(\d+)-(\d+)-(\d+) (\d+):(\d+):(\d+)\s*$/;
  Math.TAU = 2 * Math.PI;
  return {
    Cnk: M,
    fact: T,
    bitCount: k,
    getPruning: G,
    setNOri: h,
    getNOri: n,
    setNPerm: r,
    getNPerm: y,
    getNParity: c,
    permMul4: I,
    Coord: b,
    createMove: d,
    createMoveHash: function(f, m, D, z) {
      var H = [f],
        F = {},
        P = [];
      F[D(f)] = 0;
      P[0] = 1;
      f = [];
      for (var C = 0; C < m.length; C++) f[C] = [];
      for (var E = +new Date, O = 0; O < H.length; O++) {
        O == P.at(-1) && P.push(H.length);
        9999 == O % 1E4 && DEBUG && console.log(O, "states scanned, tt=", +new Date - E);
        var Q = H[O];
        for (C = 0; C < m.length; C++) {
          var ba =
            z(Q, m[C]);
          if (ba) {
            var ja = D(ba);
            ja in F || (F[ja] = H.length, H.push(ba));
            f[C][O] = F[ja]
          } else f[C][O] = -1
        }
      }
      DEBUG && console.log("[move hash] " + H.length + " states generated, tt=", +new Date - E, JSON.stringify(P));
      return [f, F]
    },
    edgeMove: function(f, m) {
      0 == m ? a(f, 0, 7, 8, 4, 1) : 1 == m ? a(f, 3, 6, 11, 7, 0) : 2 == m ? a(f, 0, 1, 2, 3, 0) : 3 == m ? a(f, 2, 5, 10, 6, 1) : 4 == m ? a(f, 1, 4, 9, 5, 0) : 5 == m && a(f, 11, 10, 9, 8, 0)
    },
    circle: J,
    circleOri: a,
    acycle: t,
    createPrun: l,
    CubieCube: e,
    minx: L,
    SOLVED_FACELET: "UUUUUUUUURRRRRRRRRFFFFFFFFFDDDDDDDDDLLLLLLLLLBBBBBBBBB",
    fillFacelet: function(f,
      m, D, z, H) {
      for (var F = 0; F < f.length; F++) {
        var P = f[F],
          C = void 0 === D[F] ? F : D[F];
        if ("number" == typeof P) m[P] = ~~(f[C] / H);
        else
          for (var E = z[F] || 0, O = 0; O < P.length; O++) m[P[(O + E) % P.length]] = ~~(f[C][O] / H)
      }
    },
    detectFacelet: function(f, m, D, z, H) {
      for (var F = 0; F < f.length; F++) {
        var P = f[F].length,
          C = 0;
        a: for (; C < f.length + 1; C++) {
          if (C == f.length) return -1;
          if (f[C].length == P)
            for (var E = 0; E < P; E++) {
              for (var O = !0, Q = 0; Q < P; Q++)
                if (~~(f[C][Q] / H) != m[f[F][(Q + E) % P]]) {
                  O = !1;
                  break
                } if (O) {
                D[F] = C;
                z[F] = E;
                break a
              }
            }
        }
      }
      return 0
    },
    rn: x,
    rndEl: function(f) {
      return f[~~(X.random() *
        f.length)]
    },
    rndProb: function(f) {
      for (var m = 0, D = 0, z = 0; z < f.length; z++) 0 != f[z] && (X.random() < f[z] / (m + f[z]) && (D = z), m += f[z]);
      return D
    },
    rndHit: function(f) {
      return X.random() < f
    },
    time2str: function(f, m) {
      if (!f) return "N/A";
      f = new Date(1E3 * f);
      return (m || "%Y-%M-%D %h:%m:%s").replace("%Y", f.getFullYear()).replace("%M", ("0" + (f.getMonth() + 1)).slice(-2)).replace("%D", ("0" + f.getDate()).slice(-2)).replace("%h", ("0" + f.getHours()).slice(-2)).replace("%m", ("0" + f.getMinutes()).slice(-2)).replace("%s", ("0" + f.getSeconds()).slice(-2)).replace("%S",
        ("00" + f.getMilliseconds()).slice(-3))
    },
    str2time: function(f) {
      f = S.exec(f);
      if (!f) return null;
      var m = new Date(1970, 0, 1);
      m.setFullYear(~~f[1]);
      m.setMonth(~~f[2] - 1);
      m.setDate(~~f[3]);
      m.setHours(~~f[4]);
      m.setMinutes(~~f[5]);
      m.setSeconds(~~f[6]);
      return ~~(m.getTime() / 1E3)
    },
    obj2str: function(f) {
      return "string" == typeof f ? f : JSON.stringify(f)
    },
    str2obj: function(f) {
      return "string" != typeof f ? f : JSON.parse(f)
    },
    valuedArray: u,
    idxArray: function(f, m) {
      return f.map(function(D) {
        return D[m]
      })
    },
    Solver: q,
    Searcher: g,
    rndPerm: function(f,
      m) {
      for (var D = 0, z = [], H = 0; H < f; H++) z[H] = H;
      for (H = 0; H < f - 1; H++) {
        var F = x(f - H);
        J(z, H, H + F);
        D ^= 0 != F
      }
      m && D && J(z, 0, 1);
      return z
    },
    permOriMult: function(f, m, D, z, H, F, P) {
      for (var C = 0; C < m.length; C++) P && (F[C] = (z[m[C]] + H[C]) % P), D[C] = f[m[C]]
    },
    gSolver: p,
    getSeed: X.getSeed,
    setSeed: X.setSeed
  }
}();
var grouplib = function(a) {
  function J(c, n) {
    for (var h = [], k = 0; k < c.length; k++) h[k] = n[c[k]];
    return h
  }

  function t(c) {
    for (var n = [], h = 0; h < c.length; h++) n[c[h]] = h;
    return n
  }

  function G(c, n) {
    if (c.sgs) this.copy(c);
    else {
      this.sgs = [];
      this.sgsi = [];
      this.t2i = [];
      this.i2t = [];
      this.keyIdx = [];
      this.Tk = [];
      this.e = [];
      for (var h = c[0].length, k = 0; k < h; k++) this.e[k] = k;
      for (k = 0; k < h; k++) this.sgs.push([]), this.sgsi.push([]), this.t2i.push([]), this.i2t.push([k]), this.Tk.push([]), this.sgs[k][k] = this.e, this.sgsi[k][k] = this.e, this.t2i[k][k] =
        0;
      this.extend(c, n)
    }
  }

  function r(c) {
    this.gens = c;
    this.glen = c.length;
    this.trieNodes = [null];
    this.trieNodes.push([]);
    this.skipSeqs = []
  }

  function y(c, n, h) {
    this.genG = c;
    this.genH = n;
    this.genM = h;
    if (!n) {
      n = [];
      for (h = 0; h < c[0].length; h++) n[h] = h;
      this.genH = [n]
    }
  }
  G.prototype.extend = function(c, n) {
    for (var h = 0; h < c.length; h++) {
      var k = c[h];
      n && (k = J(J(t(n), k), n));
      0 > this.isMember(k) && this.knutha(this.e.length - 1, k)
    }
  };
  G.prototype.copy = function(c) {
    this.sgs = [];
    this.sgsi = [];
    this.t2i = [];
    this.i2t = [];
    this.keyIdx = c.keyIdx.slice();
    this.Tk = [];
    this.e = c.e;
    for (var n = this.e.length, h = 0; h < n; h++) this.sgs[h] = c.sgs[h].slice(), this.sgsi[h] = c.sgsi[h].slice(), this.t2i[h] = c.t2i[h].slice(), this.i2t[h] = c.i2t[h].slice(), this.Tk[h] = c.Tk[h].slice()
  };
  G.prototype.toKeyIdx = function(c) {
    var n = [];
    c = c || this.e;
    for (var h = 0; h < this.keyIdx.length; h++) n[h] = c[this.keyIdx[h]];
    return n
  };
  G.prototype.isMember = function(c, n) {
    n = n || 0;
    for (var h = 0, k = [], b = c.length - 1; b >= n; b--) {
      for (var d = c[b], e = 0; e < k.length; e++) d = k[e][d];
      if (d !== b) {
        if (!this.sgs[b][d]) return -1;
        k.push(this.sgsi[b][d])
      }
      h =
        h * this.i2t[b].length + this.t2i[b][d]
    }
    return h
  };
  G.prototype.isSubgroupMemberByKey = function(c, n) {
    for (var h = 0, k = [], b = 0; b < this.keyIdx.length; b++) {
      for (var d = this.keyIdx[b], e = c[b], l = 0; l < k.length; l++) e = k[l][e];
      if (e !== d) {
        if (!n.sgs[d][e]) return -1;
        k.push(n.sgsi[d][e])
      }
      h = h * n.i2t[d].length + n.t2i[d][e]
    }
    return h
  };
  G.prototype.knutha = function(c, n) {
    this.Tk[c].push(n);
    for (var h = 0; h < this.sgs[c].length; h++) this.sgs[c][h] && this.knuthb(c, J(this.sgs[c][h], n))
  };
  G.prototype.knuthb = function(c, n) {
    var h = n[c];
    if (this.sgs[c][h]) n =
      J(n, this.sgsi[c][h]), 0 > this.isMember(n) && this.knutha(c - 1, n);
    else
      for (this.sgs[c][h] = n, this.sgsi[c][h] = t(n), this.t2i[c][h] = this.i2t[c].length, this.i2t[c].push(h), 2 == this.i2t[c].length && (this.keyIdx.push(c), this.keyIdx.sort(function(k, b) {
          return b - k
        })), h = 0; h < this.Tk[c].length; h++) this.knuthb(c, J(n, this.Tk[c][h]))
  };
  G.prototype.size = function(c) {
    for (var n = this.sgs.length, h = c ? BigInt(1) : 1, k = 0; k < n; k++) h *= c ? BigInt(this.i2t[k].length) : this.i2t[k].length;
    return h
  };
  G.prototype.minElem = function(c, n) {
    c = t(c);
    for (n =
      0; n < this.keyIdx.length; n++) {
      for (var h = this.keyIdx[n], k = c[h], b = h, d = 1; d < this.i2t[h].length; d++) {
        var e = this.i2t[h][d];
        c[e] > k && (k = c[e], b = e)
      }
      b !== h && (c = J(this.sgs[h][b], c))
    }
    return t(c)
  };
  G.prototype.listCoset = function(c) {
    var n = [this.e.slice()],
      h = 1,
      k = this.keyIdx.length - 1;
    a: for (; 0 <= k; k--) {
      var b = this.keyIdx[k];
      if (this.i2t[b].length != c.i2t[b].length) {
        h *= this.i2t[b].length;
        h /= c.i2t[b].length;
        for (var d = 0, e = n.length; d < e; d++) {
          var l = n[d],
            q = 1;
          b: for (; q < this.i2t[b].length; q++) {
            for (var g = this.i2t[b][q], p = J(l, this.sgs[b][g]),
                x = 1; x < c.i2t[b].length; x++)
              if (p[c.i2t[b][x]] > g) continue b;
            n.push(p);
            if (n.length >= h) continue a
          }
        }
        console.log("[grouplib] listCoset ERROR, Not enough coset representatives")
      }
    }
    return n
  };
  G.prototype.rndElem = function() {
    for (var c = this.e.slice(), n = this.e.length - 1; 0 <= n; n--) {
      for (var h = 0, k = 0, b = 0; b <= n; b++) this.sgs[n][b] && 1 > a(++h) && (k = b);
      k !== n && (c = J(c, this.sgsi[n][k]))
    }
    return c
  };
  r.prototype.addSkipSeq = function(c) {
    this.skipSeqs.push(c.slice());
    for (var n = 1, h = 0; h < c.length; h++) {
      var k = ~~this.trieNodes[n][c[h]];
      if (-1 ==
        k) break;
      if (h == c.length - 1) {
        this.trieNodes[n][c[h]] = -1;
        break
      }
      if (0 >= k)
        for (k = this.trieNodes.length, this.trieNodes.push([]), this.trieNodes[n][c[h]] = k, n = 0; n < this.glen; n++) this.updateNext(c.slice(0, h + 1).concat(n));
      n = k
    }
  };
  r.prototype.traversalTrie = function(c, n, h) {
    if (!(0 >= c)) {
      for (var k = 0; k < this.glen; k++) n.push(k), this.traversalTrie(~~this.trieNodes[c][k], n, h), n.pop();
      h(c, n)
    }
  };
  r.prototype.updateNext = function(c) {
    for (var n = 1, h = 0; h < c.length; h++) {
      var k = ~~this.trieNodes[n][c[h]];
      0 == k && (k = this.updateNext(c.slice(1,
        h + 1)), k = 0 < k ? ~k : k, this.trieNodes[n][c[h]] = k);
      if (-1 == k) return -1;
      0 > k && (k = ~k);
      n = k
    }
    return n
  };
  r.prototype.refillNext = function() {
    var c = this;
    this.traversalTrie(1, [], function(n, h) {
      for (h = 0; h < c.glen; h++) {
        var k = ~~c.trieNodes[n][h]; - 1 != k && k <= n && (c.trieNodes[n][h] = 0)
      }
    });
    this.traversalTrie(1, [], function(n, h) {
      for (var k = 0; k < c.glen; k++) {
        0 == (k & 31) && (c.trieNodes[n][c.glen + (k >> 5)] = 0);
        var b = ~~c.trieNodes[n][k]; - 1 != b && b <= n && c.updateNext(h.concat(k)); - 1 == ~~c.trieNodes[n][k] && (c.trieNodes[n][c.glen + (k >> 5)] |= 1 << (k & 31))
      }
    })
  };
  r.prototype.countSeq = function(c, n) {
    var h = n ? BigInt(0) : 0,
      k = n ? [BigInt(0), BigInt(1)] : [0, 1];
    n = n ? [BigInt(0), BigInt(1)] : [1];
    for (var b = 0; b < c; b++) {
      for (var d = [], e = h, l = 1; l < this.trieNodes.length; l++) {
        var q = k[l] || h;
        if (0 != q)
          for (var g = 0; g < this.glen; g++) {
            var p = ~~this.trieNodes[l][g]; - 1 != p && (p = 0 > p ? ~p : p, d[p] = (d[p] || h) + q, e += q)
          }
      }
      k = d;
      n.push(e)
    }
    return n
  };
  r.prototype.countSeqMove = function(c, n, h) {
    var k = [];
    k[h * this.trieNodes.length + 1 - 1] = 1;
    h = [];
    for (var b = 0; b < c; b++) {
      for (var d = [], e = [], l = 0, q = 0; q < n[0].length; q++)
        for (var g = 1; g <
          this.trieNodes.length; g++) {
          var p = k[q * this.trieNodes.length + g - 1] || 0;
          if (0 != p)
            for (var x = 0; x < this.glen; x++) {
              var u = ~~this.trieNodes[g][x];
              if (-1 != u) {
                u = 0 > u ? ~u : u;
                var M = n[x][q];
                u = M * this.trieNodes.length + u - 1;
                d[u] = (d[u] || 0) + p;
                e[M] = (e[M] || 0) + p;
                l += p
              }
            }
        }
      k = d;
      h.push(e, l)
    }
    return h
  };
  r.prototype.initTrie = function(c) {
    this.trieNodes = [null];
    this.trieNodes.push([]);
    this.refillNext();
    for (var n = [], h = 0; h < this.gens[0].length; h++) n[h] = h;
    h = new Map;
    for (var k = 0; k <= c; k++) this.searchSkip(n, k, [], 1, h), this.refillNext()
  };
  r.prototype.searchSkip =
    function(c, n, h, k, b) {
      if (0 == n) c = String.fromCharCode.apply(null, c), b.has(c) ? this.addSkipSeq(h) : b.set(c, h.slice());
      else
        for (var d = 0; d < this.glen; d++) {
          var e = this.trieNodes[k][d];
          if (-1 != e) {
            0 > e && (e = ~e);
            var l = J(this.gens[d], c);
            h.push(d);
            this.searchSkip(l, n - 1, h, e, b);
            h.pop()
          }
        }
    };
  y.prototype.permHash = function(c) {
    return String.fromCharCode.apply(null, c)
  };
  y.prototype.midCosetHash = function(c) {
    return null == this.sgsM ? this.sgsG.isMember(t(c), this.sgsMdepth) : this.permHash(this.sgsM.minElem(c))
  };
  y.prototype.initTables =
    function(c) {
      if (!this.coset2idx) {
        c = c || 1E5;
        this.sgsH = new G(this.genH);
        this.sgsG = new G(this.sgsH);
        this.sgsG.extend(this.genG);
        var n = this.sgsG.size() / this.sgsH.size();
        this.isCosetSearch = 1 < this.sgsH.size();
        var h = 1;
        if (this.genM) this.sgsM = new G(this.genM), h = this.sgsG.size() / this.sgsM.size();
        else if (1 == this.sgsH.size()) {
          this.sgsM = null;
          this.sgsMdepth = 0;
          for (var k = this.sgsG.e.length - 1; 0 <= k && !(h * this.sgsG.i2t[k].length > c); k--) this.sgsMdepth = k, h *= this.sgsG.i2t[k].length
        } else n <= c ? (this.sgsM = new G(this.genH), h =
          n) : (this.sgsM = null, this.sgsMdepth = this.sgsG.e.length);
        this.clen = h;
        DEBUG && console.log("[Subgroup Solver] coset space:", n, "mid coset size:", h);
        this.genEx = [];
        this.genExi = [];
        this.genExMap = [];
        var b = new Map;
        b.set(this.permHash(this.sgsG.e), -1);
        for (k = 0; k < this.genG.length; k++) {
          c = this.genG[k];
          for (var d = 1;;) {
            n = this.permHash(c);
            if (b.has(n)) break;
            b.set(n, this.genEx.length);
            this.genEx.push(c);
            this.genExi.push(t(c));
            this.genExMap.push([k, d]);
            c = J(this.genG[k], c);
            d++
          }
        }
        this.glen = this.genEx.length;
        for (k = 0; k < this.glen; k++) c =
          t(this.genEx[k]), this.genExMap[k][2] = b.get(this.permHash(c));
        this.canon = new r(this.genEx);
        this.canon.initTrie(2);
        this.canoni = new r(this.genEx);
        for (k = 0; k < this.canon.skipSeqs.length; k++) {
          c = this.canon.skipSeqs[k].slice();
          c.reverse();
          for (b = 0; b < c.length; b++) c[b] = this.genExMap[c[b]][2];
          this.canoni.addSkipSeq(c)
        }
        this.canoni.refillNext();
        this.moveTable = [];
        this.idx2coset = [this.sgsG.e];
        this.coset2idx = {};
        for (k = this.coset2idx[this.midCosetHash(this.sgsG.e)] = 0; k < this.idx2coset.length; k++) {
          if (k >= h) {
            console.log("ERROR!");
            break
          }
          c = this.idx2coset[k];
          for (b = 0; b < this.glen; b++) 1 == this.genExMap[b][1] && (d = J(this.genEx[b], c), n = this.midCosetHash(d), n in this.coset2idx || (this.coset2idx[n] = this.idx2coset.length, this.idx2coset.push(d)), this.moveTable[k * this.glen + b] = this.coset2idx[n])
        }
        h = null;
        for (b = 0; b < this.glen; b++)
          if (1 == this.genExMap[b][1]) h = b;
          else
            for (k = 0; k < this.clen; k++) this.moveTable[k * this.glen + b] = this.moveTable[this.moveTable[k * this.glen + b - 1] * this.glen + h];
        this.prunTable = this.initPrunTable(this.sgsG.e);
        DEBUG && console.log("[Subgroup Solver] prun table size:",
          this.prunTable[0].length)
      }
    };
  y.prototype.idaMidSearch = function(c, n, h, k, b, d, e, l, q) {
    var g = l[0][c];
    if (g > n) return !1;
    if (0 == n) {
      if (c >= this.clen) {
        b.push(-1);
        var p = J(d, e),
          x = q(b, p);
        b.pop();
        return x
      }
      return q(b, d)
    }
    if (c >= this.clen && 0 != h && (x = l[3][c - this.clen], b.push(-1), p = J(d, e), x = this.idaMidSearch(x, n, 1, k, b, p, e, l, q), b.pop(), x)) return x;
    h = k[h || 1];
    for (var u = c * (this.glen + 31 >> 5), M = 0; M < this.glen; M += 32) {
      var T = h[this.glen + (M >> 5)];
      T |= g >= n - 1 ? l[g - n + 2][u + (M >> 5)] : 0;
      for (T = ~T & (32 <= this.glen - M ? -1 : (1 << this.glen - M) - 1); 0 != T;) {
        p =
          31 - Math.clz32(T);
        T -= 1 << p;
        p += M;
        x = c % this.clen;
        x = this.moveTable[x * this.glen + p] + c - x;
        if (DEBUG && l[0][x] >= n) debugger;
        var L = h[p];
        b.push(p);
        p = J(d, this.genExi[p]);
        x = this.idaMidSearch(x, n - 1, L ^ L >> 31, k, b, p, e, l, q);
        b.pop();
        if (x) return x
      }
    }
    return !1
  };
  y.prototype.initPrunTable = function(c, n) {
    for (var h = this.coset2idx[this.midCosetHash(c)], k = [], b = [], d = [], e = this.glen + 31 >> 5, l = 0; l < this.clen; l++) k[l] = -1;
    var q = [];
    if (n) {
      for (l = 0; l < this.clen; l++) k.push(-1, -1), q[l] = this.coset2idx[this.midCosetHash(J(c, this.idx2coset[l]))], q[q[l] +
        this.clen] = l;
      k[0] = 0
    } else k[h] = 0;
    c = 1;
    for (l = h = 0; c != h;) {
      h = c;
      for (var g = 0; g < k.length; g++)
        if (k[g] == l) {
          for (var p = g % this.clen, x = g - p, u = 0; u < this.glen; u++) {
            var M = this.moveTable[p * this.glen + u] + x,
              T = k[M]; - 1 == k[M] && (k[M] = l + 1, T = l + 1, c++);
            T > l && (b[g * e + (u >> 5)] |= 1 << (u & 31));
            T >= l && (d[g * e + (u >> 5)] |= 1 << (u & 31))
          }
          if (n && 0 == x)
            for (u = 0; 2 > u; u++) M = q[p + (1 - u) * this.clen] + (u + 1) * this.clen, -1 == k[M] && (k[M] = l, c++)
        } l++
    }
    return [k, b, d, q, l]
  };
  y.prototype.checkPerm = function(c) {
    this.initTables();
    return 0 <= this.sgsH.isMember(c) ? 1 : 0 > this.sgsG.isMember(c) ?
      2 : 0
  };
  y.ONLY_IDA = 1;
  y.ALLOW_PRE = 2;
  y.prototype.DissectionSolve = function(c, n, h, k, b) {
    var d = this;
    k = k || {};
    var e = $.now();
    this.initTables();
    DEBUG && console.log("[Subgroup Solver] finished init tables, tt=", $.now() - e);
    if (0 > this.sgsG.isMember(c)) console.log("[Subgroup Solver] NOT A MEMBER OF G");
    else {
      var l = this.coset2idx[this.midCosetHash(c)];
      if (l || 0 === l) {
        var q = 0 != (k.mask & y.ONLY_IDA),
          g = 0 != (k.mask & y.ALLOW_PRE) && this.isCosetSearch,
          p = null,
          x = this.prunTable,
          u = null;
        g && (k.prunTable = k.prunTable || this.initPrunTable(c,
          g), x = u = k.prunTable, l = this.clen);
        DEBUG && console.log("[Subgroup Solver] finish init searching, prun value:", x[0][l], "tt=", $.now() - e);
        for (n = Math.max(n, x[0][l]); n <= h; n++) {
          var M = 0;
          k = 0;
          var T = t(c);
          if (q || n <= this.prunTable[4]) p = this.idaMidSearch(g ? this.clen : l, n, 1, this.canon.trieNodes, [], this.sgsG.toKeyIdx(g ? null : T), T, x, function(S, f) {
            M++;
            if (!(0 > d.sgsG.isSubgroupMemberByKey(f, d.sgsH))) {
              f = [];
              for (var m = 0; m < S.length; m++) f.push(-1 == S[m] ? -1 : d.genExMap[S[m]].slice(0, 2));
              return b ? b(f) : f
            }
          }), DEBUG && console.log("[Subgroup Solver] ida ",
            M + k, "node(s) checked at", n, "tt=", $.now() - e);
          else {
            var L = ~~(n / 2);
            u || (u = this.initPrunTable(c, g));
            for (var K = g ? 2 : 1, I = 0, w = [], B = 0; B < this.clen * K; B++) {
              var A = B,
                N = B + (g ? B >= this.clen ? -this.clen : 2 * this.clen : 0);
              if (!(x[0][A] > L || u[0][N] > n - L)) {
                I++;
                var R = new Map,
                  W = 0,
                  X = 0;
                p = this.isCosetSearch ? this.sgsG.e : this.sgsG.toKeyIdx();
                this.idaMidSearch(A, L, 0, this.canon.trieNodes, [], p, T, x, function(S, f) {
                  d.isCosetSearch ? (f = d.sgsH.minElem(f), f = d.permHash(f)) : f = d.permHash(f);
                  W++;
                  var m = R.get(f) || [];
                  m.push(S.slice());
                  R.set(f, m)
                });
                p = this.idaMidSearch(N,
                  n - L, 1, this.canoni.trieNodes, [], p, c, u,
                  function(S, f) {
                    f = g ? f : J(f, c);
                    if (d.isCosetSearch) {
                      f = d.sgsH.minElem(f);
                      var m = d.permHash(f)
                    } else m = d.permHash(f);
                    X++;
                    if (R.has(m)) {
                      f = [];
                      for (var D = 1, z = 0; z < S.length; z++) {
                        var H = S[S.length - 1 - z];
                        H = -1 == H ? -1 : d.genExMap[H][2];
                        D = -1 == H ? 1 : d.canon.trieNodes[D][H];
                        if (DEBUG && -1 == D) debugger;
                        D ^= D >> 31;
                        f.push(-1 == H ? -1 : d.genExMap[H].slice(0, 2))
                      }
                      S = R.get(m);
                      for (z = 0; z < S.length; z++) {
                        m = f.slice();
                        for (var F = D, P = 0; P < S[z].length; P++) {
                          H = S[z][P];
                          F = -1 == H ? 1 : d.canon.trieNodes[F][H];
                          if (-1 == F) break;
                          F ^=
                            F >> 31;
                          m.push(-1 == H ? -1 : d.genExMap[H].slice(0, 2))
                        }
                        if (-1 != F && (H = b ? b(m) : m)) return H
                      }
                    }
                  });
                w.push([B, W, X]);
                M += W;
                k += X;
                if (p) break
              }
            }
            DEBUG && console.log("[Subgroup Solver] dis ", M + k, "node(s) checked at", n, "tt=", $.now() - e)
          }
          if (p) break
        }
        return p
      }
      console.log("[Subgroup Solver] ERROR!")
    }
  };
  y.prototype.godsAlgo = function(c) {
    var n = this;
    this.initTables();
    for (var h = 0, k = 0; k < this.clen; k++)
      for (var b = new Set, d = 0; d <= c; d++) {
        var e = this.isCosetSearch ? this.sgsG.e : this.sgsG.toKeyIdx();
        this.idaMidSearch(k, d, 1, this.canon.trieNodes,
          [], e, null, this.prunTable,
          function(l, q) {
            n.isCosetSearch ? (l = n.sgsH.minElem(q), l = n.permHash(l)) : l = n.permHash(q);
            b.has(l) || (h++, b.add(l))
          })
      }
    return h
  };
  return {
    permMult: J,
    permInv: t,
    permCmp: function(c, n) {
      if (c.length != n.length) return c.length - n.length;
      for (var h = c.length - 1; 0 <= h; h--)
        if (c[h] != n[h]) return c[h] - n[h];
      return 0
    },
    CanonSeqGen: r,
    SchreierSims: G,
    SubgroupSolver: y
  }
}(mathlib.rn);
var min2phase = function() {
  function a() {
    this.move = [];
    this.moveSol = [];
    this.nodeUD = [];
    this.valid1 = 0;
    this.allowShorter = !1;
    this.cc = new r;
    this.urfCubieCube = [];
    this.urfCoordCube = [];
    this.phase1Cubie = [];
    this.preMoveCubes = [];
    this.preMoves = [];
    this.maxPreMoves = this.preMoveLen = 0;
    this.isRec = !1;
    for (var U = 0; 21 > U; U++) this.nodeUD[U] = new e, this.phase1Cubie[U] = new r;
    for (U = 0; 6 > U; U++) this.urfCubieCube[U] = new r, this.urfCoordCube[U] = new e;
    for (U = 0; 20 > U; U++) this.preMoveCubes[U + 1] = new r
  }

  function J(U, fa, ea) {
    U[fa >> 3] ^= ea << (fa <<
      2)
  }

  function t(U, fa, ea) {
    return Math.min(U, fa[ea >> 3] >> (ea << 2) & 15)
  }

  function G(U, fa, ea) {
    U = Ga[U];
    ea && (U ^= 14540032 >> ((U & 15) << 1) & 3);
    return U & 65520 | m[U & 15][fa]
  }

  function r() {
    this.ca = [0, 1, 2, 3, 4, 5, 6, 7];
    this.ea = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  }

  function y(U, fa, ea) {
    ea--;
    for (var la = 1985229328, pa = 0; pa < ea; ++pa) {
      var qa = M[ea - pa],
        Fa = ~~(fa / qa);
      fa %= qa;
      Fa <<= 2;
      U[pa] = U[pa] & 240 | la >> Fa & 15;
      qa = (1 << Fa) - 1;
      la = (la & qa) + (la >> 4 & ~qa)
    }
    U[ea] = U[ea] & 240 | la & 15
  }

  function c(U, fa) {
    for (var ea = 0, la = 1985229328, pa = 0; pa < fa - 1; ++pa) {
      var qa = (U[pa] & 15) << 2;
      ea = (fa - pa) * ea + (la >> qa & 15);
      la -= 286331152 << qa
    }
    return ea
  }

  function n(U, fa, ea) {
    U[ea - 1] &= 240;
    for (var la = ea - 2; 0 <= la; --la) {
      U[la] = U[la] & 240 | fa % (ea - la);
      fa = ~~(fa / (ea - la));
      for (var pa = la + 1; pa < ea; ++pa)(U[pa] & 15) >= (U[la] & 15) && (U[pa] += 1)
    }
  }

  function h(U, fa) {
    for (var ea = 0, la = 0; la < fa; ++la) {
      ea *= fa - la;
      for (var pa = la + 1; pa < fa; ++pa)(U[pa] & 15) < (U[la] & 15) && ++ea
    }
    return ea
  }

  function k(U, fa) {
    for (var ea = 0, la = 4, pa = U.length - 1; 0 <= pa; pa--)(U[pa] & 12) == fa && (ea += u[pa][la--]);
    return ea
  }

  function b(U, fa, ea) {
    for (var la = U.length - 1, pa = 4, qa = la; 0 <=
      la; la--) fa >= u[la][pa] ? (fa -= u[la][pa--], U[la] = U[la] & 240 | pa | ea) : ((qa & 12) == ea && (qa -= 4), U[la] = U[la] & 240 | qa--)
  }

  function d(U, fa) {
    for (var ea = 0, la = fa - 2; 0 <= la; la--) ea ^= U % (fa - la), U = ~~(U / (fa - la));
    return ea & 1
  }

  function e() {
    this.flipc = this.twstc = this.prun = this.slice = this.flip = this.twst = 0
  }

  function l() {
    function U(Oa, bb, fb, Ta, eb, Na, Ra) {
      for (var cb = new r, $a = new r, Ya = 0, nb = 2 <= eb ? 1 : 2, qb = 1 != eb ? r.EdgeConjugate : r.CornConjugate, db = 0; db < Oa; db++)
        if (void 0 === fb[db]) {
          Na.call(cb, db);
          for (var ab = 0; 16 > ab; ab += nb) {
            qb(cb, ab, $a);
            var sb =
              Ra.call($a);
            0 == eb && (O[Ya << 3 | ab >> 1] = sb);
            sb == db && (Ta[Ya] |= 1 << ab / nb);
            fb[sb] = (Ya << 4 | ab) / nb
          }
          bb[Ya++] = db
        } return Ya
    }

    function fa(Oa, bb, fb, Ta, eb, Na, Ra, cb) {
      for (var $a = 0; $a < fb; $a++) {
        eb.call(ea, bb[$a]);
        for (var Ya = 0; Ya < Ta; Ya++) Ra(ea, S[cb ? cb[Ya] : Ya], la), Oa[$a * Ta + Ya] = Na.call(la)
      }
    }
    for (var ea = new r, la = new r, pa = (new r).initCoord(28783, 0, 259268407, 0), qa = (new r).initCoord(15138, 0, 119765538, 7), Fa = (new r).initCoord(5167, 0, 83473207, 0), Da = 0; 8 > Da; Da++) Fa.ca[Da] |= 48;
    for (Da = 0; 16 > Da; Da++) f[Da] = (new r).init(ea.ca, ea.ea), r.CornMultFull(ea,
      qa, la), r.EdgeMult(ea, qa, la), ea.init(la.ca, la.ea), 3 == Da % 4 && (r.CornMultFull(ea, Fa, la), r.EdgeMult(ea, Fa, la), ea.init(la.ca, la.ea)), 7 == Da % 8 && (r.CornMultFull(ea, pa, la), r.EdgeMult(ea, pa, la), ea.init(la.ca, la.ea));
    for (Da = 0; 16 > Da; Da++) m[Da] = [], D[Da] = [], z[Da] = [], F[Da] = [], H[Da] = [];
    for (Da = 0; 16 > Da; Da++)
      for (pa = 0; 16 > pa; pa++) m[Da][pa] = Da ^ pa ^ 84660 >> pa & Da << 1 & 2, D[m[Da][pa]][pa] = Da;
    ea = new r;
    for (Da = 0; 16 > Da; Da++)
      for (pa = 0; 18 > pa; pa++) {
        r.CornConjugate(S[pa], D[0][Da], ea);
        qa = 0;
        a: for (; 18 > qa; qa++) {
          for (Fa = 0; 8 > Fa; Fa++)
            if (S[qa].ca[Fa] !=
              ea.ca[Fa]) continue a;
          z[Da][pa] = qa;
          H[Da][K[pa]] = K[qa];
          break
        }
        0 == Da % 2 && (F[pa << 3 | Da >> 1] = z[Da][pa])
      }
    U(2048, P, C, E, 0, r.prototype.setFlip, r.prototype.getFlip);
    U(2187, Q, ba, ja, 1, r.prototype.setTwst, r.prototype.getTwst);
    U(40320, wa, Ca, sa, 2, r.prototype.setEPerm, r.prototype.getEPerm);
    pa = new r;
    for (Da = 0; 2768 > Da; Da++) y(pa.ea, wa[Da], 8), ua[Da] = k(pa.ea, 0) + 70 * d(wa[Da], 8), ea.invFrom(pa), Ga[Da] = Ca[ea.getEPerm()];
    ea = new r;
    la = new r;
    fa(ya, P, 336, 18, r.prototype.setFlip, r.prototype.getFlipSym, r.EdgeMult);
    fa(Ha, Q, 324, 18, r.prototype.setTwst,
      r.prototype.getTwstSym, r.CornMult);
    fa(ia, wa, 2768, 10, r.prototype.setEPerm, r.prototype.getEPermSym, r.EdgeMult, L);
    fa(ca, wa, 2768, 10, r.prototype.setCPerm, r.prototype.getCPermSym, r.CornMult, L);
    for (Da = 0; 495 > Da; Da++) {
      ea.setSlice(Da);
      for (pa = 0; 18 > pa; pa++) r.EdgeMult(ea, S[pa], la), ka[18 * Da + pa] = la.getSlice();
      for (pa = 0; 16 > pa; pa += 2) r.EdgeConjugate(ea, D[0][pa], la), Y[Da << 3 | pa >> 1] = la.getSlice()
    }
    for (Da = 0; 24 > Da; Da++) {
      ea.setMPerm(Da);
      for (pa = 0; 10 > pa; pa++) r.EdgeMult(ea, S[L[pa]], la), ma[10 * Da + pa] = la.getMPerm();
      for (pa = 0; 16 >
        pa; pa++) r.EdgeConjugate(ea, D[0][pa], la), xa[Da << 4 | pa] = la.getMPerm()
    }
    for (Da = 0; 140 > Da; Da++) {
      ea.setCComb(Da % 70);
      for (pa = 0; 10 > pa; pa++) r.CornMult(ea, S[L[pa]], la), Ba[10 * Da + pa] = la.getCComb() + 70 * (165 >> pa & 1 ^ ~~(Da / 70));
      for (pa = 0; 16 > pa; pa++) r.CornConjugate(ea, D[0][pa], la), da[Da << 4 | pa] = la.getCComb() + 70 * ~~(Da / 70)
    }
  }

  function q(U, fa, ea, la, pa, qa, Fa, Da) {
    var Oa = Da & 15,
      bb = 1 == (Da >> 4 & 1) ? 14540032 : 0,
      fb = Da >> 8 & 15,
      Ta = Da >> 12 & 15,
      eb = Da >> 16 & 15,
      Na = (1 << Oa) - 1,
      Ra = null == la;
    ea *= fa;
    Da = 1 == (Da >> 5 & 1) ? 10 : 18;
    var cb = 10 == Da ? 66 : 599186,
      $a = (U[ea >>
        3] >> (ea << 2) & 15) - 1;
    if (-1 == $a) {
      for (var Ya = 0; Ya < (ea >> 3) + 1; Ya++) U[Ya] = -1;
      J(U, 0, 15);
      $a = 0
    } else J(U, ea, 15 ^ $a + 1);
    for (Ta = 0 < x ? Math.min(Math.max($a + 1, eb), Ta) : Ta; $a < Ta;) {
      var nb = (eb = $a > fb) ? 15 : $a,
        qb = 286331153 * nb,
        db = eb ? $a : 15;
      $a++;
      za++;
      var ab = $a ^ 15,
        sb = 0,
        Ab = 0;
      for (Ya = 0; Ya < ea; Ya++, Ab >>= 4) {
        if (0 == (Ya & 7)) {
          Ab = U[Ya >> 3];
          var ub = Ab ^ qb;
          if (0 == (ub - 286331153 & ~ub & 2290649224)) {
            Ya += 7;
            continue
          }
        }
        if ((Ab & 15) == nb) {
          ub = Ya % fa;
          var Xa = ~~(Ya / fa),
            ib = 0,
            Cb = 0;
          Ra && (ib = C[ub], Cb = ib & 7, ib >>= 3);
          for (var pb = 0; pb < Da; pb++) {
            var ob = qa[Xa * Da + pb];
            var tb = Ra ? O[ya[ib *
              Da + F[pb << 3 | Cb]] ^ Cb ^ ob & Na] : pa[la[ub * Da + pb] << Oa | ob & Na];
            ob >>= Oa;
            var La = ob * fa + tb,
              Sa = U[La >> 3] >> (La << 2) & 15;
            if (Sa != db) Sa < $a - 1 && (pb += cb >> pb & 3);
            else {
              sb++;
              if (eb) {
                J(U, Ya, ab);
                break
              }
              J(U, La, ab);
              La = 1;
              for (Sa = Fa[ob]; 0 != (Sa >>= 1); La++)
                if (1 == (Sa & 1)) {
                  var Za = ob * fa;
                  Za = Ra ? Za + O[C[tb] ^ La] : Za + pa[tb << Oa | La ^ bb >> (La << 1) & 3];
                  (U[Za >> 3] >> (Za << 2) & 15) == db && (J(U, Za, ab), sb++)
                }
            }
          }
        }
      }
    }
    J(U, ea, $a + 1 ^ 15);
    return $a + 1
  }

  function g(U) {
    Ia = q(V, 2048, 324, null, null, Ha, ja, 103939);
    za > U || (Ka = q(Z, 495, 324, ka, Y, Ha, ja, 431619), za > U || (Ma = q(oa, 495, 336, ka, Y, ya, E,
      431619), za > U || (Ua = q(ta, 24, 2768, ma, xa, ca, sa, 584244), za > U || (ra = q(na, 140, 2768, Ba, da, ia, sa, 514084)))))
  }

  function p() {
    0 > za && (l(), za = 0);
    if (0 == za) g(99);
    else if (54 > za) g(za);
    else return !0;
    return !1
  }
  for (var x = 2, u = [], M = [1], T = "U ;U2;U';R ;R2;R';F ;F2;F';D ;D2;D';L ;L2;L';B ;B2;B'".split(";"), L = [0, 1, 2, 4, 7, 9, 10, 11, 13, 16, 3, 5, 6, 8, 12, 14, 15, 17], K = [], I = [], w = [
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      [6, 7, 8, 0, 1, 2, 3, 4, 5, 15, 16, 17, 9, 10, 11, 12, 13, 14],
      [3, 4, 5, 6, 7, 8, 0, 1, 2, 12, 13, 14, 15, 16, 17, 9, 10, 11],
      [2, 1, 0, 5, 4, 3, 8, 7, 6, 11, 10,
        9, 14, 13, 12, 17, 16, 15
      ],
      [8, 7, 6, 2, 1, 0, 5, 4, 3, 17, 16, 15, 11, 10, 9, 14, 13, 12],
      [5, 4, 3, 8, 7, 6, 2, 1, 0, 14, 13, 12, 17, 16, 15, 11, 10, 9]
    ], B = 0; 18 > B; B++) K[L[B]] = B;
  for (B = 0; 10 > B; B++)
    for (var A = ~~(L[B] / 3), N = I[B] = 0; 10 > N; N++) {
      var R = ~~(L[N] / 3);
      I[B] |= (A == R || A % 3 == R % 3 && A >= R ? 1 : 0) << N
    }
  for (B = I[10] = 0; 13 > B; B++)
    for (u[B] = [], M[B + 1] = M[B] * (B + 1), N = u[B][0] = u[B][B] = 1; 13 > N; N++) u[B][N] = N <= B ? u[B - 1][N - 1] + u[B - 1][N] : 0;
  r.EdgeMult = function(U, fa, ea) {
    for (var la = 0; 12 > la; la++) ea.ea[la] = U.ea[fa.ea[la] & 15] ^ fa.ea[la] & 16
  };
  r.CornMult = function(U, fa, ea) {
    for (var la =
        0; 8 > la; la++) ea.ca[la] = U.ca[fa.ca[la] & 15] & 15 | ((U.ca[fa.ca[la] & 15] >> 4) + (fa.ca[la] >> 4)) % 3 << 4
  };
  r.CornMultFull = function(U, fa, ea) {
    for (var la = 0; 8 > la; la++) {
      var pa = U.ca[fa.ca[la] & 15] >> 4,
        qa = fa.ca[la] >> 4,
        Fa = pa + (3 > pa ? qa : 6 - qa);
      Fa = Fa % 3 + (3 > pa == 3 > qa ? 0 : 3);
      ea.ca[la] = U.ca[fa.ca[la] & 15] & 15 | Fa << 4
    }
  };
  r.CornConjugate = function(U, fa, ea) {
    var la = f[D[0][fa]];
    fa = f[fa];
    for (var pa = 0; 8 > pa; pa++) {
      var qa = U.ca[fa.ca[pa] & 15] >> 4;
      ea.ca[pa] = la.ca[U.ca[fa.ca[pa] & 15] & 15] & 15 | (3 > la.ca[U.ca[fa.ca[pa] & 15] & 15] >> 4 ? qa : (3 - qa) % 3) << 4
    }
  };
  r.EdgeConjugate =
    function(U, fa, ea) {
      var la = f[D[0][fa]];
      fa = f[fa];
      for (var pa = 0; 12 > pa; pa++) ea.ea[pa] = la.ea[U.ea[fa.ea[pa] & 15] & 15] ^ U.ea[fa.ea[pa] & 15] & 16 ^ fa.ea[pa] & 16
    };
  r.prototype.init = function(U, fa) {
    this.ca = U.slice();
    this.ea = fa.slice();
    return this
  };
  r.prototype.initCoord = function(U, fa, ea, la) {
    y(this.ca, U, 8);
    this.setTwst(fa);
    n(this.ea, ea, 12);
    this.setFlip(la);
    return this
  };
  r.prototype.isEqual = function(U) {
    for (var fa = 0; 8 > fa; fa++)
      if (this.ca[fa] != U.ca[fa]) return !1;
    for (fa = 0; 12 > fa; fa++)
      if (this.ea[fa] != U.ea[fa]) return !1;
    return !0
  };
  r.prototype.setFlip = function(U) {
    for (var fa = 0, ea = 10; 0 <= ea; ea--, U >>= 1) this.ea[ea] = this.ea[ea] & 15 | (U & 1) << 4, fa ^= this.ea[ea];
    this.ea[11] = this.ea[11] & 15 | fa & 16
  };
  r.prototype.getFlip = function() {
    for (var U = 0, fa = 0; 11 > fa; fa++) U = U << 1 | this.ea[fa] >> 4 & 1;
    return U
  };
  r.prototype.getFlipSym = function() {
    return C[this.getFlip()]
  };
  r.prototype.setTwst = function(U) {
    for (var fa = 15, ea = 6; 0 <= ea; ea--, U = ~~(U / 3)) this.ca[ea] = this.ca[ea] & 15 | U % 3 << 4, fa -= this.ca[ea] >> 4;
    this.ca[7] = this.ca[7] & 15 | fa % 3 << 4
  };
  r.prototype.getTwst = function() {
    for (var U =
        0, fa = 0; 7 > fa; fa++) U += (U << 1) + (this.ca[fa] >> 4);
    return U
  };
  r.prototype.getTwstSym = function() {
    return ba[this.getTwst()]
  };
  r.prototype.setCPerm = function(U) {
    y(this.ca, U, 8)
  };
  r.prototype.getCPerm = function() {
    return c(this.ca, 8)
  };
  r.prototype.getCPermSym = function() {
    var U = Ca[c(this.ca, 8)];
    return U ^ 14540032 >> ((U & 15) << 1) & 3
  };
  r.prototype.setEPerm = function(U) {
    y(this.ea, U, 8)
  };
  r.prototype.getEPerm = function() {
    return c(this.ea, 8)
  };
  r.prototype.getEPermSym = function() {
    return Ca[c(this.ea, 8)]
  };
  r.prototype.getSlice = function() {
    return 494 -
      k(this.ea, 8)
  };
  r.prototype.setSlice = function(U) {
    b(this.ea, 494 - U, 8)
  };
  r.prototype.getMPerm = function() {
    return h(this.ea, 12) % 24
  };
  r.prototype.setMPerm = function(U) {
    n(this.ea, U, 12)
  };
  r.prototype.getCComb = function() {
    return k(this.ca, 0)
  };
  r.prototype.setCComb = function(U) {
    b(this.ca, U, 0)
  };
  r.prototype.URFConjugate = function() {
    var U = new r;
    r.CornMult(r.urf2, this, U);
    r.CornMult(U, r.urf1, this);
    r.EdgeMult(r.urf2, this, U);
    r.EdgeMult(U, r.urf1, this)
  };
  var W = [
      [8, 9, 20],
      [6, 18, 38],
      [0, 36, 47],
      [2, 45, 11],
      [29, 26, 15],
      [27, 44, 24],
      [33,
        53, 42
      ],
      [35, 17, 51]
    ],
    X = [
      [5, 10],
      [7, 19],
      [3, 37],
      [1, 46],
      [32, 16],
      [28, 25],
      [30, 43],
      [34, 52],
      [23, 12],
      [21, 41],
      [50, 39],
      [48, 14]
    ];
  r.prototype.toFaceCube = function(U, fa) {
    U = U || W;
    fa = fa || X;
    for (var ea = [], la = 0; 54 > la; la++) ea[la] = "URFDLB" [~~(la / 9)];
    for (var pa = 0; 8 > pa; pa++) {
      la = this.ca[pa] & 15;
      for (var qa = this.ca[pa] >> 4, Fa = 0; 3 > Fa; Fa++) ea[U[pa][(Fa + qa) % 3]] = "URFDLB" [~~(U[la][Fa] / 9)]
    }
    for (U = 0; 12 > U; U++)
      for (la = this.ea[U] & 15, qa = this.ea[U] >> 4, Fa = 0; 2 > Fa; Fa++) ea[fa[U][(Fa + qa) % 2]] = "URFDLB" [~~(fa[la][Fa] / 9)];
    return ea.join("")
  };
  r.prototype.invFrom =
    function(U) {
      for (var fa = 0; 12 > fa; fa++) this.ea[U.ea[fa] & 15] = fa & 15 | U.ea[fa] & 16;
      for (fa = 0; 8 > fa; fa++) this.ca[U.ca[fa] & 15] = fa | 64 >> (U.ca[fa] >> 4) & 48;
      return this
    };
  r.prototype.fromFacelet = function(U, fa, ea) {
    fa = fa || W;
    ea = ea || X;
    for (var la = 0, pa = [], qa = U[4] + U[13] + U[22] + U[31] + U[40] + U[49], Fa = 0; 54 > Fa; ++Fa) {
      pa[Fa] = qa.indexOf(U[Fa]);
      if (-1 == pa[Fa]) return -1;
      la += 1 << (pa[Fa] << 2)
    }
    if (10066329 != la) return -1;
    var Da;
    for (Fa = 0; 8 > Fa; ++Fa) {
      for (Da = 0; 3 > Da && 0 != pa[fa[Fa][Da]] && 3 != pa[fa[Fa][Da]]; ++Da);
      U = pa[fa[Fa][(Da + 1) % 3]];
      la = pa[fa[Fa][(Da +
        2) % 3]];
      for (qa = 0; 8 > qa; ++qa)
        if (U == ~~(fa[qa][1] / 9) && la == ~~(fa[qa][2] / 9)) {
          this.ca[Fa] = qa | Da % 3 << 4;
          break
        }
    }
    for (Fa = 0; 12 > Fa; ++Fa)
      for (qa = 0; 12 > qa; ++qa) {
        if (pa[ea[Fa][0]] == ~~(ea[qa][0] / 9) && pa[ea[Fa][1]] == ~~(ea[qa][1] / 9)) {
          this.ea[Fa] = qa;
          break
        }
        if (pa[ea[Fa][0]] == ~~(ea[qa][1] / 9) && pa[ea[Fa][1]] == ~~(ea[qa][0] / 9)) {
          this.ea[Fa] = qa | 16;
          break
        }
      }
  };
  e.prototype.set = function(U) {
    this.twst = U.twst;
    this.flip = U.flip;
    this.slice = U.slice;
    this.prun = U.prun;
    this.twstc = U.twstc;
    this.flipc = U.flipc
  };
  e.prototype.calcPruning = function(U) {
    this.prun =
      Math.max(t(Ka, Z, 495 * (this.twst >> 3) + Y[this.slice << 3 | this.twst & 7]), t(Ma, oa, 495 * (this.flip >> 3) + Y[this.slice << 3 | this.flip & 7]), t(Ia, V, this.twstc >> 3 << 11 | O[this.flipc ^ this.twstc & 7]), t(Ia, V, this.twst >> 3 << 11 | O[this.flip ^ this.twst & 7]))
  };
  e.prototype.setWithPrun = function(U, fa) {
    this.twst = U.getTwstSym();
    this.flip = U.getFlipSym();
    this.prun = t(Ia, V, this.twst >> 3 << 11 | O[this.flip ^ this.twst & 7]);
    if (this.prun > fa) return !1;
    this.slice = U.getSlice();
    this.prun = Math.max(this.prun, t(Ka, Z, 495 * (this.twst >> 3) + Y[this.slice << 3 | this.twst &
      7]), t(Ma, oa, 495 * (this.flip >> 3) + Y[this.slice << 3 | this.flip & 7]));
    if (this.prun > fa) return !1;
    var ea = new r;
    r.CornConjugate(U, 1, ea);
    r.EdgeConjugate(U, 1, ea);
    this.twstc = ea.getTwstSym();
    this.flipc = ea.getFlipSym();
    this.prun = Math.max(this.prun, t(Ia, V, this.twstc >> 3 << 11 | O[this.flipc ^ this.twstc & 7]));
    return this.prun <= fa
  };
  e.prototype.doMovePrun = function(U, fa, ea) {
    this.slice = ka[18 * U.slice + fa];
    this.flip = ya[18 * (U.flip >> 3) + F[fa << 3 | U.flip & 7]] ^ U.flip & 7;
    this.twst = Ha[18 * (U.twst >> 3) + F[fa << 3 | U.twst & 7]] ^ U.twst & 7;
    return this.prun =
      Math.max(t(Ka, Z, 495 * (this.twst >> 3) + Y[this.slice << 3 | this.twst & 7]), t(Ma, oa, 495 * (this.flip >> 3) + Y[this.slice << 3 | this.flip & 7]), t(Ia, V, this.twst >> 3 << 11 | O[this.flip ^ this.twst & 7]))
  };
  e.prototype.doMovePrunConj = function(U, fa) {
    fa = z[3][fa];
    this.flipc = ya[18 * (U.flipc >> 3) + F[fa << 3 | U.flipc & 7]] ^ U.flipc & 7;
    this.twstc = Ha[18 * (U.twstc >> 3) + F[fa << 3 | U.twstc & 7]] ^ U.twstc & 7;
    return t(Ia, V, this.twstc >> 3 << 11 | O[this.flipc ^ this.twstc & 7])
  };
  a.prototype.solution = function(U, fa, ea, la, pa, qa, Fa) {
    p();
    U = this.verify(U);
    if (0 != U) return "Error " +
      Math.abs(U);
    void 0 === fa && (fa = 21);
    void 0 === ea && (ea = 1E9);
    void 0 === la && (la = 0);
    void 0 === pa && (pa = 0);
    this.sol = fa + 1;
    this.probe = 0;
    this.probeMax = ea;
    this.probeMin = Math.min(la, ea);
    this.verbose = pa;
    this.moveSol = null;
    this.isRec = !1;
    this.firstFilters = [0, 0, 0, 0, 0, 0];
    this.lastFilters = [0, 0, 0, 0, 0, 0];
    for (fa = 0; 3 > fa; fa++) void 0 !== qa && (this.firstFilters[fa] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * qa] / 3), this.lastFilters[fa + 3] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * qa] / 3)), void 0 !== Fa && (this.lastFilters[fa] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * Fa] / 3), this.firstFilters[fa +
      3] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * Fa] / 3));
    this.initSearch();
    return this.search()
  };
  a.prototype.initSearch = function() {
    this.conjMask = 0;
    this.maxPreMoves = 7 < this.conjMask ? 0 : 20;
    for (var U = 0; 6 > U; U++)
      if (this.urfCubieCube[U].init(this.cc.ca, this.cc.ea), this.urfCoordCube[U].setWithPrun(this.urfCubieCube[U], 20), this.cc.URFConjugate(), 2 == U % 3) {
        var fa = (new r).invFrom(this.cc);
        this.cc.init(fa.ca, fa.ea)
      }
  };
  a.prototype.next = function(U, fa, ea) {
    this.probe = 0;
    this.probeMax = U;
    this.probeMin = Math.min(fa, U);
    this.moveSol = null;
    this.isRec = !0;
    this.verbose = ea;
    return this.search()
  };
  a.prototype.verify = function(U) {
    if (-1 == this.cc.fromFacelet(U)) return -1;
    for (var fa = U = 0, ea = 0; 12 > ea; ea++) fa |= 1 << (this.cc.ea[ea] & 15), U ^= this.cc.ea[ea] >> 4;
    if (4095 != fa) return -2;
    if (0 != U) return -3;
    for (ea = U = fa = 0; 8 > ea; ea++) fa |= 1 << (this.cc.ca[ea] & 15), U += this.cc.ca[ea] >> 4;
    return 255 != fa ? -4 : 0 != U % 3 ? -5 : 0 != (d(h(this.cc.ea, 12), 12) ^ d(this.cc.getCPerm(), 8)) ? -6 : 0
  };
  a.prototype.phase1PreMoves = function(U, fa, ea) {
    if (U == this.maxPreMoves - 1 && 0 != (this.lastFilter >> fa & 1)) return 1;
    this.preMoveLen =
      this.maxPreMoves - U;
    if (this.isRec ? this.depth1 == this.length1 - this.preMoveLen : 0 == this.preMoveLen || 0 == (225207 >> fa & 1))
      if (this.depth1 = this.length1 - this.preMoveLen, this.phase1Cubie[0].init(ea.ca, ea.ea), this.allowShorter = 7 == this.depth1 && 0 != this.preMoveLen, this.nodeUD[this.depth1 + 1].setWithPrun(ea, this.depth1) && 0 == this.phase1(this.nodeUD[this.depth1 + 1], this.depth1, -1)) return 0;
    if (0 == U || this.preMoveLen + 7 >= this.length1) return 1;
    var la = 0;
    if (1 == U || this.preMoveLen + 1 + 7 >= this.length1) la |= 225207;
    fa = 3 * ~~(fa / 3);
    for (var pa =
        0; 18 > pa; pa++)
      if (pa == fa || pa == fa - 9 || pa == fa + 9) pa += 2;
      else if (!(this.isRec && pa != this.preMoves[this.maxPreMoves - U] || 0 != (la & 1 << pa)) && (r.CornMult(S[pa], ea, this.preMoveCubes[U]), r.EdgeMult(S[pa], ea, this.preMoveCubes[U]), this.preMoves[this.maxPreMoves - U] = pa, 0 == this.phase1PreMoves(U - 1, pa, this.preMoveCubes[U]))) return 0;
    return 1
  };
  a.prototype.search = function() {
    for (this.length1 = this.isRec ? this.length1 : 0; this.length1 < this.sol; this.length1++)
      for (this.urfIdx = this.isRec ? this.urfIdx : 0; 6 > this.urfIdx; this.urfIdx++)
        if (0 ==
          (this.conjMask & 1 << this.urfIdx) && (this.firstFilter = this.firstFilters[this.urfIdx], this.lastFilter = this.lastFilters[this.urfIdx], 0 == this.phase1PreMoves(this.maxPreMoves, -30, this.urfCubieCube[this.urfIdx], 0))) return null == this.moveSol ? "Error 8" : this.moveSol;
    return null == this.moveSol ? "Error 7" : this.moveSol
  };
  a.prototype.initPhase2Pre = function() {
    this.isRec = !1;
    if (this.probe >= (null == this.moveSol ? this.probeMax : this.probeMin)) return 0;
    ++this.probe;
    for (var U = this.valid1; U < this.depth1; U++) r.CornMult(this.phase1Cubie[U],
      S[this.move[U]], this.phase1Cubie[U + 1]), r.EdgeMult(this.phase1Cubie[U], S[this.move[U]], this.phase1Cubie[U + 1]);
    this.valid1 = this.depth1;
    U = this.initPhase2(this.phase1Cubie[this.depth1]);
    if (0 == U || 0 == this.preMoveLen || 2 == U) return U;
    U = 3 * ~~(this.preMoves[this.preMoveLen - 1] / 3) + 1;
    r.CornMult(S[U], this.phase1Cubie[this.depth1], this.phase1Cubie[this.depth1 + 1]);
    r.EdgeMult(S[U], this.phase1Cubie[this.depth1], this.phase1Cubie[this.depth1 + 1]);
    this.preMoves[this.preMoveLen - 1] += 2 - this.preMoves[this.preMoveLen - 1] % 3 * 2;
    U = this.initPhase2(this.phase1Cubie[this.depth1 + 1]);
    this.preMoves[this.preMoveLen - 1] += 2 - this.preMoves[this.preMoveLen - 1] % 3 * 2;
    return U
  };
  a.prototype.initPhase2 = function(U) {
    var fa = U.getCPermSym(),
      ea = fa & 15;
    fa >>= 4;
    var la = U.getEPermSym(),
      pa = la & 15;
    la >>= 4;
    U = U.getMPerm();
    var qa = Math.max(t(ra, na, 140 * la + da[(ua[fa] & 255) << 4 | D[pa][ea]]), t(Ua, ta, 24 * fa + xa[U << 4 | ea])),
      Fa = Math.min(13, this.sol - this.length1);
    if (qa >= Fa) return qa > Fa ? 2 : 1;
    var Da;
    for (Da = Fa - 1; Da >= qa; Da--) {
      var Oa = this.phase2(la, pa, fa, ea, U, Da, this.depth1, 10);
      if (0 > Oa) break;
      Da -= Oa;
      this.moveSol = [];
      for (Oa = 0; Oa < this.depth1 + Da; Oa++) this.appendSolMove(this.move[Oa]);
      for (Oa = this.preMoveLen - 1; 0 <= Oa; Oa--) this.appendSolMove(this.preMoves[Oa]);
      this.sol = this.moveSol.length;
      this.moveSol = this.solutionToString()
    }
    return Da != Fa - 1 ? this.probe >= this.probeMin ? 0 : 1 : 1
  };
  a.prototype.phase1 = function(U, fa, ea) {
    if (fa == this.depth1 - 1 && 0 != (this.firstFilter >> ea & 1)) return 1;
    if (0 == U.prun && 5 > fa) {
      if (this.allowShorter || 0 == fa) {
        this.depth1 -= fa;
        var la = this.initPhase2Pre();
        this.depth1 += fa;
        return la
      }
      return 1
    }
    for (var pa =
        0; 18 > pa; pa += 3)
      if (pa != ea && pa != ea - 9)
        for (var qa = 0; 3 > qa; qa++)
          if (la = pa + qa, !this.isRec || la == this.move[this.depth1 - fa]) {
            var Fa = this.nodeUD[fa].doMovePrun(U, la, !0);
            if (Fa > fa) break;
            else if (Fa == fa) continue;
            Fa = this.nodeUD[fa].doMovePrunConj(U, la);
            if (Fa > fa) break;
            else if (Fa == fa) continue;
            this.move[this.depth1 - fa] = la;
            this.valid1 = Math.min(this.valid1, this.depth1 - fa);
            la = this.phase1(this.nodeUD[fa], fa - 1, pa);
            if (0 == la) return 0;
            if (2 == la) break
          } return 1
  };
  a.prototype.appendSolMove = function(U) {
    if (0 == this.moveSol.length) this.moveSol.push(U);
    else {
      var fa = ~~(U / 3),
        ea = ~~(this.moveSol.at(-1) / 3);
      fa == ea ? (U = (U % 3 + this.moveSol.at(-1) % 3 + 1) % 4, 3 == U ? this.moveSol.pop() : this.moveSol.splice(-1, 1, 3 * fa + U)) : 1 < this.moveSol.length && fa % 3 == ea % 3 && fa == ~~(this.moveSol.at(-2) / 3) ? (U = (U % 3 + this.moveSol.at(-2) % 3 + 1) % 4, 3 == U ? (this.moveSol.splice(-2, 1, this.moveSol.at(-1)), this.moveSol.pop()) : this.moveSol.splice(-2, 1, 3 * fa + U)) : this.moveSol.push(U)
    }
  };
  a.prototype.phase2 = function(U, fa, ea, la, pa, qa, Fa, Da) {
    if (0 == this.depth1 && 1 == Fa && 0 != (this.firstFilter >> L[Da] & 1)) return -1;
    if (0 ==
      U && 0 == ea && 0 == pa && (0 < this.preMoveLen || 0 == (this.lastFilter >> L[Da] & 1))) return qa;
    Da = I[Da];
    for (var Oa = 0; 10 > Oa; Oa++)
      if (0 != (Da >> Oa & 1)) Oa += 66 >> Oa & 3;
      else {
        var bb = ma[10 * pa + Oa],
          fb = ca[10 * ea + H[la][Oa]],
          Ta = m[fb & 15][la];
        fb >>= 4;
        if (!(t(Ua, ta, 24 * fb + xa[bb << 4 | Ta]) >= qa)) {
          var eb = ia[10 * U + H[fa][Oa]],
            Na = m[eb & 15][fa];
          eb >>= 4;
          if (!(t(ra, na, 140 * eb + da[(ua[fb] & 255) << 4 | D[Na][Ta]]) >= qa)) {
            var Ra = G(eb, Na, !1),
              cb = G(fb, Ta, !0);
            if (!(t(ra, na, 140 * (Ra >> 4) + da[(ua[cb >> 4] & 255) << 4 | D[Ra & 15][cb & 15]]) >= qa) && (bb = this.phase2(eb, Na, fb, Ta, bb, qa - 1, Fa +
                1, Oa), 0 <= bb)) return this.move[Fa] = L[Oa], bb
          }
        }
      } return -1
  };
  a.prototype.solutionToString = function() {
    var U = "",
      fa = 0 != (this.verbose & 2) ? (this.urfIdx + 3) % 6 : this.urfIdx;
    if (3 > fa)
      for (var ea = 0; ea < this.moveSol.length; ++ea) U += T[w[fa][this.moveSol[ea]]] + " ";
    else
      for (ea = this.moveSol.length - 1; 0 <= ea; --ea) U += T[w[fa][this.moveSol[ea]]] + " ";
    return U
  };
  var S = [],
    f = [],
    m = [],
    D = [],
    z = [],
    H = [],
    F = [],
    P = [],
    C = [],
    E = [],
    O = [],
    Q = [],
    ba = [],
    ja = [],
    wa = [],
    Ca = [],
    sa = [],
    ua = [],
    Ga = [],
    Ha = [],
    ya = [],
    ka = [],
    Y = [],
    Z = [],
    oa = [],
    V = [],
    ca = [],
    ia = [],
    ma = [],
    xa = [],
    Ba = [],
    da = [],
    ta = [],
    na = [],
    Ia = 15,
    Ka = 15,
    Ma = 15,
    Ua = 15,
    ra = 15;
  for (B = 0; 18 > B; B++) S[B] = new r;
  S[0].initCoord(15120, 0, 119750400, 0);
  S[3].initCoord(21021, 1494, 323403417, 0);
  S[6].initCoord(8064, 1236, 29441808, 550);
  S[9].initCoord(9, 0, 5880, 0);
  S[12].initCoord(1230, 412, 2949660, 0);
  S[15].initCoord(224, 137, 328552, 137);
  for (B = 0; 18 > B; B += 3)
    for (A = 0; 2 > A; A++) r.EdgeMult(S[B + A], S[B], S[B + A + 1]), r.CornMult(S[B + A], S[B], S[B + A + 1]);
  r.urf1 = (new r).initCoord(2531, 1373, 67026819, 1367);
  r.urf2 = (new r).initCoord(2089, 1906, 322752913, 2040);
  var za = -1;
  return {
    Search: a,
    solve: function(U) {
      return (new a).solution(U)
    },
    randomCube: function() {
      var U = ~~(2048 * Math.random()),
        fa = ~~(2187 * Math.random());
      do {
        var ea = ~~(Math.random() * M[12]);
        var la = ~~(Math.random() * M[8])
      } while (d(la, 8) != d(ea, 12));
      return (new r).initCoord(la, fa, ea, U).toFaceCube()
    },
    fromScramble: function(U) {
      for (var fa = -1, ea = new r, la = new r, pa = 0; pa < U.length; pa++) switch (U[pa]) {
        case "U":
        case "R":
        case "F":
        case "D":
        case "L":
        case "B":
          fa = 3 * "URFDLB".indexOf(U[pa]);
          break;
        case " ":
          -1 != fa && (r.CornMult(ea, S[fa], la),
            r.EdgeMult(ea, S[fa], la), ea.init(la.ca, la.ea));
          fa = -1;
          break;
        case "2":
          fa++;
          break;
        case "'":
          fa += 2
      } - 1 != fa && (r.CornMult(ea, S[fa], la), r.EdgeMult(ea, S[fa], la), ea.init(la.ca, la.ea));
      return la.toFaceCube()
    },
    initFull: function() {
      x = 0;
      p()
    },
    INVERSE_SOLUTION: 2
  }
}();
"undefined" !== typeof module && "undefined" !== typeof module.exports && (module.exports = min2phase);
var scrMgr = function(a, J) {
    function t(k, b, d) {
      k = k || [
        [""]
      ];
      b = b || [""];
      d = d || 0;
      for (var e = 0, l = -1, q = [], g, p, x = 0; x < d; x++) {
        do g = a(k.length), p = a(k[g].length), g != l && (e = 0, l = g); while (0 != (e >> p & 1));
        e |= 1 << p;
        k[g][p].constructor == Array ? q.push(J(k[g][p]) + J(b)) : q.push(k[g][p] + J(b))
      }
      return q.join(" ")
    }

    function G(k, b, d) {
      DEBUG && console.log("[regscr]", k);
      if ($.isArray(k))
        for (d = 0; d < k.length; d++) y[k[d]] = b;
      else y[k] = b, $.isArray(d) ? c[k] = function(e, l) {
        return e[l]
      }.bind(null, d) : d && (c[k] = d);
      "333" == k && (y.mrbl = y["333oh"] = y["333ft"] =
        b);
      return G
    }

    function r(k, b, d) {
      if (0 >= d || 0 > k || 0 > b) return 0;
      var e = b + 131 * ~~(k / d);
      b = e % 24317 + 42;
      var l = (137 * e ^ b) % 32141,
        q = (b + l + 63629) % d,
        g = ~~(e / d) % d + 1,
        p = ~~(e / d / d) % d + 1;
      k = (k + e) % d;
      0 == k % 3 && (k = (k / 3 * 24317 + b) % ~~((d + 2) / 3) * 3);
      0 == k % 2 && (k = (k / 2 * 32141 + l) % ~~((d + 1) / 2) * 2);
      k < ~~(d / 2) && (k = (63629 * k + (b ^ l ^ q)) % ~~(d / 2));
      (k ^ g) < d && (k ^= g);
      k = (63629 * k + q) % d;
      (k ^ p) < d && (k ^= p);
      return k
    }
    var y = {
        blank: function() {
          return "N/A"
        }
      },
      c = {},
      n = 0,
      h = -1;
    return {
      reg: G,
      scramblers: y,
      getExtra: function(k, b) {
        if (k in c) return c[k](b)
      },
      mega: t,
      formatScramble: function(k) {
        return k.replace(/[$#]\{([^\}]+)\}/g,
          function(b, d) {
            return "$" == b[0] ? (b = [d], "[" == d[0] && (b = JSON.parse(d)), y[b[0]].apply(this, b)) : "#" == b[0] ? t.apply(this, JSON.parse("[" + d + "]")) : ""
          })
      },
      rndState: function(k, b) {
        if (void 0 != b) {
          var d = b.slice();
          void 0 == k && (k = d);
          if (0 == b[0]) return k.slice();
          b = [];
          for (var e = 0; e < k.length; e++) b.push(e), k[e] ? 1 == n && (d[e] = 1) : (d[e] = 0, b.pop());
          return 2 == n ? (0 > h++ && (h = mathlib.rn(65536)), b[r(h % b.length, ~~(h / b.length), b.length)]) : mathlib.rndProb(d)
        }
      },
      fixCase: function(k, b) {
        return void 0 != k ? k : 2 == n ? (0 > h++ && (h = mathlib.rn(65536)), r(h %
          b.length, ~~(h / b.length), b.length)) : 1 == n ? mathlib.rn(b.length) : mathlib.rndProb(b)
      },
      setEqPr: function(k) {
        n = ~~k
      },
      getEqPr: function() {
        return n
      },
      toTxt: function(k) {
        return k.replace(/<span[^>]*>(.*?)<\/span>/ig, "$1 ").replace(/~/g, "").replace(/\\n/g, "\n").replace(/`(.*?)`/g, "$1")
      }
    }
  }(mathlib.rn, mathlib.rndEl);
var scramble_333 = function(a, J, t, G, r) {
  function y() {
    return b(0xffffffffffff, 0xffffffffffff, 4294967295, 4294967295)
  }

  function c(U) {
    for (var fa = 0, ea = 0; ea < U.length; ea++) - 1 == U[ea] && fa++;
    return fa
  }

  function n(U, fa, ea) {
    for (var la = 0, pa = 0, qa = 0; qa < U.length; qa++) - 1 != U[qa] && (la += U[qa]);
    la %= ea;
    for (qa = 0; qa < U.length - 1; qa++) - 1 == U[qa] && (1 == fa-- ? U[qa] = ((ea << 4) - la) % ea : (U[qa] = G(ea), la += U[qa])), pa *= ea, pa += U[qa];
    1 == fa && U.splice(-1, 1, ((ea << 4) - la) % ea);
    return pa
  }

  function h(U, fa, ea) {
    for (var la = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], pa = 0; pa <
      U.length; pa++) - 1 != U[pa] && (la[U[pa]] = -1);
    for (var qa = pa = 0; pa < la.length; pa++) - 1 != la[pa] && (la[qa++] = la[pa]);
    var Fa;
    for (pa = 0; pa < U.length && 0 < fa; pa++)
      if (-1 == U[pa]) {
        qa = G(fa);
        for (U[pa] = la[qa]; 11 > qa; qa++) la[qa] = la[qa + 1];
        2 == fa-- && (Fa = pa)
      } t(a(U, U.length), U.length) == 1 - ea && (fa = U[pa - 1], U[pa - 1] = U[Fa], U[Fa] = fa);
    return a(U, U.length)
  }

  function k(U, fa) {
    if ("number" !== typeof U) return U;
    for (var ea = [], la = 0; la < fa; la++) {
      var pa = U & 15;
      ea[la] = 15 == pa ? -1 : pa;
      U /= 16
    }
    return ea
  }

  function b(U, fa, ea, la, pa, qa, Fa, Da, Oa) {
    qa = qa || H;
    Fa = Fa || H;
    U = k(U, 12);
    fa = k(fa, 12);
    ea = k(ea, 8);
    la = k(la, 8);
    var bb = "";
    do {
      var fb = fa.slice(),
        Ta = U.slice(),
        eb = la.slice(),
        Na = ea.slice(),
        Ra = n(fb, c(fb), 2),
        cb = n(eb, c(eb), 3);
      var $a = c(Ta);
      var Ya = c(Na);
      1 == $a && (h(Ta, $a, -1), $a = 0);
      1 == Ya && (h(Na, Ya, -1), Ya = 0);
      0 == $a && 0 == Ya ? ($a = a(Ta, 12), Ya = a(Na, 8)) : 0 != $a && 0 == Ya ? (Ya = a(Na, 8), $a = h(Ta, $a, t(Ya, 8))) : ($a = 0 == $a && 0 != Ya ? a(Ta, 12) : h(Ta, $a, -1), Ya = h(Na, Ya, t($a, 12)));
      if (0 != Ya + cb + $a + Ra) {
        bb = r(Fa);
        Ra = r(qa);
        cb = new mathlib.CubieCube;
        $a = new mathlib.CubieCube;
        for (Ya = 0; 12 > Ya; Ya++) cb.ea[Ya] = Ta[Ya] << 1 | fb[Ya],
          8 > Ya && (cb.ca[Ya] = eb[Ya] << 3 | Na[Ya]);
        for (Ya = 0; Ya < bb.length; Ya++) mathlib.CubieCube.CubeMult(mathlib.CubieCube.moveCube[bb[Ya]], cb, $a), cb.init($a.ca, $a.ea);
        for (Ya = 0; Ya < Ra.length; Ya++) mathlib.CubieCube.CubeMult(cb, mathlib.CubieCube.moveCube[Ra[Ya]], $a), cb.init($a.ca, $a.ea);
        pa && (cb.ori = mathlib.rn([1, 4, 8, 1, 1, 1, 24][pa]), cb.selfConj(), cb.ori = 0);
        fb = cb.toFaceCube();
        bb = f.solution(fb, 21, 1E9, 50, 2, Oa, Da)
      }
    } while (3 >= bb.length);
    return bb.replace(/ +/g, " ")
  }

  function d() {
    return b(0xffffffffffff, 0xffffffffffff, 1985229328,
      0)
  }

  function e() {
    return b(0xba9876543210, 0, 4294967295, 4294967295)
  }

  function l(U, fa, ea, la) {
    return b(0xba987654ffff, 65535, 1985282047, 65535, la)
  }

  function q(U, fa, ea, la) {
    U = F[scrMgr.fixCase(ea, P)][0];
    fa = Math.pow(16, U & 15);
    ea = Math.pow(16, U >> 8 & 15);
    return b(0xba9f7654ffff - 7 * fa, 64424574975 - (15 ^ U >> 4 & 1) * fa, 1986002943 - 11 * ea, 1048575 - (15 ^ U >> 12 & 3) * ea, la, m)
  }

  function g(U, fa, ea, la, pa) {
    var qa = fa[scrMgr.fixCase(la, ea)][0];
    fa = [
      [5, 10],
      [7, 19],
      [3, -1],
      [1, -1], null, null, null, null, [23, 12]
    ][qa & 15];
    ea = qa >> 4 & 1;
    la = [
      [8, 20, 9],
      [6, -1, 18],
      [0, -1, -1],
      [2, 11, -1],
      [-1, 15, 26]
    ][qa >> 8 & 15];
    qa = qa >> 12 & 3;
    U = U.split("");
    for (var Fa = 0; 3 > Fa; Fa++) 2 > Fa && 0 <= fa[Fa] && (U[fa[Fa]] = "BR".charAt(ea ^ Fa)), 0 <= la[Fa] && (U[la[Fa]] = "URB".charAt((qa + 3 + Fa) % 3));
    image.face3Image(U.join(""), pa)
  }

  function p(U, fa, ea, la) {
    return b(0xffff7654ffff, 0xffff0000ffff, 4294967295, 4294967295, la)
  }

  function x(U, fa, ea, la) {
    U = Ha[scrMgr.fixCase(ea, ya)];
    return b(U[2] + 0xba9876540000, 0, U[0] + 1985216512, U[1], la, m, m)
  }

  function u(U, fa, ea, la, pa) {
    var qa = Ha[scrMgr.fixCase(ea, ya)];
    pa = Ha[scrMgr.rndState(pa,
      ya)];
    U = [4, 7, 6, 5];
    fa = qa[0];
    ea = qa[1];
    qa = qa[2] + 0xba9800000000;
    for (var Fa = 0; 4 > Fa; Fa++) fa += (7 - (pa[0] >> 4 * Fa & 15)) * Math.pow(16, 7 - Fa), ea += (pa[1] >> 4 * Fa & 15) * Math.pow(16, 7 - Fa), qa += U[pa[2] >> 4 * Fa & 15] * Math.pow(16, U[Fa]);
    return b(qa, 0, fa, ea, la, Ma, H)
  }

  function M(U, fa) {
    var ea = Ha[U][3];
    if (!fa) return [ea, null, ka[U]];
    image.llImage.drawImage(ea, null, fa)
  }

  function T(U, fa, ea, la) {
    U = Y[scrMgr.fixCase(ea, Z)];
    return b(0xba987654ffff, 0, U[0] + 1985216512, U[1], la, m, m)
  }

  function L(U, fa, ea) {
    U = Y[scrMgr.fixCase(ea, Z)];
    fa = G(4);
    ea = [];
    for (var la =
        0; la < m.length; la++) ea.push(m[la].concat(D[fa]));
    return b(0xba98f6f4ffff, 4042326015, U[0] + 1985216512, U[1], 0, ea, m) + z[fa]
  }

  function K(U, fa, ea) {
    U = Y[fa][2].replace(/e/g, U || "U");
    if (!ea) return [U, null, oa[fa]];
    image.llImage.drawImage(U, null, ea)
  }

  function I(U, fa, ea, la) {
    return b(0xba9876543f1f, 0, 1985282047, 65535, la, m)
  }

  function w(U, fa, ea, la) {
    U = V[scrMgr.fixCase(ea, ca)];
    return b(0xba9876540000 + U[1], 0, 1984954368 + U[0], 0, la, m, m)
  }

  function B() {
    var U = G(4);
    return b(0xba98f6f4ffff, 4042326015, 1985229328, 0, 0, [D[U]], m) + z[U]
  }

  function A(U, fa, ea, la) {
    U = Y[scrMgr.fixCase(ea, Z)];
    return b(0xba987654ffff, 65535, U[0] + 1985216512, U[1], la, m, m)
  }

  function N(U, fa, ea, la) {
    return b(0xba987654ffff, 65535, 1985229328, 0, la)
  }

  function R(U, fa) {
    var ea = da[U].slice(1);
    2 == ea.length && (ea = ea.concat([
      [ea[0][1], ea[0][0]],
      [ea[1][1], ea[1][0]]
    ]));
    ea = ["DDDDDDDDD" + da[U][0], ea];
    if (!fa) return ea.concat([Ba[U]]);
    image.llImage.drawImage(ea[0], ea[1], fa)
  }

  function W(U, fa) {
    for (var ea = "", la = ta[U][4], pa = 0; 21 > pa; pa++) 4 == pa ? ea += "D" : (ea += la & 1 ? "D" : "G", la >>= 1);
    if (!fa) return [ea,
      null, Ia[U]
    ];
    image.llImage.drawImage(ea, null, fa)
  }

  function X(U, fa) {
    var ea = " x x2 x' z z'".split(" "),
      la = ["", "y", "y2", "y'"];
    if (0 == ra.length)
      for (var pa = 0; 24 > pa; pa++) {
        var qa = new mathlib.CubieCube;
        qa.selfMoveStr(la[pa & 3]);
        qa.selfMoveStr(ea[pa >> 2]);
        ra.push(qa.toPerm(null, null, null, !0))
      }
    pa = qa = 0;
    a: for (; 24 > pa; pa++) {
      for (var Fa = 0; 6 > Fa; Fa++)
        if (U[ra[pa][9 * Fa + 4]] != "URFDLB".charAt(Fa)) continue a;
      qa = [];
      for (Fa = 0; 54 > Fa; Fa++) qa[Fa] = U[ra[pa][Fa]];
      U = qa.join("");
      qa = pa;
      break
    }
    ea = ea[qa >> 2];
    "" != ea && fa.push(ea[0] + "'2 ".charAt("2'".indexOf(ea[1]) +
      1));
    la = la[qa & 3];
    "" != la && fa.push(la[0] + "'2 ".charAt("2'".indexOf(la[1]) + 1));
    return U
  }

  function S(U) {
    var fa = U.join("|");
    if (!za[fa]) {
      for (var ea = [], la = 0; la < U.length; la++) {
        var pa = new mathlib.CubieCube;
        pa.selfMoveStr(U[la]);
        ea.push(pa.toPerm(null, null, null, !0))
      }
      za[fa] = new grouplib.SubgroupSolver(ea);
      za[fa].initTables()
    }
    ea = "";
    if (1E8 > za[fa].sgsG.size()) {
      do ea = za[fa].sgsG.rndElem(), ea = za[fa].DissectionSolve(ea, 12, 20).map(function(qa) {
        return U[qa[0]] + ["", "2", "'"][qa[1] - 1]
      }).join(" "); while (2 >= ea.length);
      return ea.replace(/ +/g,
        " ")
    }
    do {
      ea = za[fa].sgsG.rndElem();
      for (la = 0; la < ea.length; la++) ea[la] = "URFDLB".charAt(~~(ea[la] / 9));
      la = [];
      ea = X(ea.join(""), la);
      ea = f.solution(ea, 21, 1E9, 50, 2)
    } while (3 >= ea.length);
    la.unshift(ea);
    return la.join(" ").replace(/ +/g, " ")
  }
  var f = new min2phase.Search,
    m = [
      [],
      [0],
      [1],
      [2]
    ],
    D = [
      [],
      [3, 14],
      [4, 13],
      [5, 12]
    ],
    z = ["", "x'", "x2", "x"],
    H = [
      []
    ],
    F = [
      [8192, 4, "Easy-01"],
      [4113, 4, "Easy-02"],
      [8210, 4, "Easy-03"],
      [4099, 4, "Easy-04"],
      [8195, 4, "RE-05"],
      [4114, 4, "RE-06"],
      [8194, 4, "RE-07"],
      [4115, 4, "RE-08"],
      [8211, 4, "REFC-09"],
      [4098,
        4, "REFC-10"
      ],
      [8208, 4, "REFC-11"],
      [4097, 4, "REFC-12"],
      [8209, 4, "REFC-13"],
      [4096, 4, "REFC-14"],
      [8193, 4, "SPGO-15"],
      [4112, 4, "SPGO-16"],
      [0, 4, "SPGO-17"],
      [17, 4, "SPGO-18"],
      [3, 4, "PMS-19"],
      [18, 4, "PMS-20"],
      [2, 4, "PMS-21"],
      [19, 4, "PMS-22"],
      [1, 4, "Weird-23"],
      [16, 4, "Weird-24"],
      [1024, 4, "CPEU-25"],
      [1041, 4, "CPEU-26"],
      [5120, 4, "CPEU-27"],
      [9233, 4, "CPEU-28"],
      [5137, 4, "CPEU-29"],
      [9216, 4, "CPEU-30"],
      [24, 4, "EPCU-31"],
      [8, 4, "EPCU-32"],
      [8200, 4, "EPCU-33"],
      [4104, 4, "EPCU-34"],
      [8216, 4, "EPCU-35"],
      [4120, 4, "EPCU-36"],
      [1048, 1, "ECP-37"],
      [5128,
        1, "ECP-38"
      ],
      [9224, 1, "ECP-39"],
      [5144, 1, "ECP-40"],
      [9240, 1, "ECP-41"],
      [1032, 1, "Solved-42"]
    ],
    P = mathlib.idxArray(F, 1);
  J = mathlib.idxArray(F, 2);
  for (var C = [], E = [], O = [], Q = 0; Q < F.length; Q++) F[Q][0] & 240 || (C.push(F[Q]), E.push(P[Q]), O.push(J[Q]));
  var ba = [],
    ja = [];
  for (Q = 0; 27 > Q; Q++) ba[Q] = ~~(Q / 9) << 12 | ~~(Q / 3) % 3 << 8 | Q % 3, ja[Q] = 1;
  var wa = [],
    Ca = [],
    sa = [];
  for (Q = 0; 216 > Q; Q++) {
    var ua = Q % 27,
      Ga = ~~(Q / 27);
    wa[Q] = [~~(ua / 9) % 3 << 12 | ~~(ua / 3) % 3 << 8 | ua % 3, (Ga >> 2 & 1) << 12 | (Ga >> 1 & 1) << 8 | Ga & 1];
    Ca[Q] = 1;
    sa[Q] = "WVLS;UB;UF;UF UB;UL;UB UL;UF UL;No Edge".split(";")[Ga] +
      "-" + (ua + 1)
  }
  var Ha = function() {
      for (var U = [], fa = [], ea = new mathlib.CubieCube, la = 0; 15552 > la; la++)
        if (!(U[la >> 5] >> (la & 31) & 1)) {
          var pa = la % 24,
            qa = ~~(la / 24) % 24,
            Fa = ~~(la / 24 / 24);
          if (mathlib.getNParity(qa, 4) == mathlib.getNParity(pa, 4)) {
            Fa = mathlib.setNOri([], Fa, 4, -3);
            qa = mathlib.setNPerm([], qa, 4, 0);
            var Da = mathlib.setNPerm([], pa, 4, 0);
            pa = [0, 0, 0, null, 0, null];
            for (var Oa = 0; 4 > Oa; Oa++) pa[0] += qa[Oa] << 4 * Oa, pa[1] += Fa[Oa] << 4 * Oa, pa[2] += Da[Oa] << 4 * Oa;
            for (var bb = 0; 16 > bb; bb++) {
              var fb = bb >> 2,
                Ta = bb & 3,
                eb = [],
                Na = [],
                Ra = [];
              for (Oa = 0; 4 > Oa; Oa++) eb[Oa +
                fb & 3] = Fa[Oa], Na[Oa + fb & 3] = qa[Oa] + Ta & 3, Ra[Oa + fb & 3] = Da[Oa] + Ta & 3;
              Oa = mathlib.getNOri(eb, 4, -3);
              Na = mathlib.getNPerm(Na, 4, 0);
              Ra = mathlib.getNPerm(Ra, 4, 0);
              Oa = 24 * (24 * Oa + Na) + Ra;
              U[Oa >> 5] >> (Oa & 31) & 1 || (U[Oa >> 5] |= 1 << (Oa & 31), pa[4]++)
            }
            for (Oa = 0; 12 > Oa; Oa++) ea.ea[Oa] = Da[Oa] << 1, 8 > Oa && (ea.ca[Oa] = Fa[Oa] << 3 | qa[Oa]);
            Fa = pa;
            qa = [0, 1, 2, 3, 4, 5, 6, 7, 8, 18, 19, 20, 9, 10, 11, 45, 46, 47, 36, 37, 38];
            Oa = ea.toPerm();
            Da = [];
            for (bb = 0; bb < qa.length; bb++) Da[bb] = "DDDDDDDDDLLLLLLLLLFFFFFFFFFUUUUUUUUURRRRRRRRRBBBBBBBBB" [Oa[qa[bb]]];
            qa = Da.join("");
            Fa[3] =
              qa;
            0 < la && fa.push(pa)
          }
        } U = {
        0: "O",
        18: "U",
        33: "T",
        258: "L",
        273: "aS",
        546: "S",
        4386: "Pi",
        4626: "H"
      };
      ea = {};
      for (Oa = 0; Oa < fa.length; Oa++) pa = fa[Oa], la = U[pa[1]], ea[la] = ea[la] || [], Fa = ea[la], qa = Fa.indexOf(pa[0]), -1 == qa ? (qa = Fa.length, Fa.push(pa[0], 1)) : Fa[qa + 1]++, pa[5] = la + ((qa >> 1) + 1) + "-" + ea[la][qa + 1];
      return fa
    }(),
    ya = mathlib.idxArray(Ha, 4),
    ka = mathlib.idxArray(Ha, 5),
    Y = [
      [12816, 8481, "FeFeeeBeBLGRDGDRGLDGD", 2, "H-1"],
      [8961, 4626, "ReLeeeReLBGBDGDFGFDGD", 2, "H-2"],
      [4611, 4626, "ReBeeeLeBFGRDGDLGFDGD", 4, "H-3"],
      [8211, 4626, "LeReeeFeFRGLDGDBGBDGD",
        4, "H-4"
      ],
      [12321, 4128, "DeLeeeReDBGRFGBDGFLGD", 4, "L-1"],
      [4611, 513, "DeReeeLeDFGBRGFDGLBGD", 4, "L-2"],
      [8961, 258, "DeBeeeLeDFGRFGRDGLBGD", 4, "L-3"],
      [12816, 4128, "DeLeeeFeDRGFLGBDGBRGD", 4, "L-4"],
      [12546, 4128, "DeLeeeLeDFGBRGBDGRFGD", 4, "L-5"],
      [8211, 513, "DeReeeReDBGLBGFDGFLGD", 4, "L-6"],
      [12816, 4386, "LeFeeeReFBGDRGLDGBDGD", 4, "Pi-1"],
      [8961, 8466, "FeLeeeFeRRGDBGBDGLDGD", 4, "Pi-2"],
      [4611, 4641, "ReLeeeReLBGDFGBDGFDGD", 4, "Pi-3"],
      [12546, 4386, "BeFeeeFeBRGDLGLDGRDGD", 4, "Pi-4"],
      [8211, 4641, "BeLeeeLeFFGDRGBDGRDGD", 4, "Pi-5"],
      [12321,
        4386, "BeReeeLeBFGDLGFDGRDGD", 4, "Pi-6"
      ],
      [12816, 8736, "ReBeeeFeDRGFLGDLGDBGD", 4, "S-1"],
      [8961, 546, "BeReeeLeDFGRFGDBGDLGD", 4, "S-2"],
      [12321, 8736, "BeReeeFeDRGFLGDBGDLGD", 4, "S-3"],
      [8211, 8706, "ReBeeeLeDFGRFGDLGDBGD", 4, "S-4"],
      [12546, 8736, "FeBeeeLeDFGBRGDLGDRGD", 4, "S-5"],
      [4611, 8706, "LeReeeFeDRGLBGDBGDFGD", 4, "S-6"],
      [4611, 4098, "BeLeeeDeDBGRFGDFGRDGL", 4, "T-1"],
      [12546, 8448, "ReBeeeDeDLGBRGDLGFDGF", 4, "T-2"],
      [8961, 528, "BeFeeeDeDBGFLGDRGRDGL", 4, "T-3"],
      [12816, 8448, "FeFeeeDeDBGBRGDRGLDGL", 4, "T-4"],
      [8211, 4098, "BeBeeeDeDLGRFGDLGRDGF",
        4, "T-5"
      ],
      [12321, 8448, "FeBeeeDeDRGRFGDLGLDGB", 4, "T-6"],
      [8961, 288, "LeLeeeDeDFGBRGBDGDFGR", 4, "U-1"],
      [12816, 4608, "LeReeeDeDBGBRGFDGDFGL", 4, "U-2"],
      [12321, 4608, "FeFeeeDeDBGBRGLDGDRGL", 4, "U-3"],
      [8211, 8193, "BeFeeeDeDFGBRGLDGDLGR", 4, "U-4"],
      [4611, 8193, "ReFeeeDeDBGRFGLDGDBGL", 4, "U-5"],
      [12546, 4608, "LeBeeeDeDBGRFGRDGDFGL", 4, "U-6"],
      [12816, 4353, "LeFeeeDeRRGFDGLDGBDGB", 4, "aS-1"],
      [8961, 4368, "ReFeeeDeLRGBDGLDGFDGB", 4, "aS-2"],
      [12321, 4353, "LeBeeeDeFFGLDGRDGBDGR", 4, "aS-3"],
      [8211, 4113, "LeFeeeDeBFGRDGLDGBDGR", 4, "aS-4"],
      [4611, 4113, "FeBeeeDeLFGBDGRDGLDGR", 4, "aS-5"],
      [12546, 4353, "FeBeeeDeRBGFDGRDGLDGL", 4, "aS-6"],
      [12321, 0, "DeDeeeDeDBGRFGBRGFLGL", 4, "O-Adj"],
      [8961, 0, "DeDeeeDeDBGFLGRFGBRGL", 1, "O-Diag"],
      [12816, 0, "DeDeeeDeDBGBRGRFGFLGL", 1, "O-AUF"]
    ],
    Z = mathlib.idxArray(Y, 3),
    oa = mathlib.idxArray(Y, 4),
    V = [
      [205840, 12816, "FBar-1"],
      [205840, 12546, "FBar-2"],
      [205840, 12321, "FBar-3"],
      [205840, 8961, "FBar-4"],
      [205840, 8496, "FBar-5"],
      [205840, 8211, "FBar-6"],
      [205840, 4896, "FBar-7"],
      [205840, 4611, "FBar-8"],
      [205840, 4146, "FBar-9"],
      [205840, 786, "FBar-10"],
      [205840, 561, "FBar-11"],
      [205840, 291, "FBar-12"],
      [205825, 12801, "2Opp-1"],
      [205825, 12576, "2Opp-2"],
      [205825, 12306, "2Opp-3"],
      [205825, 8976, "2Opp-4"],
      [205825, 8451, "2Opp-5"],
      [205825, 8241, "2Opp-6"],
      [205825, 4866, "2Opp-7"],
      [205825, 4656, "2Opp-8"],
      [205825, 4131, "2Opp-9"],
      [205825, 801, "2Opp-10"],
      [205825, 531, "2Opp-11"],
      [205825, 306, "2Opp-12"],
      [201760, 12801, "ROpp-1"],
      [201760, 12576, "ROpp-2"],
      [201760, 12306, "ROpp-3"],
      [201760, 8976, "ROpp-4"],
      [201760, 8451, "ROpp-5"],
      [201760, 8241, "ROpp-6"],
      [201760, 4866, "ROpp-7"],
      [201760, 4656,
        "ROpp-8"
      ],
      [201760, 4131, "ROpp-9"],
      [201760, 801, "ROpp-10"],
      [201760, 531, "ROpp-11"],
      [201760, 306, "ROpp-12"],
      [201730, 12816, "RBar-1"],
      [201730, 12546, "RBar-2"],
      [201730, 12321, "RBar-3"],
      [201730, 8961, "RBar-4"],
      [201730, 8496, "RBar-5"],
      [201730, 8211, "RBar-6"],
      [201730, 4896, "RBar-7"],
      [201730, 4611, "RBar-8"],
      [201730, 4146, "RBar-9"],
      [201730, 786, "RBar-10"],
      [201730, 561, "RBar-11"],
      [201730, 291, "RBar-12"],
      [197665, 12816, "2Bar-1"],
      [197665, 12546, "2Bar-2"],
      [197665, 12321, "2Bar-3"],
      [197665, 8961, "2Bar-4"],
      [197665, 8496, "2Bar-5"],
      [197665,
        8211, "2Bar-6"
      ],
      [197665, 4896, "2Bar-7"],
      [197665, 4611, "2Bar-8"],
      [197665, 4146, "2Bar-9"],
      [197665, 786, "2Bar-10"],
      [197665, 561, "2Bar-11"],
      [197665, 291, "2Bar-12"],
      [197650, 12801, "FOpp-1"],
      [197650, 12576, "FOpp-2"],
      [197650, 12306, "FOpp-3"],
      [197650, 8976, "FOpp-4"],
      [197650, 8451, "FOpp-5"],
      [197650, 8241, "FOpp-6"],
      [197650, 4866, "FOpp-7"],
      [197650, 4656, "FOpp-8"],
      [197650, 4131, "FOpp-9"],
      [197650, 801, "FOpp-10"],
      [197650, 531, "FOpp-11"],
      [197650, 306, "FOpp-12"]
    ],
    ca = [],
    ia = [];
  for (Q = 0; Q < V.length; Q++) ca[Q] = 1, ia[Q] = V[Q][2];
  var ma = [
      [4146,
        12816, 1, "H"
      ],
      [12546, 12816, 4, "Ua"],
      [12321, 12816, 4, "Ub"],
      [8961, 12816, 2, "Z"],
      [12816, 12321, 4, "Aa"],
      [12816, 12546, 4, "Ab"],
      [12816, 8961, 2, "E"],
      [12306, 12801, 4, "F"],
      [8496, 12321, 4, "Ga"],
      [4896, 12546, 4, "Gb"],
      [12321, 12546, 4, "Gc"],
      [12546, 12321, 4, "Gd"],
      [12801, 12801, 4, "Ja"],
      [12576, 12801, 4, "Jb"],
      [4656, 12306, 1, "Na"],
      [12306, 12306, 1, "Nb"],
      [531, 12801, 4, "Ra"],
      [8976, 12801, 4, "Rb"],
      [4656, 12801, 4, "T"],
      [12576, 12306, 4, "V"],
      [12801, 12306, 4, "Y"]
    ],
    xa = mathlib.idxArray(ma, 2),
    Ba = mathlib.idxArray(ma, 3),
    da = [
      ["BFBRLRFBFLRL", [1, 7],
        [3, 5]
      ],
      ["BRBRLRFFFLBL", [3, 7],
        [7, 5],
        [5, 3]
      ],
      ["BLBRBRFFFLRL", [3, 5],
        [5, 7],
        [7, 3]
      ],
      ["LFLBRBRBRFLF", [1, 5],
        [3, 7]
      ],
      ["LBBRRLBFRFLF", [0, 2],
        [2, 6],
        [6, 0]
      ],
      ["RBFLRRFFLBLB", [0, 6],
        [6, 8],
        [8, 0]
      ],
      ["LBRFRBRFLBLF", [0, 6],
        [2, 8]
      ],
      ["BFRFRBRBFLLL", [1, 7],
        [2, 8]
      ],
      ["BRRFLBRBFLFL"],
      ["BFRFBBRLFLRL"],
      ["BFRFLBRRFLBL"],
      ["BLRFFBRBFLRL"],
      ["BBRFFBRRFLLL", [1, 5],
        [2, 8]
      ],
      ["LBBRLLBRRFFF", [2, 8],
        [5, 7]
      ],
      ["FBBRLLBFFLRR", [2, 6],
        [3, 5]
      ],
      ["BBFLLRFFBRRL", [0, 8],
        [3, 5]
      ],
      ["LLBRBLBFRFRF", [1, 3],
        [2, 8]
      ],
      ["RBFLFRFLLBRB", [2, 8],
        [3, 7]
      ],
      ["BBRFLBRFFLRL", [2, 8],
        [3, 5]
      ],
      ["BBFLFRFRBRLL",
        [0, 8],
        [1, 5]
      ],
      ["BBFLRRFLBRFL", [0, 8],
        [1, 3]
      ]
    ],
    ta = [
      [0, 0, 1, "PLL", 255],
      [4369, 4626, 2, "Point-1", 965120],
      [4369, 4386, 4, "Point-2", 907776],
      [4369, 546, 4, "Point-3", 374304],
      [4369, 273, 4, "Point-4", 447360],
      [17, 8226, 4, "Square-5", 538123],
      [17, 4113, 4, "Square-6", 396054],
      [17, 8706, 4, "SLBS-7", 79402],
      [17, 273, 4, "SLBS-8", 410514],
      [17, 4368, 4, "Fish-9", 152458],
      [17, 8736, 4, "Fish-10", 627788],
      [17, 546, 4, "SLBS-11", 595470],
      [17, 4353, 4, "SLBS-12", 281363],
      [257, 8226, 4, "Knight-13", 108088],
      [257, 273, 4, "Knight-14", 181144],
      [257, 546, 4, "Knight-15",
        566809
      ],
      [257, 4113, 4, "Knight-16", 166684],
      [4369, 258, 4, "Point-17", 308097],
      [4369, 18, 4, "Point-18", 300805],
      [4369, 33, 4, "Point-19", 825861],
      [4369, 0, 1, "CO-20", 299685],
      [0, 4626, 2, "OCLL-21", 83290],
      [0, 4386, 4, "OCLL-22", 672858],
      [0, 18, 4, "OCLL-23", 82170],
      [0, 33, 4, "OCLL-24", 66014],
      [0, 258, 4, "OCLL-25", 132222],
      [0, 273, 4, "OCLL-26", 133470],
      [0, 546, 4, "OCLL-27", 74874],
      [17, 0, 4, "CO-28", 4783],
      [17, 528, 4, "Awkward-29", 70542],
      [17, 8448, 4, "Awkward-30", 144042],
      [17, 33, 4, "P-31", 328598],
      [17, 4098, 4, "P-32", 22059],
      [257, 33, 4, "T-33", 99228],
      [257,
        528, 4, "C-34", 172728
      ],
      [17, 4128, 4, "Fish-35", 303569],
      [17, 258, 4, "W-36", 803475],
      [17, 8208, 4, "Fish-37", 13195],
      [17, 513, 4, "W-38", 72238],
      [257, 4128, 4, "BLBS-39", 100924],
      [257, 258, 4, "BLBS-40", 574105],
      [17, 4608, 4, "Awkward-41", 86698],
      [17, 288, 4, "Awkward-42", 38221],
      [17, 18, 4, "P-43", 918166],
      [17, 8193, 4, "P-44", 14891],
      [257, 18, 4, "T-45", 688796],
      [257, 288, 4, "C-46", 276579],
      [17, 4641, 4, "L-47", 338706],
      [17, 4386, 4, "L-48", 677386],
      [17, 8466, 4, "L-49", 935442],
      [17, 8721, 4, "L-50", 967760],
      [257, 4641, 4, "I-51", 109336],
      [257, 4386, 4, "I-52", 342338],
      [17, 8481, 4, "L-53", 345874],
      [17, 4626, 4, "L-54", 87818],
      [257, 8481, 2, "I-55", 116504],
      [257, 4626, 2, "I-56", 698904],
      [257, 0, 2, "CO-57", 33469]
    ],
    na = mathlib.idxArray(ta, 2),
    Ia = mathlib.idxArray(ta, 3),
    Ka = [
      [],
      [9],
      [10],
      [11]
    ],
    Ma = [];
  for (Q = 0; 16 > Q; Q++) Ma.push(m[Q >> 2].concat(Ka[Q & 3]));
  var Ua = ["", "y", "y2", "y'"];
  ua = "UR UF UL UB DR DF DL DB RF LF LB RB URF UFL ULB UBR DFR DLF DBL DRB".split(" ");
  for (Q = 0; 20 > Q; Q++) Ga = ua[Q], ua[Q + 20] = (2 == Ga.length ? "OriE-" : "OriC-") + Ga, ua[Q] = (2 == Ga.length ? "PermE-" : "PermC-") + Ga;
  Q = mathlib.valuedArray(40,
    0);
  var ra = [],
    za = {};
  scrMgr.reg("333", y)("333fm", function() {
    return "R' U' F " + b(0xffffffffffff, 0xffffffffffff, 4294967295, 4294967295, 0, void 0, void 0, 2, 1) + "R' U' F"
  })("edges", d)("corners", e)("333custom", function(U, fa, ea, la) {
    var pa = fa = U = 0,
      qa = 0,
      Fa = 4352;
    ea = ea || mathlib.valuedArray(40, 1);
    for (var Da = 0; 12 > Da; Da++) Fa += (ea[Da] ? 69632 : 0) + (ea[Da + 20] ? 16 : 0), U += (ea[Da] ? 15 : Da) * Math.pow(16, Da), fa += (ea[Da + 20] ? 15 : 0) * Math.pow(16, Da);
    for (Da = 0; 8 > Da; Da++) Fa += (ea[Da + 12] ? 65792 : 0) + (ea[Da + 32] ? 1 : 0), pa += (ea[Da + 12] ? 15 : Da) * Math.pow(16,
      Da), qa += (ea[Da + 32] ? 15 : 0) * Math.pow(16, Da);
    return 0 == (Fa & 1887470) ? "U' U " : b(U, fa, pa, qa, la)
  }, [ua, Q])("ll", l)("lsll2", q, [J, P, g.bind(null, "GGGGDGGGGGGGGRRGRRGGGBBGBBG", F, P)])("f2l", p)("zbll", x, [ka, ya, M])("zbllx2", u, [ka, ya, M])("zzll", I)("zbls", q, [J, P, g.bind(null, "GGGGDGGGGGGGGRRGRRGGGBBGBBG", F, P)])("ttll", w, [ia, ca, function(U, fa) {
    for (var ea = [], la = V[U], pa = 3; 0 <= pa; pa--) ea.push(["FR", "LF", "BL", "RB", "GG"][la[0] >> 4 * pa & 15]), ea.push("RFLB".charAt(la[1] >> 4 * pa & 15));
    ea = ea.join("");
    ea = ea.slice(7) + ea.slice(0, 7);
    ea = ["GDDDDDDDD" + ea, null];
    if (!fa) return ea.concat([ia[U]]);
    image.llImage.drawImage(ea[0], ea[1], fa)
  }])("eols", function(U, fa, ea, la) {
    U = C[scrMgr.fixCase(ea, E)][0];
    fa = Math.pow(16, U >> 8 & 15);
    return b(0xba9f7654ffff - 7 * Math.pow(16, U & 15), 0, 1986002943 - 11 * fa, 1048575 - (15 ^ U >> 12 & 3) * fa, la, m)
  }, [O, E, g.bind(null, "GDGDDDGDGGGGGRRGRRGGGBBDBBG", C, E)])("wvls", function(U, fa, ea, la) {
    U = ba[scrMgr.fixCase(ea, ja)];
    return b(0xba9f7654ff8f, 0, 1986002767, 983072 | U, la)
  }, ["Oriented Rectangle-1 Rectangle-2 Tank-1 Bowtie-1 Bowtie-3 Tank-2 Bowtie-2 Bowtie-4 Snake-1 Adjacent-1 Adjacent-2 Gun-Far Sune-1 Pi-Near Gun-Back Pi-Front H-Side Snake-2 Adjacent-3 Adjacent-4 Gun-Sides H-Front Pi-Back Gun-Near Pi-Far Sune-2".split(" "),
    ja,
    function(U, fa) {
      U = ba[scrMgr.fixCase(U, ja)];
      var ea = ["DGG", "GDG", "GGD"];
      ea = ea[U & 3] + ea[U >> 8 & 3] + ea[U >> 12 & 3];
      image.llImage.drawImage("3D6DDDBB0RR21G87G54GU".replace(/[0-9]/g, function(la) {
        return ea[~~la]
      }), null, fa)
    }
  ])("vls", function(U, fa, ea, la) {
    U = wa[scrMgr.fixCase(ea, Ca)];
    return b(0xba9f7654ff8f, 64424509440 + U[1], 1986002767, 983072 + U[0], la, [
      [2]
    ])
  }, [sa, Ca, function(U, fa) {
    U = wa[scrMgr.fixCase(U, Ca)];
    var ea = ["DGG", "GDG", "GGD"];
    ea = ea[U[0] & 3] + ea[U[0] >> 8 & 3] + ea[U[0] >> 12 & 3];
    var la = ["DG", "GD"];
    la = la[U[1] & 3] + la[U[1] >>
      8 & 3] + la[U[1] >> 12 & 3];
    image.llImage.drawImage("6a0eDR3cR4dUFF21b87f5".replace(/[0-9]/g, function(pa) {
      return ea[~~pa]
    }).replace(/[a-z]/g, function(pa) {
      return la[pa.charCodeAt(0) - 97]
    }), null, fa)
  }])("lse", B)("cmll", L, [oa, Z, K.bind(null, "G")])("cll", A, [oa, Z, K.bind(null, "G")])("coll", T, [oa, Z, K.bind(null, "D")])("ell", N)("pll", function(U, fa, ea, la) {
    U = ma[scrMgr.fixCase(ea, xa)];
    return b(U[0] + 0xba9876540000, 0, U[1] + 1985216512, 0, la, m, m)
  }, [Ba, xa, R])("oll", function(U, fa, ea, la) {
    U = ta[scrMgr.fixCase(ea, na)];
    return b(0xba987654ffff,
      U[0], 1985282047, U[1], la, m, m)
  }, [Ia, na, W])("2gll", function(U, fa, ea, la) {
    return b(0xba987654ffff, 0, 1985229328, 65535, la, m)
  })("sbrx", function(U, fa, ea) {
    U = G(4);
    return b(0xfa9ff6ffffff, 0xf00ff0ffffff, 4133486591, 4027580415, 0, [D[U]]) + z[U]
  })("half", S.bind(null, "U2 R2 F2 D2 L2 B2".split(" ")))("333drud", S.bind(null, "U R2 F2 D L2 B2".split(" ")))("3gen_F", S.bind(null, ["U", "R", "F"]))("3gen_L", S.bind(null, ["U", "R", "L"]))("2gen", S.bind(null, ["U", "R"]))("2genl", S.bind(null, ["U", "L"]))("RrU", S.bind(null, ["R", "Rw", "U"]))("roux",
    S.bind(null, ["M", "U"]))("mt3qb", function() {
    var U = mathlib.rn(4);
    return b(0xffff765fffff, 0xffff000fffff, 4133486591, 4027580415, 0, [Ka[U]]) + Ua[U]
  })("mteole", function() {
    var U = mathlib.rn(4),
      fa = mathlib.rn(4);
    return b(0xba98765fffff + 4294967296 * (17767 & 15 << 4 * U), 1048575 + 4294967296 * (15 << 4 * U), 4133486591, 4027580415, 0, [Ka[fa]]) + Ua[fa]
  })("mttdr", function() {
    return b(0xba98765fffff, 0, 4133486591, 4027580415)
  })("mt6cp", function() {
    return b(0xba98765fffff, 0, 4133486591, 0)
  })("mtl5ep", function() {
    return b(0xba98765fffff, 0, 1985229328,
      0)
  })("mtcdrll", function() {
    return b(0xba98765fffff, 0, 1985282047, 65535)
  })("easyc", function(U, fa, ea, la) {
    U = cross.getEasyCross(fa);
    return b(U[0], U[1], 4294967295, 4294967295, la)
  })("easyxc", function(U, fa, ea, la) {
    U = cross.getEasyXCross(fa);
    return b(U[0], U[1], U[2], U[3], la)
  })("eoline", function(U, fa, ea, la) {
    return b(0xffff7f5fffff, 0, 4294967295, 4294967295, la)
  })("eocross", function(U, fa, ea, la) {
    return b(0xffff7654ffff, 0, 4294967295, 4294967295, la)
  });
  return {
    getRandomScramble: y,
    getEdgeScramble: d,
    getCornerScramble: e,
    getLLScramble: l,
    getLSLLScramble: q,
    getCOLLScramble: T,
    getZBLLScramble: x,
    getZBLLx2Scramble: u,
    getZZLLScramble: I,
    getTTLLScramble: w,
    getF2LScramble: p,
    getLSEScramble: B,
    getCMLLScramble: L,
    getCLLScramble: A,
    getELLScramble: N,
    getAnyScramble: b,
    getPLLImage: R,
    getOLLImage: W,
    getCOLLImage: K,
    getZBLLImage: M,
    genFacelet: function(U) {
      return f.solution(U, 21, 1E9, 50, 2)
    },
    solvFacelet: function(U) {
      return f.solution(U, 21, 1E9, 50, 0)
    }
  }
}(mathlib.getNPerm, mathlib.setNPerm, mathlib.getNParity, mathlib.rn, mathlib.rndEl);
var scramble_222 = function(a) {
  function J(X, S) {
    mathlib.acycle(X, h[S])
  }

  function t(X, S) {
    mathlib.acycle(X, h[S], 1, k[S])
  }

  function G(X, S) {
    X = mathlib.setNPerm([], X, 7);
    S = b.set([], S);
    for (var f = [], m = 0; 24 > m; m++) f[m] = m >> 2;
    mathlib.fillFacelet(d, f, X, S, 4);
    for (m = 0; 24 > m; m += 4)
      if ((1 << f[m] | 1 << f[m + 3]) & (1 << f[m + 1] | 1 << f[m + 2])) return !1;
    return !0
  }

  function r(X, S, f) {
    var m = 0,
      D = 4;
    S = [0, 1, 2, 3];
    var z = [0, 0, 0, 0, 0, 0, 0];
    if ("222tcp" == X) m = p[scrMgr.fixCase(f, K)], z = [0, 0, 0, 0, 1, 0, 0], S = S.concat(q[0]);
    else if ("222tcn" == X) m = x[scrMgr.fixCase(f, w)],
      z = [0, 0, 0, 0, 2, 0, 0], S = S.concat(q[0]);
    else if ("222tc" == X)
      for (z = scrMgr.fixCase(f, A), m = u[z].slice(), z = [0, 0, 0, 0, 8 > z ? 1 : 2, 0, 0], S = S.concat(q[0]), X = mathlib.rndPerm(4), f = m[0] = 0; 4 > f; f++) m[0] |= X[f] << 4 * f;
    else if ("222eg0" == X) m = g[scrMgr.fixCase(f, T)], S = S.concat(q[0]);
    else if ("222eg1" == X) m = g[scrMgr.fixCase(f, T)], S = S.concat(q[2 + a(4)]);
    else if ("222eg2" == X) m = g[scrMgr.fixCase(f, T)], S = S.concat(q[1]);
    else if ("222lsall" == X) {
      S = S.concat(q[0]);
      X = mathlib.rndPerm(4);
      X.push(X[3]);
      X[3] = 4;
      m = [0, M[scrMgr.fixCase(f, R)][0]];
      for (f = 0; 5 >
        f; f++) m[0] |= X[f] << 4 * f;
      D = 5
    }
    for (f = a(4); 0 < f--;) J(S, 0);
    X = S.slice();
    for (f = 0; f < D; f++) S[f] = X[m[0] >> 4 * f & 15], z[f] = m[1] >> 4 * f & 15;
    for (m = a(4); 0 < m--;) t(z, 0), J(S, 0);
    S = mathlib.getNPerm(S, 7);
    z = b.get(z);
    return n.toStr(n.search([S, z], 9).reverse(), "URF", "'2 ")
  }

  function y(X, S, f, m, D) {
    S = S[m];
    for (var z = [], H = 0; 4 > H; H++)
      if (!X || "all" == X || "ori" == X)
        for (var F = S[0] >> (H << 2) & 15, P = S[1] >> (H << 2) & 15, C = "all" == X ? "DLFURB" : "DGGUGG", E = 0; 3 > E; E++) {
          var O = e.indexOf(d[H][E]);
          z[O] = C.charAt(d[F][(E + 3 - P) % 3] >> 2)
        } else if ("ls" == X)
          for (P = S[0] >> (H << 2) &
            15, E = 0; 3 > E; E++) O = e.indexOf(d[H][E]), z[O] = "DGU".charAt(0 == (E + 3 - P) % 3 ? 3 == H ? 2 : 0 : 1);
    z = z.join("");
    if (!D) return [z, null, f[m]];
    image.llImage.drawImage(z, null, D)
  }

  function c(X, S, f) {
    var m = "222o" == X ? 0 : 9;
    do {
      var D = 2;
      if ("222o" == X || "222so" == X) {
        var z = a(5040);
        var H = a(729);
        D = 3
      } else if ("222easy" == X) {
        D = Math.min(11, Math.max(4, ~~S || 4));
        do z = a(5040), H = a(729); while (null == n.search([z, H], 0, D));
        D = 3
      } else if ("222eg" == X) {
        H = l[f & 7];
        z = [0, 2, 3, 4, 5, 1][f >> 3];
        z = mathlib.setNPerm([0, 0, 0, 0].concat(q[z]), a(24), 4);
        z = mathlib.getNPerm(z, 7);
        var F =
          a(4);
        for (H = b.set([], H); 0 < F--;) t(H, 0);
        H = b.get(H)
      } else {
        if (/^222eg[012]$/.exec(X)) return c("222eg", S, [0, 8, 40][~~X[5]] + f);
        if ("222nb" == X) {
          do z = a(5040), H = a(729); while (!G(z, H))
        }
      }
    } while (0 == z && 0 == H || null != n.search([z, H], 0, D));
    return n.toStr(n.search([z, H], m).reverse(), "URF", "'2 ")
  }
  var n = new mathlib.Solver(3, 3, [
      [0, [J, "p", 7], 5040],
      [0, [t, "o", 7, -3], 729]
    ]),
    h = [
      [0, 2, 3, 1],
      [0, 1, 5, 4],
      [0, 4, 6, 2]
    ],
    k = [null, [0, 1, 0, 1, 3],
      [1, 0, 1, 0, 3]
    ],
    b = new mathlib.Coord("o", 7, -3),
    d = [
      [3, 4, 9],
      [1, 20, 5],
      [2, 8, 17],
      [0, 16, 21],
      [13, 11, 6],
      [15, 7, 22],
      [12, 19, 10]
    ],
    e = [0, 1, 2, 3, 8, 9, 4, 5, 20, 21, 16, 17],
    l = [0, 17, 5, 14, 8, 1, 2, 4],
    q = [
      [4, 5, 6],
      [4, 6, 5],
      [6, 5, 4],
      [5, 4, 6],
      [5, 6, 4],
      [6, 4, 5]
    ],
    g = [
      [12816, 4641, 2, "H-1"],
      [12576, 4641, 2, "H-2"],
      [8976, 4641, 4, "H-3"],
      [12306, 4641, 4, "H-4"],
      [786, 528, 4, "L-1"],
      [8976, 528, 4, "L-2"],
      [531, 528, 4, "L-3"],
      [12816, 528, 4, "L-4"],
      [8211, 528, 4, "L-5"],
      [12306, 528, 4, "L-6"],
      [12816, 4626, 4, "Pi-1"],
      [531, 4626, 4, "Pi-2"],
      [8976, 4626, 4, "Pi-3"],
      [8211, 4626, 4, "Pi-4"],
      [12306, 4626, 4, "Pi-5"],
      [786, 4626, 4, "Pi-6"],
      [12816, 8736, 4, "S-1"],
      [531, 8736, 4, "S-2"],
      [786, 8736, 4, "S-3"],
      [12306, 8736, 4, "S-4"],
      [8211, 8736, 4, "S-5"],
      [8976, 8736, 4, "S-6"],
      [8976, 4128, 4, "T-1"],
      [8211, 4128, 4, "T-2"],
      [531, 4128, 4, "T-3"],
      [12816, 4128, 4, "T-4"],
      [12306, 4128, 4, "T-5"],
      [786, 4128, 4, "T-6"],
      [531, 8208, 4, "U-1"],
      [12816, 8208, 4, "U-2"],
      [786, 8208, 4, "U-3"],
      [12306, 8208, 4, "U-4"],
      [8976, 8208, 4, "U-5"],
      [8211, 8208, 4, "U-6"],
      [12816, 4113, 4, "aS-1"],
      [531, 4113, 4, "aS-2"],
      [786, 4113, 4, "aS-3"],
      [12306, 4113, 4, "aS-4"],
      [8976, 4113, 4, "aS-5"],
      [8211, 4113, 4, "aS-6"]
    ],
    p = [
      [291, 545, 4, "Hammer-1"],
      [12321, 545, 4, "Hammer-2"],
      [306, 545, 4, "Hammer-3"],
      [561, 545, 4, "Hammer-4"],
      [801, 545, 4, "Hammer-5"],
      [8961, 545, 4, "Hammer-6"],
      [291, 4130, 4, "Spaceship-1"],
      [8961, 4130, 4, "Spaceship-2"],
      [4896, 4130, 4, "Spaceship-3"],
      [12321, 4130, 4, "Spaceship-4"],
      [12306, 4130, 4, "Spaceship-5"],
      [561, 4130, 4, "Spaceship-6"],
      [8241, 2, 4, "Stollery-1"],
      [12576, 2, 4, "Stollery-2"],
      [12801, 2, 4, "Stollery-3"],
      [8451, 2, 4, "Stollery-4"],
      [561, 2, 4, "Stollery-5"],
      [8496, 2, 4, "Stollery-6"],
      [291, 8738, 1, "Pinwheel-1"],
      [4146, 8738, 1, "Pinwheel-2"],
      [12801, 8738, 4, "Pinwheel-3"],
      [8241, 272, 2, "2Face-1"],
      [12546, 272, 4, "2Face-2"],
      [531, 272, 2, "2Face-3"],
      [12321, 272, 4, "2Face-4"],
      [4866, 290, 4, "Turtle-1"],
      [4146, 290, 4, "Turtle-2"],
      [12801, 290, 4, "Turtle-3"],
      [4656, 290, 4, "Turtle-4"],
      [8976, 290, 4, "Turtle-5"],
      [801, 290, 4, "Turtle-6"],
      [12816, 4370, 4, "Pinwheel Poser-1"],
      [12576, 4370, 4, "Pinwheel Poser-2"],
      [12801, 4370, 4, "Pinwheel Poser-3"],
      [8451, 4370, 4, "Pinwheel Poser-4"],
      [8976, 4370, 4, "Pinwheel Poser-5"],
      [8496, 4370, 4, "Pinwheel Poser-6"],
      [8241, 17, 4, "Gun-1"],
      [4146, 17, 4, "Gun-2"],
      [306, 17, 4, "Gun-3"],
      [12321, 17, 4, "Gun-4"],
      [8976, 17, 4, "Gun-5"],
      [8496, 17, 4,
        "Gun-6"
      ]
    ],
    x = [
      [4866, 4609, 4, "Hammer-1"],
      [12321, 4609, 4, "Hammer-2"],
      [8976, 4609, 4, "Hammer-3"],
      [12801, 4609, 4, "Hammer-4"],
      [4611, 4609, 4, "Hammer-5"],
      [12576, 4609, 4, "Hammer-6"],
      [291, 4114, 4, "Spaceship-1"],
      [4146, 4114, 4, "Spaceship-2"],
      [786, 4114, 4, "Spaceship-3"],
      [12801, 4114, 4, "Spaceship-4"],
      [4131, 4114, 4, "Spaceship-5"],
      [8496, 4114, 4, "Spaceship-6"],
      [291, 1, 4, "Stollery-1"],
      [12576, 1, 4, "Stollery-2"],
      [306, 1, 4, "Stollery-3"],
      [8451, 1, 4, "Stollery-4"],
      [12546, 1, 4, "Stollery-5"],
      [4611, 1, 4, "Stollery-6"],
      [291, 4369, 1, "Pinwheel-1"],
      [4146, 4369, 1, "Pinwheel-2"],
      [4896, 4369, 4, "Pinwheel-3"],
      [8241, 8194, 2, "2Face-1"],
      [306, 8194, 4, "2Face-2"],
      [4146, 8194, 2, "2Face-3"],
      [12321, 8194, 4, "2Face-4"],
      [8241, 4354, 4, "Turtle-1"],
      [12576, 4354, 4, "Turtle-2"],
      [4131, 4354, 4, "Turtle-3"],
      [12321, 4354, 4, "Turtle-4"],
      [306, 4354, 4, "Turtle-5"],
      [4611, 4354, 4, "Turtle-6"],
      [4866, 8482, 4, "Pinwheel Poser-1"],
      [531, 8482, 4, "Pinwheel Poser-2"],
      [8211, 8482, 4, "Pinwheel Poser-3"],
      [786, 8482, 4, "Pinwheel Poser-4"],
      [8976, 8482, 4, "Pinwheel Poser-5"],
      [801, 8482, 4, "Pinwheel Poser-6"],
      [291,
        34, 4, "Gun-1"
      ],
      [4146, 34, 4, "Gun-2"],
      [306, 34, 4, "Gun-3"],
      [8976, 34, 4, "Gun-4"],
      [786, 34, 4, "Gun-5"],
      [8496, 34, 4, "Gun-6"]
    ],
    u = [
      [291, 545, 4, "TCLL1-Hammer"],
      [291, 4130, 4, "TCLL1-Spaceship"],
      [8241, 2, 4, "TCLL1-Stollery"],
      [291, 8738, 1, "TCLL1-Pinwheel"],
      [8241, 272, 2, "TCLL1-2Face"],
      [4866, 290, 4, "TCLL1-Turtle"],
      [12816, 4370, 4, "TCLL1-Pinwheel Poser"],
      [8241, 17, 4, "TCLL1-Gun"],
      [4866, 4609, 4, "TCLL2-Hammer"],
      [291, 4114, 4, "TCLL2-Spaceship"],
      [291, 1, 4, "TCLL2-Stollery"],
      [291, 4369, 1, "TCLL2-Pinwheel"],
      [8241, 8194, 2, "TCLL2-2Face"],
      [8241, 4354,
        4, "TCLL2-Turtle"
      ],
      [4866, 8482, 4, "TCLL2-Pinwheel Poser"],
      [291, 34, 4, "TCLL2-Gun"]
    ],
    M = [
      [0, "LS1-PBL"],
      [546, "LS1-Sune"],
      [273, "LS1-aSune"],
      [258, "LS1-Ua"],
      [33, "LS1-Ub"],
      [288, "LS1-La"],
      [528, "LS1-Lb"],
      [513, "LS1-Ta"],
      [18, "LS1-Tb"],
      [66081, "LS2-Hammer"],
      [66066, "LS2-Spaceship"],
      [66048, "LS2-StolleryA"],
      [65538, "LS2-StolleryB"],
      [65568, "LS2-StolleryC"],
      [65808, "LS2-2Face"],
      [65826, "LS2-Turtle"],
      [65553, "LS2-GunA"],
      [65793, "LS2-GunB"],
      [131346, "LS3-Hammer"],
      [131601, "LS3-Spaceship"],
      [131328, "LS3-StolleryA"],
      [131073, "LS3-StolleryB"],
      [131088, "LS3-StolleryC"],
      [131616, "LS3-2Face"],
      [131361, "LS3-Turtle"],
      [131106, "LS3-GunA"],
      [131586, "LS3-GunB"],
      [8226, "LS4-SuneA"],
      [8736, "LS4-SuneB"],
      [8706, "LS4-SuneC"],
      [8721, "LS4-PiA"],
      [8481, "LS4-PiB"],
      [8208, "LS4-U"],
      [8193, "LS4-L"],
      [8448, "LS4-T"],
      [8466, "LS4-H"],
      [73746, "LS5-HammerA"],
      [73986, "LS5-HammerB"],
      [74016, "LS5-SpaceshipA"],
      [74241, "LS5-SpaceshipB"],
      [73728, "LS5-Stollery"],
      [74274, "LS5-Pinwheel"],
      [73761, "LS5-TurtleA"],
      [74256, "LS5-TurtleB"],
      [74001, "LS5-Pinwheel Poser"],
      [139536, "LS6-Hammer"],
      [139521,
        "LS6-Spaceship"
      ],
      [139266, "LS6-2Face"],
      [139281, "LS6-Turtle"],
      [139554, "LS6-Pinwheel PoserA"],
      [139809, "LS6-Pinwheel PoserB"],
      [139794, "LS6-Pinwheel PoserC"],
      [139776, "LS6-GunA"],
      [139296, "LS6-GunB"],
      [4113, "LS7-aSuneA"],
      [4368, "LS7-aSuneB"],
      [4353, "LS7-aSuneC"],
      [4626, "LS7-PiA"],
      [4386, "LS7-PiB"],
      [4608, "LS7-U"],
      [4098, "LS7-L"],
      [4128, "LS7-T"],
      [4641, "LS7-H"],
      [70176, "LS8-Hammer"],
      [69666, "LS8-Spaceship"],
      [69633, "LS8-2Face"],
      [70146, "LS8-Turtle"],
      [69921, "LS8-Pinwheel PoserA"],
      [69906, "LS8-Pinwheel PoserB"],
      [70161, "LS8-Pinwheel PoserC"],
      [69648, "LS8-GunA"],
      [69888, "LS8-GunB"],
      [135681, "LS9-HammerA"],
      [135201, "LS9-HammerB"],
      [135186, "LS9-SpaceshipA"],
      [135456, "LS9-SpaceshipB"],
      [135168, "LS9-Stollery"],
      [135441, "LS9-Pinwheel"],
      [135426, "LS9-TurtleA"],
      [135696, "LS9-TurtleB"],
      [135714, "LS9-Pinwheel Poser"]
    ],
    T = mathlib.idxArray(g, 2),
    L = mathlib.idxArray(g, 3),
    K = mathlib.idxArray(p, 2),
    I = mathlib.idxArray(p, 3),
    w = mathlib.idxArray(x, 2),
    B = mathlib.idxArray(x, 3),
    A = mathlib.idxArray(u, 2),
    N = mathlib.idxArray(u, 3),
    R = mathlib.valuedArray(M.length, 1),
    W = mathlib.idxArray(M,
      1);
  scrMgr.reg(["222o", "222so", "222nb", "222easy"], c)("222eg0", r, [L, T, y.bind(null, "all", g, L)])("222eg1", r, [L, T, y.bind(null, "all", g, L)])("222eg2", r, [L, T, y.bind(null, "all", g, L)])("222tcp", r, [I, K, y.bind(null, "all", p, I)])("222tcn", r, [B, w, y.bind(null, "all", x, B)])("222tc", r, [N, A, y.bind(null, "ori", u, N)])("222lsall", r, [W, R, y.bind(null, "ls", M, W)])("222eg", c, ["EG0-O EG0-H EG0-L EG0-Pi EG0-S EG0-T EG0-U EG0-aS EG1B-O EG1B-H EG1B-L EG1B-Pi EG1B-S EG1B-T EG1B-U EG1B-aS EG1L-O EG1L-H EG1L-L EG1L-Pi EG1L-S EG1L-T EG1L-U EG1L-aS EG1F-O EG1F-H EG1F-L EG1F-Pi EG1F-S EG1F-T EG1F-U EG1F-aS EG1R-O EG1R-H EG1R-L EG1R-Pi EG1R-S EG1R-T EG1R-U EG1R-aS EG2-O EG2-H EG2-L EG2-Pi EG2-S EG2-T EG2-U EG2-aS".split(" "),
    [1, 2, 4, 4, 4, 4, 4, 4, 1, 2, 4, 4, 4, 4, 4, 4, 1, 2, 4, 4, 4, 4, 4, 4, 1, 2, 4, 4, 4, 4, 4, 4, 1, 2, 4, 4, 4, 4, 4, 4, 1, 2, 4, 4, 4, 4, 4, 4]
  ]);
  return {
    getEGLLImage: y.bind(null, !1, g, L)
  }
}(mathlib.rn);
var scramble_444 = function(a, J) {
  function t(v, aa) {
    var ha;
    var va = Array(v);
    if (void 0 != aa)
      for (ha = 0; ha < v; ha++) va[ha] = Array(aa);
    return va
  }

  function G() {
    db = arguments[0].prototype;
    for (var v = 1; v < arguments.length; ++v) arguments[v].prototype = db
  }

  function r() {}

  function y() {
    y = r;
    sb = t(15582, 36);
    Xa = t(15582);
    ab = t(15582);
    ob = t(48, 48);
    pb = t(48, 36);
    Cb = t(48);
    Ab = t(48)
  }

  function c(v, aa) {
    for (var ha = 0; 24 > ha; ++ha)
      if (v.ct[ha] != aa.ct[ha]) return !1;
    return !0
  }

  function n(v) {
    for (var aa = 0, ha = 8, va = 23; 0 <= va; --va) 1 == v.ct[va] && (aa += a[va][ha--]);
    return aa
  }

  function h(v, aa, ha) {
    for (var va = 0, Aa = 8, Ea = 23; 0 <= Ea; --Ea)
      if (1 == v.ct[aa[Ea]] && (va += a[Ea][Aa--]), va >= ha) return -1;
    return va
  }

  function k(v) {
    var aa;
    if (null != ub)
      for (aa = 0; 48 > aa; aa++) {
        var ha = h(v, ib[aa], mathlib.Cnk[21][8]);
        if (-1 != ha) return v = ub[ha], v & -64 | ob[aa][v & 63]
      }
    for (aa = 0; 48 > aa; ++aa) {
      ha = n(v);
      a: {
        var va;
        var Aa = 0;
        for (va = Xa.length - 1; Aa <= va;) {
          var Ea = Aa + (va - Aa >> 1);
          var Ja = Xa[Ea];
          if (Ja < ha) Aa = Ea + 1;
          else if (Ja > ha) va = Ea - 1;
          else {
            ha = Ea;
            break a
          }
        }
        ha = -Aa - 1
      }
      ha = 0 <= ha ? ha : -1;
      if (-1 != ha) return 64 * ha + aa;
      b(v, 0);
      1 == aa % 2 &&
        b(v, 1);
      7 == aa % 8 && b(v, 2);
      15 == aa % 16 && b(v, 3)
    }
  }

  function b(v, aa) {
    switch (aa) {
      case 0:
        R(v, 19);
        R(v, 28);
        break;
      case 1:
        R(v, 21);
        R(v, 32);
        break;
      case 2:
        qa(v.ct, 0, 3, 1, 2, 1);
        qa(v.ct, 8, 11, 9, 10, 1);
        qa(v.ct, 4, 7, 5, 6, 1);
        qa(v.ct, 12, 15, 13, 14, 1);
        qa(v.ct, 16, 19, 21, 22, 1);
        qa(v.ct, 17, 18, 20, 23, 1);
        break;
      case 3:
        R(v, 18), R(v, 29), R(v, 24), R(v, 35)
    }
  }

  function d(v, aa) {
    var ha;
    for (ha = 0; ha < aa; ++ha) b(v, 0), 1 == ha % 2 && b(v, 1), 7 == ha % 8 && b(v, 2), 15 == ha % 16 && b(v, 3)
  }

  function e(v, aa) {
    var ha;
    var va = 8;
    for (ha = 23; 0 <= ha; --ha) v.ct[ha] = 0, aa >= a[ha][va] && (aa -= a[ha][va--],
      v.ct[ha] = 1)
  }

  function l(v, aa) {
    var ha;
    for (ha = 0; 24 > ha; ++ha) v.ct[ha] = aa.ct[ha]
  }

  function q(v) {
    if (v) this.ct = v.ct.slice();
    else
      for (this.ct = [], v = 0; 24 > v; ++v) this.ct[v] = 8 > v ? 1 : 0
  }

  function g() {
    g = r;
    gb = t(70, 28);
    tb = t(6435, 28);
    hb = t(70, 16);
    Sa = t(6435, 16);
    La = t(450450);
    Za = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]
  }

  function p(v) {
    var aa;
    var ha = 0;
    var va = 8;
    for (aa = 14; 0 <= aa; --aa) v.ct[aa] != v.ct[15] && (ha += a[aa][va--]);
    return ha
  }

  function x(v) {
    var aa;
    var ha = 0;
    var va = 4;
    for (aa = 6; 0 <= aa; --aa) v.rl[aa] !=
      v.rl[7] && (ha += a[aa][va--]);
    return 2 * ha + v.parity
  }

  function u(v, aa) {
    v.parity ^= Za[aa];
    var ha = aa % 3;
    switch (~~(aa / 3)) {
      case 0:
        qa(v.ct, 0, 1, 2, 3, ha);
        break;
      case 1:
        qa(v.rl, 0, 1, 2, 3, ha);
        break;
      case 2:
        qa(v.ct, 8, 9, 10, 11, ha);
        break;
      case 3:
        qa(v.ct, 4, 5, 6, 7, ha);
        break;
      case 4:
        qa(v.rl, 4, 5, 6, 7, ha);
        break;
      case 5:
        qa(v.ct, 12, 13, 14, 15, ha);
        break;
      case 6:
        qa(v.ct, 0, 1, 2, 3, ha);
        qa(v.rl, 0, 5, 4, 1, ha);
        qa(v.ct, 8, 9, 12, 13, ha);
        break;
      case 7:
        qa(v.rl, 0, 1, 2, 3, ha);
        qa(v.ct, 1, 15, 5, 9, ha);
        qa(v.ct, 2, 12, 6, 10, ha);
        break;
      case 8:
        qa(v.ct, 8, 9, 10, 11, ha);
        qa(v.rl,
          0, 3, 6, 5, ha);
        qa(v.ct, 3, 2, 5, 4, ha);
        break;
      case 9:
        qa(v.ct, 4, 5, 6, 7, ha);
        qa(v.rl, 3, 2, 7, 6, ha);
        qa(v.ct, 11, 10, 15, 14, ha);
        break;
      case 10:
        qa(v.rl, 4, 5, 6, 7, ha);
        qa(v.ct, 0, 8, 4, 14, ha);
        qa(v.ct, 3, 11, 7, 13, ha);
        break;
      case 11:
        qa(v.ct, 12, 13, 14, 15, ha), qa(v.rl, 1, 4, 7, 2, ha), qa(v.ct, 1, 0, 7, 6, ha)
    }
  }

  function M(v, aa) {
    switch (aa) {
      case 0:
        u(v, 19);
        u(v, 28);
        break;
      case 1:
        u(v, 21);
        u(v, 32);
        break;
      case 2:
        qa(v.ct, 0, 3, 1, 2, 1), qa(v.ct, 8, 11, 9, 10, 1), qa(v.ct, 4, 7, 5, 6, 1), qa(v.ct, 12, 15, 13, 14, 1), qa(v.rl, 0, 3, 5, 6, 1), qa(v.rl, 1, 2, 4, 7, 1)
    }
  }

  function T(v, aa, ha) {
    var va;
    for (va = 0; 16 > va; ++va) v.ct[va] = aa.ct[va] % 3;
    for (va = 0; 8 > va; ++va) v.rl[va] = aa.ct[va + 16];
    v.parity = ha
  }

  function L(v, aa) {
    var ha;
    var va = 8;
    v.ct[15] = 0;
    for (ha = 14; 0 <= ha; --ha) aa >= a[ha][va] ? (aa -= a[ha][va--], v.ct[ha] = 1) : v.ct[ha] = 0
  }

  function K(v, aa) {
    var ha;
    v.parity = aa & 1;
    aa >>>= 1;
    var va = 4;
    v.rl[7] = 0;
    for (ha = 6; 0 <= ha; --ha) aa >= a[ha][va] ? (aa -= a[ha][va--], v.rl[ha] = 1) : v.rl[ha] = 0
  }

  function I() {
    this.rl = t(8);
    this.ct = t(16);
    this.parity = 0
  }

  function w() {
    w = r;
    lb = t(29400, 20);
    Db = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1];
    xb = t(29400);
    Ib = [0,
      9, 14, 23, 27, 28, 41, 42, 46, 55, 60, 69
    ];
    bc = t(70)
  }

  function B(v) {
    var aa;
    var ha = 0;
    var va = 4;
    for (aa = 6; 0 <= aa; --aa) v.ud[aa] != v.ud[7] && (ha += a[aa][va--]);
    ha *= 35;
    va = 4;
    for (aa = 6; 0 <= aa; --aa) v.fb[aa] != v.fb[7] && (ha += a[aa][va--]);
    var Aa = v.fb[7] ^ v.ud[7];
    var Ea = 0;
    va = 4;
    for (aa = 7; 0 <= aa; --aa) v.rl[aa] != Aa && (Ea += a[aa][va--]);
    return v.parity + 2 * (12 * ha + bc[Ea])
  }

  function A(v, aa, ha) {
    var va;
    var Aa = aa.ct[0] % 3 > aa.ct[8] % 3 ^ aa.ct[8] % 3 > aa.ct[16] % 3 ^ aa.ct[0] % 3 > aa.ct[16] % 3 ? 0 : 1;
    for (va = 0; 8 > va; ++va) v.ud[va] = ~~(aa.ct[va] / 3) ^ 1, v.fb[va] = ~~(aa.ct[va +
      8] / 3) ^ 1, v.rl[va] = ~~(aa.ct[va + 16] / 3) ^ 1 ^ Aa;
    v.parity = Aa ^ ha
  }

  function N() {
    this.ud = t(8);
    this.rl = t(8);
    this.fb = t(8);
    this.parity = 0
  }

  function R(v, aa) {
    var ha = aa % 3;
    switch (~~(aa / 3)) {
      case 6:
        qa(v.ct, 8, 20, 12, 16, ha), qa(v.ct, 9, 21, 13, 17, ha);
      case 0:
        qa(v.ct, 0, 1, 2, 3, ha);
        break;
      case 7:
        qa(v.ct, 1, 15, 5, 9, ha), qa(v.ct, 2, 12, 6, 10, ha);
      case 1:
        qa(v.ct, 16, 17, 18, 19, ha);
        break;
      case 8:
        qa(v.ct, 2, 19, 4, 21, ha), qa(v.ct, 3, 16, 5, 22, ha);
      case 2:
        qa(v.ct, 8, 9, 10, 11, ha);
        break;
      case 9:
        qa(v.ct, 10, 18, 14, 22, ha), qa(v.ct, 11, 19, 15, 23, ha);
      case 3:
        qa(v.ct, 4, 5,
          6, 7, ha);
        break;
      case 10:
        qa(v.ct, 0, 8, 4, 14, ha), qa(v.ct, 3, 11, 7, 13, ha);
      case 4:
        qa(v.ct, 20, 21, 22, 23, ha);
        break;
      case 11:
        qa(v.ct, 1, 20, 7, 18, ha), qa(v.ct, 0, 23, 6, 17, ha);
      case 5:
        qa(v.ct, 12, 13, 14, 15, ha)
    }
  }

  function W() {
    this.ct = [];
    for (var v = 0; 24 > v; ++v) this.ct[v] = cc[v] >> 4
  }

  function X() {
    X = r;
    Eb = t(18);
    var v, aa;
    Eb[0] = new z(15120, 0);
    Eb[3] = new z(21021, 1494);
    Eb[6] = new z(8064, 1236);
    Eb[9] = new z(9, 0);
    Eb[12] = new z(1230, 412);
    Eb[15] = new z(224, 137);
    for (v = 0; 18 > v; v += 3)
      for (aa = 0; 2 > aa; ++aa) Eb[v + aa + 1] = new D, m(Eb[v + aa], Eb[v], Eb[v + aa + 1])
  }

  function S(v) {
    v.cp = [0, 1, 2, 3, 4, 5, 6, 7];
    v.co = [0, 0, 0, 0, 0, 0, 0, 0]
  }

  function f(v, aa) {
    var ha;
    for (ha = 0; 8 > ha; ++ha) v.cp[ha] = aa.cp[ha], v.co[ha] = aa.co[ha]
  }

  function m(v, aa, ha) {
    var va;
    for (va = 0; 8 > va; ++va) {
      ha.cp[va] = v.cp[aa.cp[va]];
      var Aa = v.co[aa.cp[va]];
      var Ea = aa.co[va];
      var Ja = Aa;
      Ja += 3 > Aa ? Ea : 6 - Ea;
      Ja %= 3;
      3 <= Aa ^ 3 <= Ea && (Ja += 3);
      ha.co[va] = Ja
    }
  }

  function D() {
    S(this)
  }

  function z(v, aa) {
    S(this);
    mathlib.setNPerm(this.cp, v, 8);
    v = aa;
    var ha = 0;
    for (aa = 6; 0 <= aa; --aa) ha += this.co[aa] = v % 3, v = ~~(v / 3);
    this.co[7] = (15 - ha) % 3
  }

  function H() {
    H = r;
    Gb = new Int32Array(1937880);
    mc = t(1538);
    Ic = t(1538);
    vc = t(1538);
    Jc = t(11880);
    id = [0, 1, 6, 3, 4, 5, 2, 7];
    nc = t(168, 12);
    oc = t(168, 12);
    wc = [1, 1, 1, 3, 12, 60, 360, 2520, 20160, 181440, 1814400, 19958400, 239500800];
    Kc = [0, 2, 4, 6, 1, 3, 7, 5, 8, 9, 10, 11]
  }

  function F(v, aa, ha, va, Aa) {
    var Ea = v.edgeo[Aa];
    v.edgeo[Aa] = v.edge[va];
    v.edge[va] = v.edgeo[ha];
    v.edgeo[ha] = v.edge[aa];
    v.edge[aa] = Ea
  }

  function P(v, aa, ha) {
    v.isStd || Ca(v);
    v = v.edge;
    for (var va = 0, Aa = 0, Ea = 0; Ea < aa; Ea++) {
      var Ja = v[Ea];
      va = va * (12 - Ea) + Ja - mathlib.bitCount(Aa & (1 << Ja) - 1);
      Aa |= 1 << Ja
    }
    return ha ? Aa : va
  }

  function C(v) {
    v.isStd ||
      Ca(v);
    return ya(v.edge, 20) >> 3
  }

  function E(v, aa) {
    v.isStd = !1;
    switch (aa) {
      case 0:
        J(v.edge, 0, 4, 1, 5);
        J(v.edgeo, 0, 4, 1, 5);
        break;
      case 1:
        sa(v.edge, 0, 4, 1, 5);
        sa(v.edgeo, 0, 4, 1, 5);
        break;
      case 2:
        J(v.edge, 0, 5, 1, 4);
        J(v.edgeo, 0, 5, 1, 4);
        break;
      case 3:
        sa(v.edge, 5, 10, 6, 11);
        sa(v.edgeo, 5, 10, 6, 11);
        break;
      case 4:
        J(v.edge, 0, 11, 3, 8);
        J(v.edgeo, 0, 11, 3, 8);
        break;
      case 5:
        sa(v.edge, 0, 11, 3, 8);
        sa(v.edgeo, 0, 11, 3, 8);
        break;
      case 6:
        J(v.edge, 0, 8, 3, 11);
        J(v.edgeo, 0, 8, 3, 11);
        break;
      case 7:
        J(v.edge, 2, 7, 3, 6);
        J(v.edgeo, 2, 7, 3, 6);
        break;
      case 8:
        sa(v.edge,
          2, 7, 3, 6);
        sa(v.edgeo, 2, 7, 3, 6);
        break;
      case 9:
        J(v.edge, 2, 6, 3, 7);
        J(v.edgeo, 2, 6, 3, 7);
        break;
      case 10:
        sa(v.edge, 4, 8, 7, 9);
        sa(v.edgeo, 4, 8, 7, 9);
        break;
      case 11:
        J(v.edge, 1, 9, 2, 10);
        J(v.edgeo, 1, 9, 2, 10);
        break;
      case 12:
        sa(v.edge, 1, 9, 2, 10);
        sa(v.edgeo, 1, 9, 2, 10);
        break;
      case 13:
        J(v.edge, 1, 10, 2, 9);
        J(v.edgeo, 1, 10, 2, 9);
        break;
      case 14:
        sa(v.edge, 0, 4, 1, 5);
        sa(v.edgeo, 0, 4, 1, 5);
        J(v.edge, 9, 11);
        J(v.edgeo, 8, 10);
        break;
      case 15:
        sa(v.edge, 5, 10, 6, 11);
        sa(v.edgeo, 5, 10, 6, 11);
        J(v.edge, 1, 3);
        J(v.edgeo, 0, 2);
        break;
      case 16:
        sa(v.edge, 0, 11, 3, 8);
        sa(v.edgeo,
          0, 11, 3, 8);
        J(v.edge, 5, 7);
        J(v.edgeo, 4, 6);
        break;
      case 17:
        sa(v.edge, 2, 7, 3, 6);
        sa(v.edgeo, 2, 7, 3, 6);
        J(v.edge, 8, 10);
        J(v.edgeo, 9, 11);
        break;
      case 18:
        sa(v.edge, 4, 8, 7, 9);
        sa(v.edgeo, 4, 8, 7, 9);
        J(v.edge, 0, 2);
        J(v.edgeo, 1, 3);
        break;
      case 19:
        sa(v.edge, 1, 9, 2, 10), sa(v.edgeo, 1, 9, 2, 10), J(v.edge, 4, 6), J(v.edgeo, 5, 7)
    }
  }

  function O(v, aa) {
    v.isStd = !1;
    switch (aa) {
      case 0:
        E(v, 14);
        E(v, 17);
        break;
      case 1:
        F(v, 11, 5, 10, 6);
        F(v, 5, 10, 6, 11);
        F(v, 1, 2, 3, 0);
        F(v, 4, 9, 7, 8);
        F(v, 8, 4, 9, 7);
        F(v, 0, 1, 2, 3);
        break;
      case 2:
        ua(v, 4, 5), ua(v, 5, 4), ua(v, 11, 8), ua(v, 8, 11),
          ua(v, 7, 6), ua(v, 6, 7), ua(v, 9, 10), ua(v, 10, 9), ua(v, 1, 1), ua(v, 0, 0), ua(v, 3, 3), ua(v, 2, 2)
    }
  }

  function Q(v, aa) {
    for (; 2 <= aa;) aa -= 2, O(v, 1), O(v, 2);
    0 != aa && O(v, 0)
  }

  function ba(v, aa) {
    var ha, va;
    var Aa = 1985229328;
    var Ea = 47768;
    for (ha = va = 0; 11 > ha; ++ha) {
      var Ja = wc[11 - ha];
      var Qa = ~~(aa / Ja);
      aa %= Ja;
      va ^= Qa;
      Qa <<= 2;
      32 <= Qa ? (Qa -= 32, v.edge[ha] = Ea >> Qa & 15, Ja = (1 << Qa) - 1, Ea = (Ea & Ja) + (Ea >> 4 & ~Ja)) : (v.edge[ha] = Aa >> Qa & 15, Ja = (1 << Qa) - 1, Aa = (Aa & Ja) + (Aa >>> 4 & ~Ja) + (Ea << 28), Ea >>= 4)
    }
    0 == (va & 1) ? v.edge[11] = Aa : (v.edge[11] = v.edge[10], v.edge[10] = Aa);
    for (ha =
      0; 12 > ha; ++ha) v.edgeo[ha] = ha;
    v.isStd = !0
  }

  function ja(v, aa) {
    var ha;
    for (ha = 0; 12 > ha; ++ha) v.edge[ha] = aa.edge[ha], v.edgeo[ha] = aa.edgeo[ha];
    v.isStd = aa.isStd
  }

  function wa(v, aa) {
    var ha;
    null == v.temp && (v.temp = t(12));
    for (ha = 0; 12 > ha; ++ha) v.temp[ha] = ha, v.edge[ha] = aa.ep[Kc[ha] + 12] % 12;
    var va = 1;
    for (ha = 0; 12 > ha; ++ha)
      for (; v.edge[ha] != ha;) {
        var Aa = v.edge[ha];
        v.edge[ha] = v.edge[Aa];
        v.edge[Aa] = Aa;
        var Ea = v.temp[ha];
        v.temp[ha] = v.temp[Aa];
        v.temp[Aa] = Ea;
        va ^= 1
      }
    for (ha = 0; 12 > ha; ++ha) v.edge[ha] = v.temp[aa.ep[Kc[ha]] % 12];
    return va
  }

  function Ca(v) {
    var aa;
    null == v.temp && (v.temp = t(12));
    for (aa = 0; 12 > aa; ++aa) v.temp[v.edgeo[aa]] = aa;
    for (aa = 0; 12 > aa; ++aa) v.edge[aa] = v.temp[v.edge[aa]], v.edgeo[aa] = aa;
    v.isStd = !0
  }

  function sa(v, aa, ha, va, Aa) {
    var Ea = v[aa];
    v[aa] = v[va];
    v[va] = Ea;
    Ea = v[ha];
    v[ha] = v[Aa];
    v[Aa] = Ea
  }

  function ua(v, aa, ha) {
    var va = v.edge[aa];
    v.edge[aa] = v.edgeo[ha];
    v.edgeo[ha] = va
  }

  function Ga() {
    this.edge = t(12);
    this.edgeo = t(12);
    this.isStd = !0;
    this.temp = null
  }

  function Ha(v, aa) {
    return v[aa >> 4] >> ((aa & 15) << 1) & 3
  }

  function ya(v, aa, ha) {
    var va = aa << 3,
      Aa = 0,
      Ea = 0;
    if (void 0 !== ha &&
      1 == Xb[aa] % 3) va |= ha & 7, Aa = ha >> 3;
    else {
      aa = oc[va];
      ha = nc[va];
      for (var Ja = 0; 4 > Ja; Ja++) {
        var Qa = aa[v[ha[Ja]]];
        Aa = Aa * (12 - Ja) + Qa - mathlib.bitCount(Ea & (1 << Qa) - 1);
        Ea |= 1 << Qa
      }
      Aa = Jc[Aa];
      va |= Aa & 7;
      Aa >>= 3
    }
    aa = oc[va];
    ha = nc[va];
    Ea = Ic[Aa];
    for (Ja = 4; 10 > Ja; Ja++) Qa = aa[v[ha[Ja]]], Aa = Aa * (12 - Ja) + Qa - mathlib.bitCount(Ea & (1 << Qa) - 1), Ea |= 1 << Qa;
    return Aa << 3 | va & 7
  }

  function ka(v) {
    var aa = new Ga;
    var ha = 0;
    var va = Ha(Gb, v);
    if (3 == va) return Lc;
    for (; 0 != v;) {
      va = (va + 2) % 3;
      var Aa = ~~(v / 20160);
      Aa = mc[Aa];
      var Ea = v % 20160;
      ba(aa, 20160 * Aa + Ea);
      for (Ea = 0; 17 > Ea; ++Ea)
        if (Aa =
          ya(aa.edge, Ea) >> 3, Ha(Gb, Aa) == va) {
          ++ha;
          v = Aa;
          break
        }
    }
    return ha
  }

  function Y(v, aa, ha) {
    v[aa >> 4] ^= (3 ^ ha) << ((aa & 15) << 1)
  }

  function Z(v, aa) {
    var ha = aa % 3;
    switch (~~(aa / 3)) {
      case 6:
        qa(v.ep, 9, 22, 11, 20, ha);
      case 0:
        qa(v.ep, 0, 1, 2, 3, ha);
        qa(v.ep, 12, 13, 14, 15, ha);
        break;
      case 7:
        qa(v.ep, 2, 16, 6, 12, ha);
      case 1:
        qa(v.ep, 11, 15, 10, 19, ha);
        qa(v.ep, 23, 3, 22, 7, ha);
        break;
      case 8:
        qa(v.ep, 3, 19, 5, 13, ha);
      case 2:
        qa(v.ep, 0, 11, 6, 8, ha);
        qa(v.ep, 12, 23, 18, 20, ha);
        break;
      case 9:
        qa(v.ep, 8, 23, 10, 21, ha);
      case 3:
        qa(v.ep, 4, 5, 6, 7, ha);
        qa(v.ep, 16, 17, 18, 19, ha);
        break;
      case 10:
        qa(v.ep, 14, 0, 18, 4, ha);
      case 4:
        qa(v.ep, 1, 20, 5, 21, ha);
        qa(v.ep, 13, 8, 17, 9, ha);
        break;
      case 11:
        qa(v.ep, 7, 15, 1, 17, ha);
      case 5:
        qa(v.ep, 2, 9, 4, 10, ha), qa(v.ep, 14, 21, 16, 22, ha)
    }
  }

  function oa() {
    this.ep = [];
    for (var v = 0; 24 > v; ++v) this.ep[v] = v
  }

  function V() {
    V = r;
    Mc = [35, 1, 34, 2, 4, 6, 22, 5, 19]
  }

  function ca(v, aa) {
    var ha = v.edge;
    var va = aa.edge,
      Aa;
    for (Aa = 0; 24 > Aa; ++Aa) ha.ep[Aa] = va.ep[Aa];
    ha = v.center;
    va = aa.center;
    for (Aa = 0; 24 > Aa; ++Aa) ha.ct[Aa] = va.ct[Aa];
    f(v.corner, aa.corner);
    v.value = aa.value;
    v.add1 = aa.add1;
    v.length1 = aa.length1;
    v.length2 = aa.length2;
    v.length3 = aa.length3;
    v.sym = aa.sym;
    for (ha = 0; 60 > ha; ++ha) v.moveBuffer[ha] = aa.moveBuffer[ha];
    v.moveLength = aa.moveLength;
    v.edgeAvail = aa.edgeAvail;
    v.centerAvail = aa.centerAvail;
    v.cornerAvail = aa.cornerAvail
  }

  function ia(v, aa) {
    for (var ha = 0, va = 0, Aa = 0, Ea = 0, Ja = 0; 24 > Ja; Ja++) v.center.ct[Ja] = aa[cc[Ja]], ha += 1 << 4 * aa[cc[Ja]];
    for (Ja = 0; 24 > Ja; Ja++)
      for (var Qa = 0; 24 > Qa; Qa++) aa[Rb[Ja][0]] == Rb[Qa][0] >> 4 && aa[Rb[Ja][1]] == Rb[Qa][1] >> 4 && (v.edge.ep[Ja] = Qa, va |= 1 << Qa);
    var Pa;
    for (Ja = 0; 8 > Ja; Ja++) {
      for (Pa = 0; 3 > Pa &&
        0 != aa[Sb[Ja][Pa]] && 3 != aa[Sb[Ja][Pa]]; Pa++);
      var Wa = aa[Sb[Ja][(Pa + 1) % 3]];
      var Va = aa[Sb[Ja][(Pa + 2) % 3]];
      for (Qa = 0; 8 > Qa; Qa++)
        if (Wa == Sb[Qa][1] >> 4 && Va == Sb[Qa][2] >> 4) {
          v.corner.cp[Ja] = Qa;
          v.corner.co[Ja] = Pa % 3;
          Aa |= 1 << Qa;
          Ea += Pa % 3;
          break
        }
    }
    return 1 * (255 != Aa) + 2 * (0 != Ea % 3) + 4 * (4473924 != ha) + 8 * (16777215 != va)
  }

  function ma(v) {
    Ba(v);
    da(v);
    ta(v);
    for (var aa = [], ha = 0; 24 > ha; ha++) aa[cc[ha]] = v.center.ct[ha];
    for (ha = 0; 24 > ha; ha++) aa[Rb[ha][0]] = Rb[v.edge.ep[ha]][0] >> 4, aa[Rb[ha][1]] = Rb[v.edge.ep[ha]][1] >> 4;
    for (ha = 0; 8 > ha; ha++)
      for (var va =
          v.corner.cp[ha], Aa = v.corner.co[ha], Ea = 0; 3 > Ea; Ea++) aa[Sb[ha][(Ea + Aa) % 3]] = Sb[va][Ea] >> 4;
    return aa
  }

  function xa(v) {
    v = ma(v);
    for (var aa = [
        [1, 2],
        [4, 8],
        [7, 11],
        [13, 14],
        [5, 6, 9, 10]
      ], ha = [0, 1, 3, 4, 5, 7, 12, 13, 15], va = [], Aa = 0; 6 > Aa; Aa++) {
      for (var Ea = 0; Ea < aa.length; Ea++)
        for (var Ja = v[Aa << 4 | aa[Ea][0]], Qa = 1; Qa < aa[Ea].length; Qa++)
          if (Ja != v[Aa << 4 | aa[Ea][Qa]]) return console.log("reduction error", aa[Ea][Qa], aa[Ea][0]), null;
      for (Ea = 0; Ea < ha.length; Ea++) va[9 * Aa + Ea] = v[Aa << 4 | ha[Ea]]
    }
    return va
  }

  function Ba(v) {
    for (; v.centerAvail < v.moveLength;) R(v.center,
      v.moveBuffer[v.centerAvail++]);
    return v.center
  }

  function da(v) {
    for (; v.cornerAvail < v.moveLength;) {
      var aa = v.corner,
        ha = v.moveBuffer[v.cornerAvail++] % 18;
      !aa.temps && (aa.temps = new D);
      m(aa, Eb[ha], aa.temps);
      f(aa, aa.temps)
    }
    return v.corner
  }

  function ta(v) {
    for (; v.edgeAvail < v.moveLength;) Z(v.edge, v.moveBuffer[v.edgeAvail++]);
    return v.edge
  }

  function na(v) {
    var aa, ha, va;
    var Aa = Array(v.moveLength - (v.add1 ? 2 : 0));
    for (aa = ha = 0; aa < v.length1; ++aa) Aa[ha++] = v.moveBuffer[aa];
    var Ea = v.sym;
    for (aa = v.length1 + (v.add1 ? 2 : 0); aa < v.moveLength; ++aa)
      if (27 <=
        pb[Ea][v.moveBuffer[aa]]) {
        Aa[ha++] = pb[Ea][v.moveBuffer[aa]] - 9;
        var Ja = Mc[pb[Ea][v.moveBuffer[aa]] - 27];
        Ea = ob[Ea][Ja]
      } else Aa[ha++] = pb[Ea][v.moveBuffer[aa]];
    aa = ob[Cb[Ea]];
    a: {
      v = Ba(v);v = new q(v);
      for (va = 0; 48 > va; ++va) {
        Ja = !0;
        for (Ea = 0; 24 > Ea; ++Ea)
          if (v.ct[Ea] != cc[Ea] >> 4) {
            Ja = !1;
            break
          } if (Ja) {
          v = va;
          break a
        }
        b(v, 0);
        1 == va % 2 && b(v, 1);
        7 == va % 8 && b(v, 2);
        15 == va % 16 && b(v, 3)
      }
      v = -1
    }
    aa = aa[v];
    v = [];
    Ea = aa;
    for (aa = ha - 1; 0 <= aa; --aa) Ja = Aa[aa], Ja = 3 * ~~(Ja / 3) + (2 - Ja % 3), 27 <= pb[Ea][Ja] ? (v.push(pb[Ea][Ja] - 9), Ja = Mc[pb[Ea][Ja] - 27], Ea = ob[Ea][Ja]) :
      v.push(pb[Ea][Ja]);
    Ea = -1;
    ha = 0;
    va = [0, 0, 0];
    for (aa = 0; aa < v.length; ++aa) {
      Ja = v[aa];
      if (Ea != ~~(Ja / 3) % 3) {
        for (Aa = 0; 3 > Aa; Aa++) va[Aa] % 4 && (v[ha++] = xc[9 * Aa + 3 * Ea + va[Aa] - 1] + " ", va[Aa] = 0);
        Ea = ~~(Ja / 3) % 3
      }
      va[~~(Ja / 9)] += Ja % 3 + 1
    }
    for (Aa = 0; 3 > Aa; Aa++) va[Aa] % 4 && (v[ha++] = xc[9 * Aa + 3 * Ea + va[Aa] - 1] + " ", va[Aa] = 0);
    return v = v.slice(0, ha).join("")
  }

  function Ia(v, aa) {
    v.moveBuffer[v.moveLength++] = aa
  }

  function Ka() {
    this.moveBuffer = t(60);
    this.edge = new oa;
    this.center = new W;
    this.corner = new D
  }

  function Ma(v) {
    Ka.call(this);
    ca(this, v)
  }

  function Ua() {
    Ua =
      r;
    var v, aa;
    xc = "U  ;U2 ;U' ;R  ;R2 ;R' ;F  ;F2 ;F' ;D  ;D2 ;D' ;L  ;L2 ;L' ;B  ;B2 ;B' ;Uw ;Uw2;Uw';Rw ;Rw2;Rw';Fw ;Fw2;Fw';Dw ;Dw2;Dw';Lw ;Lw2;Lw';Bw ;Bw2;Bw'".split(";");
    Yb = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 22, 23, 25, 28, 30, 31, 32, 34, 36];
    Xb = [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 13, 15, 16, 17, 19, 22, 25, 28, 31, 34, 36];
    jd = t(37);
    kd = t(37);
    dc = t(37, 36);
    yc = t(29, 28);
    zc = t(21, 20);
    Nc = t(36);
    pc = t(28);
    Zb = t(20);
    Oc = t(36, 24);
    for (v = 0; 29 > v; ++v) jd[Yb[v]] = v;
    for (v = 0; 21 > v; ++v) kd[Xb[v]] = v;
    for (v = 0; 36 > v; ++v) {
      for (aa = 0; 36 > aa; ++aa) dc[v][aa] =
        ~~(v / 3) == ~~(aa / 3) || ~~(v / 3) % 3 == ~~(aa / 3) % 3 && v > aa;
      dc[36][v] = !1
    }
    for (v = 0; 29 > v; ++v)
      for (aa = 0; 28 > aa; ++aa) yc[v][aa] = dc[Yb[v]][Yb[aa]];
    for (v = 0; 21 > v; ++v)
      for (aa = 0; 20 > aa; ++aa) zc[v][aa] = dc[Xb[v]][Xb[aa]];
    for (v = 0; 36 > v; ++v)
      for (Nc[v] = 36, aa = v; 36 > aa; ++aa)
        if (!dc[v][aa]) {
          Nc[v] = aa - 1;
          break
        } for (v = 0; 28 > v; ++v)
      for (pc[v] = 28, aa = v; 28 > aa; ++aa)
        if (!yc[v][aa]) {
          pc[v] = aa - 1;
          break
        } for (v = 0; 20 > v; ++v)
      for (Zb[v] = 20, aa = v; 20 > aa; ++aa)
        if (!zc[v][aa]) {
          Zb[v] = aa - 1;
          break
        } for (v = 0; 36 > v; ++v) {
      var ha = new oa;
      Z(ha, v);
      for (aa = 0; 24 > aa; aa++) Oc[v][ha.ep[aa]] =
        aa
    }
  }

  function ra(v) {
    v.solution = "";
    var aa = $.now();
    var ha = k((new q).fromCube(Ba(v.c), 0));
    var va = k((new q).fromCube(Ba(v.c), 1));
    var Aa = k((new q).fromCube(Ba(v.c), 2));
    var Ea = ab[ha >> 6];
    var Ja = ab[va >> 6];
    var Qa = ab[Aa >> 6];
    v.p1SolsCnt = 0;
    v.arr2idx = 0;
    Fa(v.p1sols);
    for (v.length1 = Math.min(Ea, Ja, Qa); 60 > v.length1 && !(Qa <= v.length1 && U(v, Aa >>> 6, Aa & 63, v.length1, -1, 0) || Ea <= v.length1 && U(v, ha >>> 6, ha & 63, v.length1, -1, 0) || Ja <= v.length1 && U(v, va >>> 6, va & 63, v.length1, -1, 0)); ++v.length1);
    ha = v.p1sols.array.slice();
    va = $.now() - aa;
    DEBUG && console.log("[scramble 444] Phase 1 Done in", $.now() - aa);
    ha.sort(function(jb, Tb) {
      return jb.value - Tb.value
    });
    Aa = 9;
    do {
      Qa = ha[0].value;
      a: for (; 60 > Qa; ++Qa)
        for (Ja = 0; Ja < ha.length; ++Ja) {
          var Pa = ha[Ja];
          if (Pa.value > Qa) break;
          if (!(Qa - Pa.length1 > Aa)) {
            ca(v.c1, Pa);
            var Wa = ta(v.c1).ep;
            T(v.ct2, Ba(v.c1), pa(Wa));
            Ea = p(v.ct2);
            var Va = x(v.ct2);
            v.length1 = Pa.length1;
            v.length2 = Qa - Pa.length1;
            v.epInv = [];
            for (Pa = 0; 24 > Pa; Pa++) v.epInv[Wa[Pa]] = Pa;
            if (fa(v, Ea, Va, v.length2, 28, 0)) break a
          }
        }++Aa
    } while (60 == Qa);
    v.arr2.sort(function(jb,
      Tb) {
      return jb.value - Tb.value
    });
    DEBUG && console.log("[scramble 444] Phase 2 Done in", $.now() - aa);
    Aa = $.now() - aa - va;
    Qa = 0;
    ha = 13;
    do {
      Ea = v.arr2[0].value;
      a: for (; 60 > Ea; ++Ea)
        for (Ja = 0; Ja < Math.min(v.arr2idx, 100) && !(v.arr2[Ja].value > Ea); ++Ja)
          if (v.arr2[Ja].length3 = Ea - v.arr2[Ja].length1 - v.arr2[Ja].length2, !(v.arr2[Ja].length3 > ha)) {
            Va = wa(v.e12, ta(v.arr2[Ja]));
            A(v.ct3, Ba(v.arr2[Ja]), Va ^ pa(da(v.arr2[Ja]).cp));
            Va = B(v.ct3);
            P(v.e12, 10);
            for (Wa = 0; 12 > Wa; Wa++) v.tempep[0][Wa] = v.e12.edge[Wa];
            Wa = ka(C(v.e12));
            if (Wa <= v.arr2[Ja].length3 &&
              ea(v, v.tempep[0], Va, Wa, v.arr2[Ja].length3, 20, 0)) {
              Qa = Ja;
              break a
            }
          }++ ha
    } while (60 == Ea);
    DEBUG && console.log("[scramble 444] Phase 3 Done in", $.now() - aa);
    ha = $.now() - aa - va - Aa;
    Qa = new Ma(v.arr2[Qa]);
    v.length1 = Qa.length1;
    v.length2 = Qa.length2;
    v.length3 = Qa.length3;
    for (Ja = 0; Ja < v.length3; ++Ja) Ia(Qa, Xb[v.move3[Ja]]);
    (Ea = xa(Qa)) || console.log("[scramble 444] Reduction Error!", ma(Qa));
    for (Ja = 0; 54 > Ja; Ja++) Ea[Ja] = "URFDLB" [Ea[Ja]];
    Ea = Ea.join("");
    Ja = scramble_333.solvFacelet(Ea).split(" ");
    for (Va = Ea = 0; Va < Ja.length; Va++) /^[URFDLB][2']?$/.exec(Ja[Va]) &&
      (Ea++, Ia(Qa, 3 * "URFDLB".indexOf(Ja[Va][0]) + "2'".indexOf(Ja[Va][1]) + 1));
    v.solution = na(Qa);
    DEBUG && console.log("[scramble 444] 3x3x3 Done in", $.now() - aa);
    DEBUG && console.log("[scramble 444] Phase depths: ", [v.length1, v.length2, v.length3, Ea, va, Aa, ha]);
    return [v.length1, v.length2, v.length3, Ea, va, Aa, ha]
  }

  function za(v) {
    "          U0U1U2U3\n          U4U5U6U7\n          U8U9UaUb\n          UcUdUeUf\nL0L1L2L3  F0F1F2F3  R0R1R2R3  B0B1B2B3\nL4L5L6L7  F4F5F6F7  R4R5R6R7  B4B5B6B7\nL8L9LaLb  F8F9FaFb  R8R9RaRb  B8B9BaBb\nLcLdLeLf  FcFdFeFf  RcRdReRf  BcBdBeBf\n          D0D1D2D3\n          D4D5D6D7\n          D8D9DaDb\n          DcDdDeDf\n".replace(/[URFDLB][0-9a-f]/g,
      function(aa) {
        var ha = "URFDLB".indexOf(aa[0]);
        aa = "0123456789abcdef".indexOf(aa[1]);
        return "URFDLB" [v[16 * ha + aa]] + " "
      })
  }

  function U(v, aa, ha, va, Aa, Ea) {
    var Ja, Qa, Pa;
    if (0 == aa) {
      if (aa = 0 == va) {
        ca(v.c1, v.c);
        for (aa = 0; aa < v.length1; ++aa) Ia(v.c1, v.move1[aa]);
        switch (Ab[ha]) {
          case 0:
            Ia(v.c1, 24);
            Ia(v.c1, 35);
            v.move1[v.length1] = 24;
            v.move1[v.length1 + 1] = 35;
            v.add1 = !0;
            ha = 19;
            break;
          case 12869:
            Ia(v.c1, 18);
            Ia(v.c1, 29);
            v.move1[v.length1] = 18;
            v.move1[v.length1 + 1] = 29;
            v.add1 = !0;
            ha = 34;
            break;
          case 735470:
            v.add1 = !1, ha = 0
        }
        T(v.ct2, Ba(v.c1),
          pa(ta(v.c1).ep));
        aa = p(v.ct2);
        va = x(v.ct2);
        v.c1.value = La[70 * aa + va] + v.length1;
        v.c1.length1 = v.length1;
        v.c1.add1 = v.add1;
        v.c1.sym = ha;
        ++v.p1SolsCnt;
        if (500 > v.p1sols.size) var Wa = new Ma(v.c1);
        else {
          ha = v.p1sols;
          if (0 == ha.size) Wa = null;
          else {
            aa = ha.array[0];
            va = ha.size - 1;
            Aa = ha.array[va];
            ha.array.splice(va, 1);
            --ha.size;
            if (0 < ha.size) {
              Da(ha, 0, Aa);
              va = 0;
              Aa = ha.size;
              for (Pa = ha.array[va]; 2 * va + 1 < Aa;) {
                Ea = (Ja = 2 * va + 1, Wa = Ja + 1, Qa = Ja, Wa < Aa && 0 > ha.array[Ja].value - ha.array[Wa].value && (Qa = Wa), Qa);
                if (0 > ha.array[Ea].value - Pa.value) break;
                Da(ha, va, ha.array[Ea]);
                va = Ea
              }
              Da(ha, va, Pa)
            }
            Wa = aa
          }
          Wa.value > v.c1.value && ca(Wa, v.c1)
        }
        Ja = v.p1sols;
        b: {
          ha = Ja.size;
          for (Ja.array[Ja.size++] = Wa; 0 < ha;) {
            Qa = ha;
            ha = ha - 1 >> 1;
            if (0 >= Wa.value - Ja.array[ha].value) {
              Da(Ja, Qa, Wa);
              break b
            }
            Da(Ja, Qa, Ja.array[ha])
          }
          Da(Ja, ha, Wa)
        }
        aa = 1E4 == v.p1SolsCnt
      }
      return aa
    }
    for (Ja = 0; 27 > Ja; Ja += 3)
      if (Ja != Aa && Ja != Aa - 9 && Ja != Aa - 18)
        for (Pa = 0; 3 > Pa; ++Pa) {
          Qa = Ja + Pa;
          Wa = sb[aa][pb[ha][Qa]];
          var Va = ab[Wa >>> 6];
          if (Va >= va) {
            if (Va > va) break
          } else if (Va = ob[ha][Wa & 63], Wa >>>= 6, v.move1[Ea] = Qa, U(v, Wa, Va, va - 1, Ja, Ea + 1)) return !0
        }
    return !1
  }

  function fa(v, aa, ha, va, Aa, Ea) {
    var Ja;
    if (0 == aa && 0 == La[ha] && 5 > va) {
      if (aa = 0 == va) {
        b: {
          aa = v.epInv;
          for (va = ha = 0; 12 > va; va++) {
            Aa = aa[va];
            Ea = aa[va + 12];
            for (Ja = 0; Ja < v.length2; Ja++) {
              var Qa = Oc[v.move2[Ja]];
              Aa = Qa[Aa];
              Ea = Qa[Ea]
            }
            if (12 > Aa != 12 <= Ea) {
              aa = !1;
              break b
            }
            ha ^= 12 <= Aa ? 1 : 0
          }
          aa = 0 == ha
        }
        if (aa) {
          ca(v.c2, v.c1);
          for (aa = 0; aa < v.length2; ++aa) Ia(v.c2, v.move2[aa]);
          aa = wa(v.e12, ta(v.c2));
          A(v.ct3, Ba(v.c2), aa ^ pa(da(v.c2).cp));
          aa = B(v.ct3);
          P(v.e12, 10);
          ha = ka(C(v.e12));
          v.arr2[v.arr2idx] ? ca(v.arr2[v.arr2idx], v.c2) : v.arr2[v.arr2idx] = new Ma(v.c2);
          v.arr2[v.arr2idx].value = v.length1 + v.length2 + Math.max(ha, xb[aa]);
          v.arr2[v.arr2idx].length2 = v.length2;
          ++v.arr2idx;
          aa = v.arr2idx == v.arr2.length
        } else aa = !1
      }
      return aa
    }
    for (Qa = 0; 23 > Qa; ++Qa)
      if (yc[Aa][Qa]) Qa = pc[Qa];
      else {
        Ja = tb[aa][Qa];
        var Pa = gb[ha][Qa];
        var Wa = La[70 * Ja + Pa];
        if (Wa >= va) Wa > va && (Qa = pc[Qa]);
        else if (v.move2[Ea] = Yb[Qa], fa(v, Ja, Pa, va - 1, Qa, Ea + 1)) return !0
      } return !1
  }

  function ea(v, aa, ha, va, Aa, Ea, Ja) {
    if (0 == Aa) return !0;
    var Qa = v.tempep[Ja];
    if (20 != Ea)
      for (var Pa = oc[Ea << 3], Wa = nc[Ea << 3], Va = 0; 12 > Va; Va++) Qa[Va] = Pa[aa[Wa[Va]]];
    for (aa = 0; 17 > aa; aa++)
      if (zc[Ea][aa]) aa = Zb[aa];
      else if (Pa = lb[ha][aa], Wa = xb[Pa], Wa >= Aa) Wa > Aa && 14 > aa && (aa = Zb[aa]);
    else if (Va = ya(Qa, aa) >> 3, Wa = va, Va = Ha(Gb, Va), Wa = 3 == Va ? Lc : (1227133513 << Va >> Wa & 3) + Wa - 1, Wa >= Aa) Wa > Aa && 14 > aa && (aa = Zb[aa]);
    else if (ea(v, Qa, Pa, Wa, Aa - 1, aa, Ja + 1)) return v.move3[Ja] = aa, !0;
    return !1
  }

  function la() {
    var v;
    this.p1sols = new Oa;
    this.move1 = t(15);
    this.move2 = t(20);
    this.move3 = t(20);
    this.c1 = new Ka;
    this.c2 = new Ka;
    this.ct2 = new I;
    this.ct3 = new N;
    this.e12 = new Ga;
    this.tempep = t(20);
    this.arr2 = t(100);
    for (v =
      0; 20 > v; ++v) this.tempep[v] = [];
    this.add1 = !1;
    this.arr2idx = 0;
    this.c = null;
    this.p1SolsCnt = this.length2 = this.length1 = 0;
    this.solution = ""
  }

  function pa(v) {
    for (var aa = 0, ha = 0, va = 0; va < v.length; va++) {
      var Aa = v[va];
      aa ^= Aa - mathlib.bitCount(ha & (1 << Aa) - 1);
      ha |= 1 << Aa
    }
    return aa & 1
  }

  function qa(v, aa, ha, va, Aa, Ea) {
    switch (Ea) {
      case 0:
        Ea = v[Aa];
        v[Aa] = v[va];
        v[va] = v[ha];
        v[ha] = v[aa];
        v[aa] = Ea;
        break;
      case 1:
        Ea = v[aa];
        v[aa] = v[va];
        v[va] = Ea;
        Ea = v[ha];
        v[ha] = v[Aa];
        v[Aa] = Ea;
        break;
      case 2:
        Ea = v[aa], v[aa] = v[ha], v[ha] = v[va], v[va] = v[Aa], v[Aa] = Ea
    }
  }

  function Fa(v) {
    v.array = [];
    v.size = 0
  }

  function Da(v, aa, ha) {
    var va = v.array[aa];
    v.array[aa] = ha;
    return va
  }

  function Oa() {
    this.array = [];
    this.array.length = 500;
    this.size = 0
  }

  function bb(v) {
    for (var aa = 0; aa < v.length; aa++) v[aa] = -1
  }

  function fb() {
    fb = r;
    var v = $.now();
    DEBUG && console.log("[scramble 444] start initialization");
    Ua();
    y();
    g();
    w();
    H();
    X();
    V();
    DEBUG && console.log("[scramble 444] alloc tables", $.now() - v);
    var aa, ha, va;
    var Aa = new q;
    for (aa = 0; 24 > aa; ++aa) Aa.ct[aa] = aa;
    var Ea = new q(Aa);
    var Ja = new q(Aa);
    var Qa = new q(Aa);
    for (aa = 0; 48 > aa; ++aa) {
      for (ha = 0; 48 > ha; ++ha) {
        for (va = 0; 48 > va; ++va) c(Aa, Ea) && (ob[aa][ha] = va, 0 == va && (Cb[aa] = ha)), b(Ea, 0), 1 == va % 2 && b(Ea, 1), 7 == va % 8 && b(Ea, 2), 15 == va % 16 && b(Ea, 3);
        b(Aa, 0);
        1 == ha % 2 && b(Aa, 1);
        7 == ha % 8 && b(Aa, 2);
        15 == ha % 16 && b(Aa, 3)
      }
      b(Aa, 0);
      1 == aa % 2 && b(Aa, 1);
      7 == aa % 8 && b(Aa, 2);
      15 == aa % 16 && b(Aa, 3)
    }
    for (aa = 0; 48 > aa; ++aa)
      for (l(Aa, Ja), d(Aa, Cb[aa]), ha = 0; 36 > ha; ++ha)
        for (l(Ea, Aa), R(Ea, ha), d(Ea, aa), va = 0; 36 > va; ++va)
          if (l(Qa, Ja), R(Qa, va), c(Qa, Ea)) {
            pb[aa][ha] = va;
            break
          } e(Aa, 0);
    for (aa = 0; 48 > aa; ++aa) Ab[Cb[aa]] = n(Aa), b(Aa, 0),
      1 == aa % 2 && b(Aa, 1), 7 == aa % 8 && b(Aa, 2), 15 == aa % 16 && b(Aa, 3);
    DEBUG && console.log("[scramble 444] initSymMeta", $.now() - v);
    ub = t(735471);
    var Pa, Wa = new q;
    new q;
    ib = [];
    for (var Va = 0; 24 > Va; Va++) Wa.ct[Va] = Va;
    for (var jb = 0; 48 > jb; jb++) ib[jb] = Wa.ct.slice(), b(Wa, 0), 1 == jb % 2 && b(Wa, 1), 7 == jb % 8 && b(Wa, 2), 15 == jb % 16 && b(Wa, 3);
    var Tb = t(22984);
    for (Va = 0; 22984 > Va; Va++) Tb[Va] = 0;
    var ld = 0;
    for (Va = 0; Va < mathlib.Cnk[21][8]; ++Va)
      if (0 == (Tb[Va >>> 5] & 1 << (Va & 31))) {
        e(Wa, Va);
        for (Pa = 0; 48 > Pa; ++Pa) {
          var qc = h(Wa, ib[Pa], mathlib.Cnk[21][8]); - 1 != qc && (Tb[qc >>>
            5] |= 1 << (qc & 31), null != ub && (ub[qc] = ld << 6 | Cb[Pa]))
        }
        Xa[ld++] = Va
      } DEBUG && console.log("[scramble 444] initCenter1Sym2Raw", $.now() - v);
    for (var Pc = new q, md = new q, Hb = 0; 15582 > Hb; ++Hb) {
      e(md, Xa[Hb]);
      for (var Bb = 0; 36 > Bb; ++Bb)
        if (1 != Bb % 3 && void 0 === sb[Hb][Bb]) {
          l(Pc, md);
          R(Pc, Bb);
          var Mb = k(Pc);
          sb[Hb][Bb] = Mb;
          var nd = pb[Mb & 63][3 * ~~(Bb / 3) + 2 - Bb % 3];
          void 0 === sb[Mb >> 6][nd] && (sb[Mb >> 6][nd] = Hb << 6 | Cb[Mb & 63])
        }
    }
    for (Hb = 0; 15582 > Hb; Hb++)
      for (Bb = 0; 36 > Bb; Bb += 3) {
        Mb = sb[Hb][Bb];
        var od = sb[Mb >>> 6][pb[Mb & 63][Bb]];
        sb[Hb][Bb + 1] = od & -64 | ob[Mb & 63][od &
          63
        ]
      }
    DEBUG && console.log("[scramble 444] initCenter1MoveTable", $.now() - v);
    ub = null;
    var Qc, ec, Rc, Ac;
    bb(ab);
    var fc = ab[0] = 0;
    for (Qc = 1; 15582 != Qc;) {
      var Ed = (Rc = 4 < fc) ? -1 : fc;
      var Fd = Rc ? fc : -1;
      ++fc;
      for (ec = 0; 15582 > ec; ++ec)
        if (ab[ec] == Ed)
          for (Ac = 0; 27 > Ac; ++Ac) {
            var pd = sb[ec][Ac] >>> 6;
            if (ab[pd] == Fd)
              if (++Qc, Rc) {
                ab[ec] = fc;
                break
              } else ab[pd] = fc
          }
    }
    DEBUG && console.log("[scramble 444] initCenter1Prun", $.now() - v);
    var Sc, kb, Fb, yb, zb = new I,
      Tc = new I;
    for (kb = 0; 70 > kb; ++kb)
      for (yb = 0; 28 > yb; ++yb) K(zb, kb), u(zb, Yb[yb]), gb[kb][yb] = x(zb);
    for (kb =
      0; 70 > kb; ++kb)
      for (K(zb, kb), Fb = 0; 16 > Fb; ++Fb) hb[kb][Fb] = x(zb), M(zb, 0), 1 == Fb % 2 && M(zb, 1), 7 == Fb % 8 && M(zb, 2);
    for (kb = 0; 6435 > kb; ++kb)
      for (L(zb, kb), Fb = 0; 16 > Fb; ++Fb) Sa[kb][Fb] = p(zb), M(zb, 0), 1 == Fb % 2 && M(zb, 1), 7 == Fb % 8 && M(zb, 2);
    for (kb = 0; 6435 > kb; ++kb)
      for (L(zb, kb), yb = 0; 28 > yb; ++yb) Tc.copy(zb), u(Tc, Yb[yb]), tb[kb][yb] = p(Tc);
    bb(La);
    var gc = La[0] = La[18] = La[28] = La[46] = La[54] = La[56] = 0;
    for (Sc = 6; 450450 != Sc;) {
      var Uc = 6 < gc,
        Gd = Uc ? -1 : gc,
        Hd = Uc ? gc : -1;
      ++gc;
      for (kb = 0; 450450 > kb; ++kb)
        if (La[kb] == Gd) {
          var Id = ~~(kb / 70);
          var Jd = kb % 70;
          for (yb = 0; 23 >
            yb; ++yb) {
            var Kd = tb[Id][yb];
            var Ld = gb[Jd][yb];
            var qd = 70 * Kd + Ld;
            if (La[qd] == Hd)
              if (++Sc, Uc) {
                La[kb] = gc;
                break
              } else La[qd] = gc
          }
        }
    }
    DEBUG && console.log("[scramble 444] initCenter2", $.now() - v);
    var Vc, vb, Jb;
    for (vb = 0; 12 > vb; ++vb) bc[Ib[vb]] = vb;
    var rd = new N,
      Wc = new N;
    for (vb = 0; 29400 > vb; ++vb) {
      var Nb = void 0,
        Xc = void 0,
        Yc = void 0,
        rb = void 0,
        Ob = rd,
        Kb = vb;
      Ob.parity = Kb & 1;
      Kb >>>= 1;
      Xc = Ib[Kb % 12];
      Kb = ~~(Kb / 12);
      Nb = 4;
      for (rb = 7; 0 <= rb; --rb) Ob.rl[rb] = 0, Xc >= a[rb][Nb] && (Xc -= a[rb][Nb--], Ob.rl[rb] = 1);
      Yc = Kb % 35;
      Kb = ~~(Kb / 35);
      Nb = 4;
      Ob.fb[7] = 0;
      for (rb =
        6; 0 <= rb; --rb) Yc >= a[rb][Nb] ? (Yc -= a[rb][Nb--], Ob.fb[rb] = 1) : Ob.fb[rb] = 0;
      Nb = 4;
      Ob.ud[7] = 0;
      for (rb = 6; 0 <= rb; --rb) Kb >= a[rb][Nb] ? (Kb -= a[rb][Nb--], Ob.ud[rb] = 1) : Ob.ud[rb] = 0;
      for (Jb = 0; 20 > Jb; ++Jb) {
        Wc.copy(rd);
        var mb = Wc,
          hc = Jb;
        mb.parity ^= Db[hc];
        switch (hc) {
          case 0:
          case 1:
          case 2:
            qa(mb.ud, 0, 1, 2, 3, hc % 3);
            break;
          case 3:
            qa(mb.rl, 0, 1, 2, 3, 1);
            break;
          case 4:
          case 5:
          case 6:
            qa(mb.fb, 0, 1, 2, 3, (hc - 1) % 3);
            break;
          case 7:
          case 8:
          case 9:
            qa(mb.ud, 4, 5, 6, 7, (hc - 1) % 3);
            break;
          case 10:
            qa(mb.rl, 4, 5, 6, 7, 1);
            break;
          case 11:
          case 12:
          case 13:
            qa(mb.fb, 4, 5,
              6, 7, (hc + 1) % 3);
            break;
          case 14:
            qa(mb.ud, 0, 1, 2, 3, 1);
            qa(mb.rl, 0, 5, 4, 1, 1);
            qa(mb.fb, 0, 5, 4, 1, 1);
            break;
          case 15:
            qa(mb.rl, 0, 1, 2, 3, 1);
            qa(mb.fb, 1, 4, 7, 2, 1);
            qa(mb.ud, 1, 6, 5, 2, 1);
            break;
          case 16:
            qa(mb.fb, 0, 1, 2, 3, 1);
            qa(mb.ud, 3, 2, 5, 4, 1);
            qa(mb.rl, 0, 3, 6, 5, 1);
            break;
          case 17:
            qa(mb.ud, 4, 5, 6, 7, 1);
            qa(mb.rl, 3, 2, 7, 6, 1);
            qa(mb.fb, 3, 2, 7, 6, 1);
            break;
          case 18:
            qa(mb.rl, 4, 5, 6, 7, 1);
            qa(mb.fb, 0, 3, 6, 5, 1);
            qa(mb.ud, 0, 3, 4, 7, 1);
            break;
          case 19:
            qa(mb.fb, 4, 5, 6, 7, 1), qa(mb.ud, 0, 7, 6, 1, 1), qa(mb.rl, 1, 4, 7, 2, 1)
        }
        lb[vb][Jb] = B(Wc)
      }
    }
    bb(xb);
    var Zc = xb[0] = 0;
    for (Vc =
      1; 29400 != Vc;) {
      for (vb = 0; 29400 > vb; ++vb)
        if (xb[vb] == Zc)
          for (Jb = 0; 17 > Jb; ++Jb) - 1 == xb[lb[vb][Jb]] && (xb[lb[vb][Jb]] = Zc + 1, ++Vc);
      ++Zc
    }
    DEBUG && console.log("[scramble 444] initCenter3", $.now() - v);
    for (var ic = new Ga, rc = 0; 21 > rc; ++rc)
      for (var sc = 0; 8 > sc; ++sc) {
        ba(ic, 0);
        E(ic, rc);
        Q(ic, sc);
        for (var Pb = 0; 12 > Pb; ++Pb) nc[rc << 3 | sc][Pb] = ic.edge[Pb];
        Ca(ic);
        for (Pb = 0; 12 > Pb; ++Pb) oc[rc << 3 | sc][Pb] = ic.temp[Pb]
      }
    DEBUG && console.log("[scramble 444] initEdge3MvRot", $.now() - v);
    var $b, jc;
    var Ub = new Ga;
    var Bc = t(1485);
    for (var wb = 0; 1485 > wb; wb++) Bc[wb] =
      0;
    for (wb = $b = 0; 11880 > wb; ++wb)
      if (0 == (Bc[wb >>> 3] & 1 << (wb & 7))) {
        ba(Ub, wb * wc[8]);
        mc[$b] = wb;
        Ic[$b] = P(Ub, 4, !0);
        for (jc = 0; 8 > jc; ++jc) {
          var Vb = P(Ub, 4);
          Vb == wb && (vc[$b] |= 1 << jc);
          Bc[Vb >> 3] |= 1 << (Vb & 7);
          Jc[Vb] = $b << 3 | id[jc];
          O(Ub, 0);
          1 == jc % 2 && (O(Ub, 1), O(Ub, 2))
        }
        $b++
      } for (var Qb = 0; 20 > Qb; Qb++) $c[Qb] = [];
    for (wb = 0; 1538 > wb; wb++)
      for (ba(Ub, mc[wb] * wc[8]), Qb = 0; 20 > Qb; ++Qb) 1 == Xb[Qb] % 3 && (Vb = ya(Ub.edge, Qb), $c[Qb][wb] = ~~((Vb >> 3) / 20160) << 3 | Vb & 7);
    DEBUG && console.log("[scramble 444] initEdge3Sym2Raw", $.now() - v);
    var ad;
    var bd = new Ga;
    var Cc = new Ga;
    var cd = new Ga;
    bb(Gb);
    var ac = 0,
      Dc = 1;
    Y(Gb, 0, 0);
    for (var Md = [1, 0, 2, 3, 5, 4, 6, 8, 7, 9, 10, 12, 11, 13, 14, 15, 16], Nd = $.now(); 31006080 != Dc;) {
      var tc = 9 < ac,
        dd = ac % 3,
        sd = (ac + 1) % 3,
        Od = (ac + 2) % 3;
      var td = tc ? 3 : dd;
      var ud = tc ? dd : 3;
      var Pd = 1431655765 * td;
      if (ac >= Lc - 1) break;
      for (var uc = 0; 31006080 > uc; uc += 16) {
        var Ec = Gb[uc >> 4];
        var vd = Ec ^ Pd;
        if ((tc || -1 != Ec) && 0 != (vd - 1431655765 & ~vd & 2863311530))
          for (var kc = uc, Qd = uc + 16; kc < Qd; ++kc, Ec >>= 2)
            if ((Ec & 3) == td) {
              var wd = ~~(kc / 20160);
              var Rd = mc[wd];
              var Sd = kc % 20160;
              ba(bd, 20160 * Rd + Sd);
              for (var Fc = 0; 17 > Fc; ++Fc) {
                var Gc =
                  Md[Fc],
                  lc = ya(bd.edge, Gc, $c[Gc][wd]),
                  Td = lc & 7;
                lc >>= 3;
                var ed = Ha(Gb, lc);
                if (ed != ud) {
                  if (ed == Od || ed == dd && lc < kc) Fc = Zb[Gc]
                } else {
                  Y(Gb, tc ? kc : lc, sd);
                  ++Dc;
                  if (tc) break;
                  var xd = ~~(lc / 20160);
                  var fd = vc[xd];
                  if (1 != fd)
                    for (ja(Cc, bd), E(Cc, Gc), Q(Cc, Td), ad = 1; 0 != (fd >>= 1); ++ad)
                      if (1 == (fd & 1)) {
                        ja(cd, Cc);
                        Q(cd, ad);
                        var yd = 20160 * xd + P(cd, 10) % 20160;
                        Ha(Gb, yd) == ud && (Y(Gb, yd, sd), ++Dc)
                      }
                }
              }
            }
      }++ac;
      DEBUG && console.log("[scramble 444] edge3 pruning ", ac, Dc, $.now() - Nd)
    }
    DEBUG && console.log("[scramble 444] initEdge3Prun", $.now() - v);
    Wb = new la
  }

  function Ta(v,
    aa, ha, va) {
    var Aa = [0, 1, 2, 3, 4, 5];
    va && (va = mathlib.rn([1, 4, 8, 1, 1, 1, 24][va]), 8 <= va && (mathlib.acycle(Aa, [0, 1, 2], va >> 3), mathlib.acycle(Aa, [3, 4, 5], va >> 3), va &= 7), 4 <= va && (mathlib.acycle(Aa, [0, 1, 3, 4], 2), va &= 3), 1 <= va && mathlib.acycle(Aa, [1, 2, 4, 5], va));
    va = !0;
    for (var Ea = 0; va && 100 > Ea; Ea++) {
      var Ja = new Ka;
      for (var Qa = [], Pa = [], Wa = [], Va = 0; 24 > Va; Va++) v >> Va & 1 && Qa.push(Va), aa >> Va & 1 && Pa.push(Va), ha >> Va & 1 && Wa.push(Va);
      var jb = mathlib.rndPerm(Qa.length);
      for (Va = 0; Va < Qa.length; Va++) Ja.center.ct[Qa[Va]] = cc[Qa[jb[Va]]] >> 4;
      Qa = mathlib.rndPerm(Pa.length);
      for (Va = 0; Va < Pa.length; Va++) Ja.edge.ep[Pa[Va]] = Pa[Qa[Va]];
      Pa = mathlib.rndPerm(Wa.length);
      Qa = 24;
      for (Va = 0; Va < Wa.length; Va++) jb = mathlib.rn(3), Ja.corner.co[Wa[Va]] = jb, Ja.corner.cp[Wa[Va]] = Wa[Pa[Va]], Qa -= jb;
      0 != Qa % 3 && (Ja.corner.co[Wa[0]] = (Ja.corner.co[Wa[0]] + Qa) % 3);
      Ja = ma(Ja);
      for (Va = 0; 96 > Va; Va++) Ja[Va] = "URFDLB".charAt(Aa[Ja[Va]]), Ja[Va] != Ja[Va >> 4 << 4] && (va = !1)
    }
    return Ja.join("")
  }

  function eb(v) {
    fb();
    v = v.split("");
    for (var aa = 0; 96 > aa; aa++) v[aa] = "URFDLB".indexOf(v[aa]);
    DEBUG && console.log("[scramble 444] Scramble to state:");
    DEBUG && za(v);
    Wb.c = new Ka;
    aa = ia(Wb.c, v);
    0 != aa && console.log("[scramble 444] State Check Error!", aa, v);
    ra(Wb);
    return Wb.solution.replace(/\s+/g, " ")
  }

  function Na(v, aa, ha, va) {
    return eb(Ta(v, aa, ha, va))
  }

  function Ra() {
    return eb(Ta(16777215, 16777215, 255))
  }

  function cb(v, aa) {
    for (var ha = new Ka, va = v.trim().split(/\s+/), Aa = 0; Aa < va.length; Aa++) {
      for (var Ea = va[Aa]; 3 > Ea.length;) Ea += " ";
      Ea = xc.indexOf(Ea);
      0 <= Ea && Ia(ha, Ea)
    }
    ha = ma(ha);
    va = [5, 21, 37, 53, 69, 85];
    Aa = -1;
    for (Ea = 0; 6 > Ea; Ea++)
      if (0 == ha[va[Ea]]) {
        Aa = Ea;
        break
      }(aa = [" z x' z2 z' x".split(" "),
        "z'  y z z2 y'".split(" "), "x y'  x' y x2".split(" "), "z2 z' x  z x'".split(" "), "z z2 y' z'  y".split(" "), "x' y x2 x y' ".split(" ")
      ][Aa][aa || 0]) && (v = v + " " + aa);
    return v.replace(/\s+/g, " ").trim()
  }

  function $a(v, aa) {
    if (0 == aa) return v.slice();
    var ha = Lb[aa],
      va = Lb[(4 - aa) % 4];
    return v.map(function(Aa, Ea) {
      return ha[v[va[Ea]]]
    })
  }

  function Ya(v, aa) {
    if (0 == aa) return v.slice();
    aa = Lb[aa];
    for (var ha = [], va = 0; 4 > va; va++) ha[aa[va]] = v[va];
    return ha
  }

  function nb(v, aa) {
    for (var ha = [], va = {}, Aa = 0; Aa < aa; Aa++) - 1 != v[Aa] && (va[v[Aa]] = !0);
    for (Aa = 0; Aa < aa; Aa++) va[Aa] || ha.push(Aa);
    for (Aa = ha.length - 1; 0 < Aa; Aa--) {
      va = mathlib.rn(Aa + 1);
      var Ea = ha[Aa];
      ha[Aa] = ha[va];
      ha[va] = Ea
    }
    for (va = Aa = 0; Aa < aa; Aa++) - 1 == v[Aa] && (v[Aa] = ha[va++])
  }

  function qb(v, aa, ha, va, Aa, Ea, Ja, Qa) {
    v = v.slice();
    aa = aa.slice();
    ha = ha.slice();
    va = va.slice();
    nb(v, 4);
    nb(ha, 4);
    for (var Pa = 0; 4 > Pa; Pa++) - 1 == aa[Pa] && (aa[Pa] = mathlib.rn(2));
    Pa = va;
    for (var Wa = 0, Va = -1, jb = 0; 4 > jb; jb++) - 1 == Pa[jb] ? Va = jb : Wa += Pa[jb];
    for (jb = 0; 4 > jb; jb++) - 1 == Pa[jb] && jb != Va && (Pa[jb] = mathlib.rn(3), Wa += Pa[jb]); - 1 != Va && (Pa[Va] =
      (3 - Wa % 3) % 3);
    Ea && 0 < Ea.length && (Pa = Ea[mathlib.rn(Ea.length)], 0 < Pa && (v = $a(v, Pa), ha = $a(ha, Pa), aa = Ya(aa, Pa), va = Ya(va, Pa)));
    if (Ja && 0 < Ja.length && (Pa = Ja[mathlib.rn(Ja.length)], 0 < Pa)) {
      Ja = Lb[Pa];
      Ea = [];
      Wa = [];
      Va = [];
      jb = [];
      for (Pa = 0; 4 > Pa; Pa++) Ea[Ja[Pa]] = v[Pa], Wa[Ja[Pa]] = aa[Pa], Va[Ja[Pa]] = ha[Pa], jb[Ja[Pa]] = va[Pa];
      v = Ea;
      aa = Wa;
      ha = Va;
      va = jb
    }
    Ja = new Ka;
    for (Pa = 0; 4 > Pa; Pa++) Ja.corner.cp[Pa] = ha[Pa], Ja.corner.co[Pa] = va[Pa];
    for (Pa = 0; 4 > Pa; Pa++) ha = v[Pa], aa[Pa] ? (Ja.edge.ep[Pa] = ha + 12, Ja.edge.ep[Pa + 12] = ha) : (Ja.edge.ep[Pa] = ha, Ja.edge.ep[Pa +
      12] = ha + 12);
    v = [0, 1, 2, 3, 4, 5];
    Aa && (Aa = mathlib.rn([1, 4, 8, 1, 1, 1, 24][Aa]), 8 <= Aa && (mathlib.acycle(v, [0, 1, 2], Aa >> 3), mathlib.acycle(v, [3, 4, 5], Aa >> 3), Aa &= 7), 4 <= Aa && (mathlib.acycle(v, [0, 1, 3, 4], 2), Aa &= 3), 1 <= Aa && mathlib.acycle(v, [1, 2, 4, 5], Aa));
    Aa = ma(Ja);
    for (Pa = 0; 96 > Pa; Pa++) Aa[Pa] = "URFDLB".charAt(v[Aa[Pa]]);
    Aa = eb(Aa.join("")).replace(/^\s+/, "");
    void 0 !== Qa && !1 !== Qa && (Aa = cb(Aa, Qa));
    return Aa
  }
  var db;
  q.prototype.fromCube = function(v, aa) {
    for (var ha = 0; 24 > ha; ++ha) this.ct[ha] = v.ct[ha] % 3 == aa ? 1 : 0;
    return this
  };
  var ab, sb,
    Ab, ub = null,
    Xa, ib, Cb, pb, ob;
  I.prototype.copy = function(v) {
    for (var aa = 0; 8 > aa; aa++) this.rl[aa] = v.rl[aa];
    for (aa = 0; 16 > aa; aa++) this.ct[aa] = v.ct[aa];
    this.parity = v.parity
  };
  var tb, La, Sa, Za, gb, hb;
  N.prototype.copy = function(v) {
    for (var aa = 0; 8 > aa; aa++) this.ud[aa] = v.ud[aa], this.rl[aa] = v.rl[aa], this.fb[aa] = v.fb[aa];
    this.parity = v.parity
  };
  var lb, Db, xb, Ib, bc;
  G(D, z);
  db.temps = null;
  var Eb, Kc, Gb, wc, nc, oc, Jc, mc, Ic, id, vc, Lc = 10,
    $c = [],
    cc = [5, 6, 10, 9, 53, 54, 58, 57, 37, 38, 42, 41, 85, 86, 90, 89, 21, 22, 26, 25, 69, 70, 74, 73],
    Sb = [
      [15, 16, 35],
      [12,
        32, 67
      ],
      [0, 64, 83],
      [3, 80, 19],
      [51, 47, 28],
      [48, 79, 44],
      [60, 95, 76],
      [63, 31, 92]
    ],
    Rb = [
      [13, 33],
      [4, 65],
      [2, 81],
      [11, 17],
      [61, 94],
      [52, 78],
      [50, 46],
      [59, 30],
      [75, 40],
      [68, 87],
      [27, 88],
      [20, 39],
      [34, 14],
      [66, 8],
      [82, 1],
      [18, 7],
      [93, 62],
      [77, 56],
      [45, 49],
      [29, 55],
      [36, 71],
      [91, 72],
      [84, 23],
      [43, 24]
    ];
  G(Ka, Ma);
  db.add1 = !1;
  db.center = null;
  db.centerAvail = 0;
  db.corner = null;
  db.cornerAvail = 0;
  db.edge = null;
  db.edgeAvail = 0;
  db.length1 = 0;
  db.length2 = 0;
  db.length3 = 0;
  db.moveLength = 0;
  db.sym = 0;
  db.value = 0;
  var Mc, dc, yc, zc, Yb, xc, Xb, Nc, pc, Zb, jd, kd, Oc, Wb, gd = [3,
      0, 1, 2
    ],
    Lb = [
      [0, 1, 2, 3], gd
    ];
  Lb[2] = Lb[1].map(function(v, aa) {
    return gd[Lb[1][aa]]
  });
  Lb[3] = Lb[2].map(function(v, aa) {
    return gd[Lb[2][aa]]
  });
  var hd = [
      [
        [2, 1, 0, 3],
        [0, 1, 2, 3], 2, "EPLL-Opp"
      ],
      [
        [0, 1, 3, 2],
        [0, 1, 2, 3], 4, "EPLL-Adj"
      ],
      [
        [3, 0, 1, 2],
        [0, 1, 2, 3], 1, "EPLL-O-"
      ],
      [
        [1, 2, 3, 0],
        [0, 1, 2, 3], 1, "EPLL-O+"
      ],
      [
        [2, 3, 1, 0],
        [0, 1, 2, 3], 4, "EPLL-W"
      ],
      [
        [0, 1, 2, 3],
        [2, 1, 0, 3], 2, "CPLL-pN"
      ],
      [
        [0, 1, 2, 3],
        [3, 1, 2, 0], 4, "CPLL-pJ"
      ],
      [
        [2, 3, 0, 1],
        [3, 1, 2, 0], 4, "CPLL-M"
      ],
      [
        [1, 2, 0, 3],
        [2, 1, 0, 3], 4, "Diag-Sa"
      ],
      [
        [3, 1, 0, 2],
        [0, 3, 2, 1], 4, "Diag-Sb"
      ],
      [
        [0, 3, 2, 1],
        [3, 2, 1, 0],
        1, "Diag-Q"
      ],
      [
        [2, 1, 0, 3],
        [3, 2, 1, 0], 1, "Diag-X"
      ],
      [
        [1, 0, 3, 2],
        [0, 2, 1, 3], 4, "Adj-Ka"
      ],
      [
        [3, 2, 1, 0],
        [0, 2, 1, 3], 4, "Adj-Kb"
      ],
      [
        [3, 1, 0, 2],
        [3, 1, 2, 0], 4, "Adj-Pa"
      ],
      [
        [2, 1, 3, 0],
        [3, 1, 2, 0], 4, "Adj-Pb"
      ],
      [
        [0, 1, 3, 2],
        [0, 2, 3, 1], 4, "Adj-Ba"
      ],
      [
        [0, 2, 1, 3],
        [3, 1, 0, 2], 4, "Adj-Bb"
      ],
      [
        [0, 3, 1, 2],
        [1, 0, 2, 3], 4, "Adj-Ca"
      ],
      [
        [0, 2, 3, 1],
        [1, 0, 2, 3], 4, "Adj-Cb"
      ],
      [
        [2, 0, 1, 3],
        [0, 1, 3, 2], 4, "Adj-Da"
      ],
      [
        [2, 1, 3, 0],
        [0, 1, 3, 2], 4, "Adj-Db"
      ],
      [
        [2, 3, 0, 1],
        [0, 1, 2, 3], 1, "PLL-H"
      ],
      [
        [3, 0, 2, 1],
        [0, 1, 2, 3], 4, "PLL-Ua"
      ],
      [
        [1, 3, 2, 0],
        [0, 1, 2, 3], 4, "PLL-Ub"
      ],
      [
        [3, 2, 1, 0],
        [0, 1, 2, 3], 2, "PLL-Z"
      ],
      [
        [0, 1, 2, 3],
        [1, 2, 0, 3], 4, "PLL-Aa"
      ],
      [
        [0, 1, 2, 3],
        [2, 0, 1, 3], 4, "PLL-Ab"
      ],
      [
        [0, 1, 2, 3],
        [1, 0, 3, 2], 2, "PLL-E"
      ],
      [
        [0, 3, 2, 1],
        [1, 0, 2, 3], 4, "PLL-F"
      ],
      [
        [2, 0, 1, 3],
        [1, 2, 0, 3], 4, "PLL-Ga"
      ],
      [
        [1, 2, 0, 3],
        [2, 0, 1, 3], 4, "PLL-Gb"
      ],
      [
        [1, 3, 2, 0],
        [2, 0, 1, 3], 4, "PLL-Gc"
      ],
      [
        [3, 0, 2, 1],
        [1, 2, 0, 3], 4, "PLL-Gd"
      ],
      [
        [3, 1, 2, 0],
        [1, 0, 2, 3], 4, "PLL-Ja"
      ],
      [
        [1, 0, 2, 3],
        [1, 0, 2, 3], 4, "PLL-Jb"
      ],
      [
        [2, 1, 0, 3],
        [2, 1, 0, 3], 1, "PLL-Na"
      ],
      [
        [0, 3, 2, 1],
        [2, 1, 0, 3], 1, "PLL-Nb"
      ],
      [
        [0, 1, 3, 2],
        [1, 0, 2, 3], 4, "PLL-Ra"
      ],
      [
        [0, 2, 1, 3],
        [1, 0, 2, 3], 4, "PLL-Rb"
      ],
      [
        [2, 1, 0, 3],
        [1, 0, 2, 3], 4, "PLL-T"
      ],
      [
        [1, 0, 2, 3],
        [2, 1, 0, 3], 4, "PLL-V"
      ],
      [
        [3, 1, 2, 0],
        [2, 1, 0, 3], 4, "PLL-Y"
      ]
    ],
    zd = mathlib.idxArray(hd, 2),
    Ad = mathlib.idxArray(hd, 3),
    Bd = [
      ["BFBRRRFBFLLL", [7, 1],
        [1, 7]
      ],
      ["LBLBLBRRRFFF", [7, 5],
        [5, 7]
      ],
      ["BRBRFRFLFLBL", [1, 3],
        [3, 7],
        [7, 5],
        [5, 1]
      ],
      ["BLBRBRFRFLFL", [1, 5],
        [5, 7],
        [7, 3],
        [3, 1]
      ],
      ["BRBRLRFBFLFL"],
      ["LLRFBBRRLBFF", [0, 8],
        [8, 0]
      ],
      ["RRFLFRFLLBBB", [2, 8],
        [8, 2]
      ],
      ["RLFLBRFRLBFB"],
      ["LRRFLBRBLBFF"],
      ["FFBRBLBRFLLR"],
      ["RFLBRFLBRFLB"],
      ["RBLBLFLFRFRB"],
      ["RRLBBRFLFLFB"],
      ["RLLBFRFRFLBB"],
      ["BRRFFBRBFLLL"],
      ["FBLBFFLLBRRR"],
      ["BRRFLBRFFLBL"],
      ["RRFLBRFFLBLB"],
      ["BLFLRBRFRFBL"],
      ["FRBRBFLFLBLR"],
      ["BFBRRFLLRFBL"],
      ["LRLBLRFBBRFF"],
      ["BFBRLRFBFLRL", [1, 7],
        [3, 5]
      ],
      ["BRBRLRFFFLBL", [3, 7],
        [7, 5],
        [5, 3]
      ],
      ["BLBRBRFFFLRL", [3, 5],
        [5, 7],
        [7, 3]
      ],
      ["LFLBRBRBRFLF", [1, 5],
        [3, 7]
      ],
      ["LBBRRLBFRFLF", [0, 2],
        [2, 6],
        [6, 0]
      ],
      ["RBFLRRFFLBLB", [0, 6],
        [6, 8],
        [8, 0]
      ],
      ["LBRFRBRFLBLF", [0, 6],
        [2, 8]
      ],
      ["BFRFRBRBFLLL", [1, 7],
        [2, 8]
      ],
      ["BRRFLBRBFLFL"],
      ["BFRFBBRLFLRL"],
      ["BFRFLBRRFLBL"],
      ["BLRFFBRBFLRL"],
      ["BBRFFBRRFLLL", [1, 5],
        [2, 8]
      ],
      ["LBBRLLBRRFFF", [2, 8],
        [5, 7]
      ],
      ["FBBRLLBFFLRR", [2, 6],
        [3, 5]
      ],
      ["BBFLLRFFBRRL", [0, 8],
        [3, 5]
      ],
      ["LLBRBLBFRFRF", [1, 3],
        [2, 8]
      ],
      ["RBFLFRFLLBRB", [2, 8],
        [3, 7]
      ],
      ["BBRFLBRFFLRL", [2, 8],
        [3, 5]
      ],
      ["BBFLFRFRBRLL", [0, 8],
        [1, 5]
      ],
      ["BBFLRRFLBRFL", [0, 8],
        [1, 3]
      ]
    ],
    Hc = [
      [
        [2, 0, 2, 2], 0, 3, 4, "3E-S-F"
      ],
      [
        [2, 0, 2, 2], 3, 3, 4, "3E-S-R"
      ],
      [
        [2, 0, 2, 2], 2, 3, 4, "3E-S-B"
      ],
      [
        [2, 0, 2, 2], 1, 3, 4, "3E-S-L"
      ],
      [
        [0, 1, 1, 1], 0, 3, 4, "3E-A-F"
      ],
      [
        [0, 1, 1, 1], 3, 3, 4, "3E-A-R"
      ],
      [
        [0, 1, 1, 1], 2, 3, 4, "3E-A-B"
      ],
      [
        [0, 1, 1, 1], 1, 3, 4, "3E-A-L"
      ],
      [
        [0, 0, 1, 2], 0, 3, 4, "3E-T-F"
      ],
      [
        [0, 0, 1, 2], 3, 3, 4, "3E-T-R"
      ],
      [
        [0, 0, 1, 2], 2, 3, 4, "3E-T-B"
      ],
      [
        [0, 0, 1, 2], 1, 3, 4, "3E-T-L"
      ],
      [
        [0, 1, 0, 2], 0, 3, 4, "3E-L-F"
      ],
      [
        [0, 1, 0, 2], 3, 3, 4, "3E-L-R"
      ],
      [
        [0, 1, 0, 2], 2, 3, 4, "3E-L-B"
      ],
      [
        [0, 1, 0, 2], 1, 3, 4, "3E-L-L"
      ],
      [
        [0, 0, 2, 1], 0, 3, 4, "3E-U-F"
      ],
      [
        [0, 0, 2, 1], 3, 3, 4, "3E-U-R"
      ],
      [
        [0, 0, 2, 1], 2, 3, 4, "3E-U-B"
      ],
      [
        [0, 0, 2, 1], 1, 3, 4, "3E-U-L"
      ],
      [
        [2, 2, 1, 1], 0, 3, 4, "3E-Pi-F"
      ],
      [
        [2, 2, 1, 1], 3, 3, 4, "3E-Pi-R"
      ],
      [
        [2, 2, 1, 1], 2, 3, 4, "3E-Pi-B"
      ],
      [
        [2, 2, 1, 1], 1, 3, 4, "3E-Pi-L"
      ],
      [
        [2, 1, 2, 1], 0, 3, 4, "3E-H-F"
      ],
      [
        [2, 1, 2, 1], 3, 3, 4, "3E-H-R"
      ],
      [
        [0, 0, 0, 0], 0, 3, 4, "3E-O-F"
      ],
      [
        [2, 0, 2, 2], 0, 1, 4, "1E-S-F"
      ],
      [
        [2, 0, 2, 2], 3, 1, 4, "1E-S-R"
      ],
      [
        [2, 0, 2, 2], 2, 1, 4, "1E-S-B"
      ],
      [
        [2, 0, 2, 2], 1, 1, 4, "1E-S-L"
      ],
      [
        [0, 1, 1, 1],
        0, 1, 4, "1E-A-F"
      ],
      [
        [0, 1, 1, 1], 3, 1, 4, "1E-A-R"
      ],
      [
        [0, 1, 1, 1], 2, 1, 4, "1E-A-B"
      ],
      [
        [0, 1, 1, 1], 1, 1, 4, "1E-A-L"
      ],
      [
        [0, 0, 1, 2], 0, 1, 4, "1E-T-F"
      ],
      [
        [0, 0, 1, 2], 3, 1, 4, "1E-T-R"
      ],
      [
        [0, 0, 1, 2], 2, 1, 4, "1E-T-B"
      ],
      [
        [0, 0, 1, 2], 1, 1, 4, "1E-T-L"
      ],
      [
        [0, 1, 0, 2], 0, 1, 4, "1E-L-F"
      ],
      [
        [0, 1, 0, 2], 3, 1, 4, "1E-L-R"
      ],
      [
        [0, 1, 0, 2], 2, 1, 4, "1E-L-B"
      ],
      [
        [0, 1, 0, 2], 1, 1, 4, "1E-L-L"
      ],
      [
        [0, 0, 2, 1], 0, 1, 4, "1E-U-F"
      ],
      [
        [0, 0, 2, 1], 3, 1, 4, "1E-U-R"
      ],
      [
        [0, 0, 2, 1], 2, 1, 4, "1E-U-B"
      ],
      [
        [0, 0, 2, 1], 1, 1, 4, "1E-U-L"
      ],
      [
        [2, 2, 1, 1], 0, 1, 4, "1E-Pi-F"
      ],
      [
        [2, 2, 1, 1], 3, 1, 4, "1E-Pi-R"
      ],
      [
        [2, 2, 1, 1], 2, 1, 4, "1E-Pi-B"
      ],
      [
        [2, 2, 1, 1], 1, 1, 4, "1E-Pi-L"
      ],
      [
        [2, 1, 2, 1], 0, 1, 4, "1E-H-F"
      ],
      [
        [2, 1, 2, 1], 3, 1, 4, "1E-H-R"
      ],
      [
        [0, 0, 0, 0], 0, 1, 4, "1E-O-F"
      ]
    ],
    Cd = mathlib.idxArray(Hc, 3),
    Dd = mathlib.idxArray(Hc, 4);
  scrMgr.reg("444wca", Ra)("4edge", function() {
    return Na(0, 16777215, 255)
  })("444edo", function() {
    return Na(0, 16777215, 0)
  })("444cto", function() {
    return Na(16777215, 0, 0)
  })("444ll", function(v, aa, ha, va) {
    return Na(0, 983280, 240, va)
  })("444ell", function(v, aa, ha, va) {
    return Na(0, 983280, 0, va)
  })("444ctud", function(v, aa, ha, va) {
    return Na(16776960, 16777215, 255,
      va)
  })("444ctrl", function(v, aa, ha, va) {
    return Na(65535, 16777215, 255, va)
  })("444l8e", function(v, aa, ha, va) {
    v = Na(0, 15793935, 255, va);
    return cb(v, 0)
  })("444ud3c", function(v, aa, ha, va) {
    v = mathlib.rn(4);
    return Na(16776960, 16715760 | 4097 << v, 255, va)
  })("444rlda", function(v, aa, ha, va) {
    v = 4 * mathlib.rn(2);
    return Na(240 | 3840 << v, 16777215, 255, va)
  })("444rlca", function(v, aa, ha, va) {
    v = 4 * mathlib.rn(2);
    return Na(240 | 3840 << v, 16715760, 255, va)
  })("444ppll", function(v, aa, ha, va) {
    v = hd[scrMgr.fixCase(ha, zd)];
    return qb(v[0], [0, 0, 0, 0], v[1],
      [0, 0, 0, 0], va, [0, 1, 2, 3], [0, 1, 2, 3], 0)
  }, [Ad, zd, function(v, aa) {
    var ha = Bd[v][0],
      va = Bd[v].slice(1);
    2 == va.length && (va = va.concat([
      [va[0][1], va[0][0]],
      [va[1][1], va[1][0]]
    ]));
    for (var Aa = "", Ea = 0; 4 > Ea; Ea++) {
      var Ja = ha[3 * Ea + 1];
      Aa += ha[3 * Ea] + Ja + Ja + ha[3 * Ea + 2]
    }
    ha = [
      [0, 0],
      [1.5, 0],
      [3, 0],
      [0, 1.5],
      [1.5, 1.5],
      [3, 1.5],
      [0, 3],
      [1.5, 3],
      [3, 3]
    ];
    Ea = [];
    for (Ja = 0; Ja < va.length; Ja++) Ea.push([ha[va[Ja][0]], ha[va[Ja][1]]]);
    va = ["DDDDDDDDDDDDDDDD" + Aa, Ea];
    if (!aa) return va.concat([Ad[v]]);
    image.llImage.drawImage(va[0], va[1], aa)
  }])("444poll",
    function(v, aa, ha, va) {
      ha = Hc[scrMgr.fixCase(ha, Cd)];
      v = ha[0];
      aa = ha[1];
      ha = ha[2];
      for (var Aa = [], Ea = 0; 4 > Ea; Ea++) Aa[Ea] = 3 == ha ? Ea == aa ? 1 : 0 : Ea == aa ? 0 : 1;
      return qb([-1, -1, -1, -1], Aa, [-1, -1, -1, -1], v, va, [0, 1, 2, 3], [0, 1, 2, 3], 0)
    }, [Dd, Cd, function(v, aa) {
      var ha = [
          [15, 20, 19],
          [12, 16, 31],
          [0, 28, 27],
          [3, 24, 23]
        ],
        va = [
          [13, 14],
          [4, 8],
          [1, 2],
          [7, 11]
        ],
        Aa = [
          [17, 18],
          [30, 29],
          [26, 25],
          [21, 22]
        ],
        Ea = Hc[v],
        Ja = Ea[0],
        Qa = Ea[1];
      Ea = Ea[2];
      for (var Pa = [], Wa = 0; 32 > Wa; Wa++) Pa[Wa] = "G";
      Pa[5] = "D";
      Pa[6] = "D";
      Pa[9] = "D";
      Pa[10] = "D";
      for (Wa = 0; 4 > Wa; Wa++) Pa[ha[Wa][Ja[Wa]]] =
        "D";
      for (ha = 0; 4 > ha; ha++) Ja = va[ha], Wa = Aa[ha], (3 == Ea ? ha == Qa : ha != Qa) ? (Pa[Wa[0]] = "D", Pa[Wa[1]] = "D") : (Pa[Ja[0]] = "D", Pa[Ja[1]] = "D");
      va = [Pa.join(""), null];
      if (!aa) return va.concat([Dd[v]]);
      image.llImage.drawImage(va[0], va[1], aa)
    }]);
  return {
    getRandomScramble: Ra,
    getPartialScramble: Na,
    testbench: function(v) {
      fb();
      v = v || 100;
      for (var aa = [], ha = 0; ha < v; ha++) {
        for (var va = Ta(16777215, 16777215, 255).split(""), Aa = 0; 96 > Aa; Aa++) va[Aa] = "URFDLB".indexOf(va[Aa]);
        Wb.c = new Ka;
        Aa = ia(Wb.c, va);
        0 != Aa && console.log("[scramble 444] State Check Error!",
          Aa, va);
        $.now();
        va = ra(Wb);
        for (Aa = 0; Aa < va.length; Aa++) aa[Aa] = (aa[Aa] || 0) + va[Aa];
        console.log(aa.map(function(Ea) {
          return ~~(100 * Ea / (ha + 1)) / 100
        }))
      }
    }
  }
}(mathlib.Cnk, mathlib.circle);
module.exports = { mathlib: mathlib, grouplib: grouplib, min2phase: min2phase, scrMgr: scrMgr, scramble_333: scramble_333, scramble_222: scramble_222, scramble_444: scramble_444 };
````

### 11.2 `min2phase.js`

（单独的两阶段求解器，`solve` / `fromScramble` / `randomCube`，结尾 `module.exports = min2phase`。）

````js
var min2phase = function() {
  function a() {
    this.move = [];
    this.moveSol = [];
    this.nodeUD = [];
    this.valid1 = 0;
    this.allowShorter = !1;
    this.cc = new r;
    this.urfCubieCube = [];
    this.urfCoordCube = [];
    this.phase1Cubie = [];
    this.preMoveCubes = [];
    this.preMoves = [];
    this.maxPreMoves = this.preMoveLen = 0;
    this.isRec = !1;
    for (var U = 0; 21 > U; U++) this.nodeUD[U] = new e, this.phase1Cubie[U] = new r;
    for (U = 0; 6 > U; U++) this.urfCubieCube[U] = new r, this.urfCoordCube[U] = new e;
    for (U = 0; 20 > U; U++) this.preMoveCubes[U + 1] = new r
  }

  function J(U, fa, ea) {
    U[fa >> 3] ^= ea << (fa <<
      2)
  }

  function t(U, fa, ea) {
    return Math.min(U, fa[ea >> 3] >> (ea << 2) & 15)
  }

  function G(U, fa, ea) {
    U = Ga[U];
    ea && (U ^= 14540032 >> ((U & 15) << 1) & 3);
    return U & 65520 | m[U & 15][fa]
  }

  function r() {
    this.ca = [0, 1, 2, 3, 4, 5, 6, 7];
    this.ea = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  }

  function y(U, fa, ea) {
    ea--;
    for (var la = 1985229328, pa = 0; pa < ea; ++pa) {
      var qa = M[ea - pa],
        Fa = ~~(fa / qa);
      fa %= qa;
      Fa <<= 2;
      U[pa] = U[pa] & 240 | la >> Fa & 15;
      qa = (1 << Fa) - 1;
      la = (la & qa) + (la >> 4 & ~qa)
    }
    U[ea] = U[ea] & 240 | la & 15
  }

  function c(U, fa) {
    for (var ea = 0, la = 1985229328, pa = 0; pa < fa - 1; ++pa) {
      var qa = (U[pa] & 15) << 2;
      ea = (fa - pa) * ea + (la >> qa & 15);
      la -= 286331152 << qa
    }
    return ea
  }

  function n(U, fa, ea) {
    U[ea - 1] &= 240;
    for (var la = ea - 2; 0 <= la; --la) {
      U[la] = U[la] & 240 | fa % (ea - la);
      fa = ~~(fa / (ea - la));
      for (var pa = la + 1; pa < ea; ++pa)(U[pa] & 15) >= (U[la] & 15) && (U[pa] += 1)
    }
  }

  function h(U, fa) {
    for (var ea = 0, la = 0; la < fa; ++la) {
      ea *= fa - la;
      for (var pa = la + 1; pa < fa; ++pa)(U[pa] & 15) < (U[la] & 15) && ++ea
    }
    return ea
  }

  function k(U, fa) {
    for (var ea = 0, la = 4, pa = U.length - 1; 0 <= pa; pa--)(U[pa] & 12) == fa && (ea += u[pa][la--]);
    return ea
  }

  function b(U, fa, ea) {
    for (var la = U.length - 1, pa = 4, qa = la; 0 <=
      la; la--) fa >= u[la][pa] ? (fa -= u[la][pa--], U[la] = U[la] & 240 | pa | ea) : ((qa & 12) == ea && (qa -= 4), U[la] = U[la] & 240 | qa--)
  }

  function d(U, fa) {
    for (var ea = 0, la = fa - 2; 0 <= la; la--) ea ^= U % (fa - la), U = ~~(U / (fa - la));
    return ea & 1
  }

  function e() {
    this.flipc = this.twstc = this.prun = this.slice = this.flip = this.twst = 0
  }

  function l() {
    function U(Oa, bb, fb, Ta, eb, Na, Ra) {
      for (var cb = new r, $a = new r, Ya = 0, nb = 2 <= eb ? 1 : 2, qb = 1 != eb ? r.EdgeConjugate : r.CornConjugate, db = 0; db < Oa; db++)
        if (void 0 === fb[db]) {
          Na.call(cb, db);
          for (var ab = 0; 16 > ab; ab += nb) {
            qb(cb, ab, $a);
            var sb =
              Ra.call($a);
            0 == eb && (O[Ya << 3 | ab >> 1] = sb);
            sb == db && (Ta[Ya] |= 1 << ab / nb);
            fb[sb] = (Ya << 4 | ab) / nb
          }
          bb[Ya++] = db
        } return Ya
    }

    function fa(Oa, bb, fb, Ta, eb, Na, Ra, cb) {
      for (var $a = 0; $a < fb; $a++) {
        eb.call(ea, bb[$a]);
        for (var Ya = 0; Ya < Ta; Ya++) Ra(ea, S[cb ? cb[Ya] : Ya], la), Oa[$a * Ta + Ya] = Na.call(la)
      }
    }
    for (var ea = new r, la = new r, pa = (new r).initCoord(28783, 0, 259268407, 0), qa = (new r).initCoord(15138, 0, 119765538, 7), Fa = (new r).initCoord(5167, 0, 83473207, 0), Da = 0; 8 > Da; Da++) Fa.ca[Da] |= 48;
    for (Da = 0; 16 > Da; Da++) f[Da] = (new r).init(ea.ca, ea.ea), r.CornMultFull(ea,
      qa, la), r.EdgeMult(ea, qa, la), ea.init(la.ca, la.ea), 3 == Da % 4 && (r.CornMultFull(ea, Fa, la), r.EdgeMult(ea, Fa, la), ea.init(la.ca, la.ea)), 7 == Da % 8 && (r.CornMultFull(ea, pa, la), r.EdgeMult(ea, pa, la), ea.init(la.ca, la.ea));
    for (Da = 0; 16 > Da; Da++) m[Da] = [], D[Da] = [], z[Da] = [], F[Da] = [], H[Da] = [];
    for (Da = 0; 16 > Da; Da++)
      for (pa = 0; 16 > pa; pa++) m[Da][pa] = Da ^ pa ^ 84660 >> pa & Da << 1 & 2, D[m[Da][pa]][pa] = Da;
    ea = new r;
    for (Da = 0; 16 > Da; Da++)
      for (pa = 0; 18 > pa; pa++) {
        r.CornConjugate(S[pa], D[0][Da], ea);
        qa = 0;
        a: for (; 18 > qa; qa++) {
          for (Fa = 0; 8 > Fa; Fa++)
            if (S[qa].ca[Fa] !=
              ea.ca[Fa]) continue a;
          z[Da][pa] = qa;
          H[Da][K[pa]] = K[qa];
          break
        }
        0 == Da % 2 && (F[pa << 3 | Da >> 1] = z[Da][pa])
      }
    U(2048, P, C, E, 0, r.prototype.setFlip, r.prototype.getFlip);
    U(2187, Q, ba, ja, 1, r.prototype.setTwst, r.prototype.getTwst);
    U(40320, wa, Ca, sa, 2, r.prototype.setEPerm, r.prototype.getEPerm);
    pa = new r;
    for (Da = 0; 2768 > Da; Da++) y(pa.ea, wa[Da], 8), ua[Da] = k(pa.ea, 0) + 70 * d(wa[Da], 8), ea.invFrom(pa), Ga[Da] = Ca[ea.getEPerm()];
    ea = new r;
    la = new r;
    fa(ya, P, 336, 18, r.prototype.setFlip, r.prototype.getFlipSym, r.EdgeMult);
    fa(Ha, Q, 324, 18, r.prototype.setTwst,
      r.prototype.getTwstSym, r.CornMult);
    fa(ia, wa, 2768, 10, r.prototype.setEPerm, r.prototype.getEPermSym, r.EdgeMult, L);
    fa(ca, wa, 2768, 10, r.prototype.setCPerm, r.prototype.getCPermSym, r.CornMult, L);
    for (Da = 0; 495 > Da; Da++) {
      ea.setSlice(Da);
      for (pa = 0; 18 > pa; pa++) r.EdgeMult(ea, S[pa], la), ka[18 * Da + pa] = la.getSlice();
      for (pa = 0; 16 > pa; pa += 2) r.EdgeConjugate(ea, D[0][pa], la), Y[Da << 3 | pa >> 1] = la.getSlice()
    }
    for (Da = 0; 24 > Da; Da++) {
      ea.setMPerm(Da);
      for (pa = 0; 10 > pa; pa++) r.EdgeMult(ea, S[L[pa]], la), ma[10 * Da + pa] = la.getMPerm();
      for (pa = 0; 16 >
        pa; pa++) r.EdgeConjugate(ea, D[0][pa], la), xa[Da << 4 | pa] = la.getMPerm()
    }
    for (Da = 0; 140 > Da; Da++) {
      ea.setCComb(Da % 70);
      for (pa = 0; 10 > pa; pa++) r.CornMult(ea, S[L[pa]], la), Ba[10 * Da + pa] = la.getCComb() + 70 * (165 >> pa & 1 ^ ~~(Da / 70));
      for (pa = 0; 16 > pa; pa++) r.CornConjugate(ea, D[0][pa], la), da[Da << 4 | pa] = la.getCComb() + 70 * ~~(Da / 70)
    }
  }

  function q(U, fa, ea, la, pa, qa, Fa, Da) {
    var Oa = Da & 15,
      bb = 1 == (Da >> 4 & 1) ? 14540032 : 0,
      fb = Da >> 8 & 15,
      Ta = Da >> 12 & 15,
      eb = Da >> 16 & 15,
      Na = (1 << Oa) - 1,
      Ra = null == la;
    ea *= fa;
    Da = 1 == (Da >> 5 & 1) ? 10 : 18;
    var cb = 10 == Da ? 66 : 599186,
      $a = (U[ea >>
        3] >> (ea << 2) & 15) - 1;
    if (-1 == $a) {
      for (var Ya = 0; Ya < (ea >> 3) + 1; Ya++) U[Ya] = -1;
      J(U, 0, 15);
      $a = 0
    } else J(U, ea, 15 ^ $a + 1);
    for (Ta = 0 < x ? Math.min(Math.max($a + 1, eb), Ta) : Ta; $a < Ta;) {
      var nb = (eb = $a > fb) ? 15 : $a,
        qb = 286331153 * nb,
        db = eb ? $a : 15;
      $a++;
      za++;
      var ab = $a ^ 15,
        sb = 0,
        Ab = 0;
      for (Ya = 0; Ya < ea; Ya++, Ab >>= 4) {
        if (0 == (Ya & 7)) {
          Ab = U[Ya >> 3];
          var ub = Ab ^ qb;
          if (0 == (ub - 286331153 & ~ub & 2290649224)) {
            Ya += 7;
            continue
          }
        }
        if ((Ab & 15) == nb) {
          ub = Ya % fa;
          var Xa = ~~(Ya / fa),
            ib = 0,
            Cb = 0;
          Ra && (ib = C[ub], Cb = ib & 7, ib >>= 3);
          for (var pb = 0; pb < Da; pb++) {
            var ob = qa[Xa * Da + pb];
            var tb = Ra ? O[ya[ib *
              Da + F[pb << 3 | Cb]] ^ Cb ^ ob & Na] : pa[la[ub * Da + pb] << Oa | ob & Na];
            ob >>= Oa;
            var La = ob * fa + tb,
              Sa = U[La >> 3] >> (La << 2) & 15;
            if (Sa != db) Sa < $a - 1 && (pb += cb >> pb & 3);
            else {
              sb++;
              if (eb) {
                J(U, Ya, ab);
                break
              }
              J(U, La, ab);
              La = 1;
              for (Sa = Fa[ob]; 0 != (Sa >>= 1); La++)
                if (1 == (Sa & 1)) {
                  var Za = ob * fa;
                  Za = Ra ? Za + O[C[tb] ^ La] : Za + pa[tb << Oa | La ^ bb >> (La << 1) & 3];
                  (U[Za >> 3] >> (Za << 2) & 15) == db && (J(U, Za, ab), sb++)
                }
            }
          }
        }
      }
    }
    J(U, ea, $a + 1 ^ 15);
    return $a + 1
  }

  function g(U) {
    Ia = q(V, 2048, 324, null, null, Ha, ja, 103939);
    za > U || (Ka = q(Z, 495, 324, ka, Y, Ha, ja, 431619), za > U || (Ma = q(oa, 495, 336, ka, Y, ya, E,
      431619), za > U || (Ua = q(ta, 24, 2768, ma, xa, ca, sa, 584244), za > U || (ra = q(na, 140, 2768, Ba, da, ia, sa, 514084)))))
  }

  function p() {
    0 > za && (l(), za = 0);
    if (0 == za) g(99);
    else if (54 > za) g(za);
    else return !0;
    return !1
  }
  for (var x = 2, u = [], M = [1], T = "U ;U2;U';R ;R2;R';F ;F2;F';D ;D2;D';L ;L2;L';B ;B2;B'".split(";"), L = [0, 1, 2, 4, 7, 9, 10, 11, 13, 16, 3, 5, 6, 8, 12, 14, 15, 17], K = [], I = [], w = [
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
      [6, 7, 8, 0, 1, 2, 3, 4, 5, 15, 16, 17, 9, 10, 11, 12, 13, 14],
      [3, 4, 5, 6, 7, 8, 0, 1, 2, 12, 13, 14, 15, 16, 17, 9, 10, 11],
      [2, 1, 0, 5, 4, 3, 8, 7, 6, 11, 10,
        9, 14, 13, 12, 17, 16, 15
      ],
      [8, 7, 6, 2, 1, 0, 5, 4, 3, 17, 16, 15, 11, 10, 9, 14, 13, 12],
      [5, 4, 3, 8, 7, 6, 2, 1, 0, 14, 13, 12, 17, 16, 15, 11, 10, 9]
    ], B = 0; 18 > B; B++) K[L[B]] = B;
  for (B = 0; 10 > B; B++)
    for (var A = ~~(L[B] / 3), N = I[B] = 0; 10 > N; N++) {
      var R = ~~(L[N] / 3);
      I[B] |= (A == R || A % 3 == R % 3 && A >= R ? 1 : 0) << N
    }
  for (B = I[10] = 0; 13 > B; B++)
    for (u[B] = [], M[B + 1] = M[B] * (B + 1), N = u[B][0] = u[B][B] = 1; 13 > N; N++) u[B][N] = N <= B ? u[B - 1][N - 1] + u[B - 1][N] : 0;
  r.EdgeMult = function(U, fa, ea) {
    for (var la = 0; 12 > la; la++) ea.ea[la] = U.ea[fa.ea[la] & 15] ^ fa.ea[la] & 16
  };
  r.CornMult = function(U, fa, ea) {
    for (var la =
        0; 8 > la; la++) ea.ca[la] = U.ca[fa.ca[la] & 15] & 15 | ((U.ca[fa.ca[la] & 15] >> 4) + (fa.ca[la] >> 4)) % 3 << 4
  };
  r.CornMultFull = function(U, fa, ea) {
    for (var la = 0; 8 > la; la++) {
      var pa = U.ca[fa.ca[la] & 15] >> 4,
        qa = fa.ca[la] >> 4,
        Fa = pa + (3 > pa ? qa : 6 - qa);
      Fa = Fa % 3 + (3 > pa == 3 > qa ? 0 : 3);
      ea.ca[la] = U.ca[fa.ca[la] & 15] & 15 | Fa << 4
    }
  };
  r.CornConjugate = function(U, fa, ea) {
    var la = f[D[0][fa]];
    fa = f[fa];
    for (var pa = 0; 8 > pa; pa++) {
      var qa = U.ca[fa.ca[pa] & 15] >> 4;
      ea.ca[pa] = la.ca[U.ca[fa.ca[pa] & 15] & 15] & 15 | (3 > la.ca[U.ca[fa.ca[pa] & 15] & 15] >> 4 ? qa : (3 - qa) % 3) << 4
    }
  };
  r.EdgeConjugate =
    function(U, fa, ea) {
      var la = f[D[0][fa]];
      fa = f[fa];
      for (var pa = 0; 12 > pa; pa++) ea.ea[pa] = la.ea[U.ea[fa.ea[pa] & 15] & 15] ^ U.ea[fa.ea[pa] & 15] & 16 ^ fa.ea[pa] & 16
    };
  r.prototype.init = function(U, fa) {
    this.ca = U.slice();
    this.ea = fa.slice();
    return this
  };
  r.prototype.initCoord = function(U, fa, ea, la) {
    y(this.ca, U, 8);
    this.setTwst(fa);
    n(this.ea, ea, 12);
    this.setFlip(la);
    return this
  };
  r.prototype.isEqual = function(U) {
    for (var fa = 0; 8 > fa; fa++)
      if (this.ca[fa] != U.ca[fa]) return !1;
    for (fa = 0; 12 > fa; fa++)
      if (this.ea[fa] != U.ea[fa]) return !1;
    return !0
  };
  r.prototype.setFlip = function(U) {
    for (var fa = 0, ea = 10; 0 <= ea; ea--, U >>= 1) this.ea[ea] = this.ea[ea] & 15 | (U & 1) << 4, fa ^= this.ea[ea];
    this.ea[11] = this.ea[11] & 15 | fa & 16
  };
  r.prototype.getFlip = function() {
    for (var U = 0, fa = 0; 11 > fa; fa++) U = U << 1 | this.ea[fa] >> 4 & 1;
    return U
  };
  r.prototype.getFlipSym = function() {
    return C[this.getFlip()]
  };
  r.prototype.setTwst = function(U) {
    for (var fa = 15, ea = 6; 0 <= ea; ea--, U = ~~(U / 3)) this.ca[ea] = this.ca[ea] & 15 | U % 3 << 4, fa -= this.ca[ea] >> 4;
    this.ca[7] = this.ca[7] & 15 | fa % 3 << 4
  };
  r.prototype.getTwst = function() {
    for (var U =
        0, fa = 0; 7 > fa; fa++) U += (U << 1) + (this.ca[fa] >> 4);
    return U
  };
  r.prototype.getTwstSym = function() {
    return ba[this.getTwst()]
  };
  r.prototype.setCPerm = function(U) {
    y(this.ca, U, 8)
  };
  r.prototype.getCPerm = function() {
    return c(this.ca, 8)
  };
  r.prototype.getCPermSym = function() {
    var U = Ca[c(this.ca, 8)];
    return U ^ 14540032 >> ((U & 15) << 1) & 3
  };
  r.prototype.setEPerm = function(U) {
    y(this.ea, U, 8)
  };
  r.prototype.getEPerm = function() {
    return c(this.ea, 8)
  };
  r.prototype.getEPermSym = function() {
    return Ca[c(this.ea, 8)]
  };
  r.prototype.getSlice = function() {
    return 494 -
      k(this.ea, 8)
  };
  r.prototype.setSlice = function(U) {
    b(this.ea, 494 - U, 8)
  };
  r.prototype.getMPerm = function() {
    return h(this.ea, 12) % 24
  };
  r.prototype.setMPerm = function(U) {
    n(this.ea, U, 12)
  };
  r.prototype.getCComb = function() {
    return k(this.ca, 0)
  };
  r.prototype.setCComb = function(U) {
    b(this.ca, U, 0)
  };
  r.prototype.URFConjugate = function() {
    var U = new r;
    r.CornMult(r.urf2, this, U);
    r.CornMult(U, r.urf1, this);
    r.EdgeMult(r.urf2, this, U);
    r.EdgeMult(U, r.urf1, this)
  };
  var W = [
      [8, 9, 20],
      [6, 18, 38],
      [0, 36, 47],
      [2, 45, 11],
      [29, 26, 15],
      [27, 44, 24],
      [33,
        53, 42
      ],
      [35, 17, 51]
    ],
    X = [
      [5, 10],
      [7, 19],
      [3, 37],
      [1, 46],
      [32, 16],
      [28, 25],
      [30, 43],
      [34, 52],
      [23, 12],
      [21, 41],
      [50, 39],
      [48, 14]
    ];
  r.prototype.toFaceCube = function(U, fa) {
    U = U || W;
    fa = fa || X;
    for (var ea = [], la = 0; 54 > la; la++) ea[la] = "URFDLB" [~~(la / 9)];
    for (var pa = 0; 8 > pa; pa++) {
      la = this.ca[pa] & 15;
      for (var qa = this.ca[pa] >> 4, Fa = 0; 3 > Fa; Fa++) ea[U[pa][(Fa + qa) % 3]] = "URFDLB" [~~(U[la][Fa] / 9)]
    }
    for (U = 0; 12 > U; U++)
      for (la = this.ea[U] & 15, qa = this.ea[U] >> 4, Fa = 0; 2 > Fa; Fa++) ea[fa[U][(Fa + qa) % 2]] = "URFDLB" [~~(fa[la][Fa] / 9)];
    return ea.join("")
  };
  r.prototype.invFrom =
    function(U) {
      for (var fa = 0; 12 > fa; fa++) this.ea[U.ea[fa] & 15] = fa & 15 | U.ea[fa] & 16;
      for (fa = 0; 8 > fa; fa++) this.ca[U.ca[fa] & 15] = fa | 64 >> (U.ca[fa] >> 4) & 48;
      return this
    };
  r.prototype.fromFacelet = function(U, fa, ea) {
    fa = fa || W;
    ea = ea || X;
    for (var la = 0, pa = [], qa = U[4] + U[13] + U[22] + U[31] + U[40] + U[49], Fa = 0; 54 > Fa; ++Fa) {
      pa[Fa] = qa.indexOf(U[Fa]);
      if (-1 == pa[Fa]) return -1;
      la += 1 << (pa[Fa] << 2)
    }
    if (10066329 != la) return -1;
    var Da;
    for (Fa = 0; 8 > Fa; ++Fa) {
      for (Da = 0; 3 > Da && 0 != pa[fa[Fa][Da]] && 3 != pa[fa[Fa][Da]]; ++Da);
      U = pa[fa[Fa][(Da + 1) % 3]];
      la = pa[fa[Fa][(Da +
        2) % 3]];
      for (qa = 0; 8 > qa; ++qa)
        if (U == ~~(fa[qa][1] / 9) && la == ~~(fa[qa][2] / 9)) {
          this.ca[Fa] = qa | Da % 3 << 4;
          break
        }
    }
    for (Fa = 0; 12 > Fa; ++Fa)
      for (qa = 0; 12 > qa; ++qa) {
        if (pa[ea[Fa][0]] == ~~(ea[qa][0] / 9) && pa[ea[Fa][1]] == ~~(ea[qa][1] / 9)) {
          this.ea[Fa] = qa;
          break
        }
        if (pa[ea[Fa][0]] == ~~(ea[qa][1] / 9) && pa[ea[Fa][1]] == ~~(ea[qa][0] / 9)) {
          this.ea[Fa] = qa | 16;
          break
        }
      }
  };
  e.prototype.set = function(U) {
    this.twst = U.twst;
    this.flip = U.flip;
    this.slice = U.slice;
    this.prun = U.prun;
    this.twstc = U.twstc;
    this.flipc = U.flipc
  };
  e.prototype.calcPruning = function(U) {
    this.prun =
      Math.max(t(Ka, Z, 495 * (this.twst >> 3) + Y[this.slice << 3 | this.twst & 7]), t(Ma, oa, 495 * (this.flip >> 3) + Y[this.slice << 3 | this.flip & 7]), t(Ia, V, this.twstc >> 3 << 11 | O[this.flipc ^ this.twstc & 7]), t(Ia, V, this.twst >> 3 << 11 | O[this.flip ^ this.twst & 7]))
  };
  e.prototype.setWithPrun = function(U, fa) {
    this.twst = U.getTwstSym();
    this.flip = U.getFlipSym();
    this.prun = t(Ia, V, this.twst >> 3 << 11 | O[this.flip ^ this.twst & 7]);
    if (this.prun > fa) return !1;
    this.slice = U.getSlice();
    this.prun = Math.max(this.prun, t(Ka, Z, 495 * (this.twst >> 3) + Y[this.slice << 3 | this.twst &
      7]), t(Ma, oa, 495 * (this.flip >> 3) + Y[this.slice << 3 | this.flip & 7]));
    if (this.prun > fa) return !1;
    var ea = new r;
    r.CornConjugate(U, 1, ea);
    r.EdgeConjugate(U, 1, ea);
    this.twstc = ea.getTwstSym();
    this.flipc = ea.getFlipSym();
    this.prun = Math.max(this.prun, t(Ia, V, this.twstc >> 3 << 11 | O[this.flipc ^ this.twstc & 7]));
    return this.prun <= fa
  };
  e.prototype.doMovePrun = function(U, fa, ea) {
    this.slice = ka[18 * U.slice + fa];
    this.flip = ya[18 * (U.flip >> 3) + F[fa << 3 | U.flip & 7]] ^ U.flip & 7;
    this.twst = Ha[18 * (U.twst >> 3) + F[fa << 3 | U.twst & 7]] ^ U.twst & 7;
    return this.prun =
      Math.max(t(Ka, Z, 495 * (this.twst >> 3) + Y[this.slice << 3 | this.twst & 7]), t(Ma, oa, 495 * (this.flip >> 3) + Y[this.slice << 3 | this.flip & 7]), t(Ia, V, this.twst >> 3 << 11 | O[this.flip ^ this.twst & 7]))
  };
  e.prototype.doMovePrunConj = function(U, fa) {
    fa = z[3][fa];
    this.flipc = ya[18 * (U.flipc >> 3) + F[fa << 3 | U.flipc & 7]] ^ U.flipc & 7;
    this.twstc = Ha[18 * (U.twstc >> 3) + F[fa << 3 | U.twstc & 7]] ^ U.twstc & 7;
    return t(Ia, V, this.twstc >> 3 << 11 | O[this.flipc ^ this.twstc & 7])
  };
  a.prototype.solution = function(U, fa, ea, la, pa, qa, Fa) {
    p();
    U = this.verify(U);
    if (0 != U) return "Error " +
      Math.abs(U);
    void 0 === fa && (fa = 21);
    void 0 === ea && (ea = 1E9);
    void 0 === la && (la = 0);
    void 0 === pa && (pa = 0);
    this.sol = fa + 1;
    this.probe = 0;
    this.probeMax = ea;
    this.probeMin = Math.min(la, ea);
    this.verbose = pa;
    this.moveSol = null;
    this.isRec = !1;
    this.firstFilters = [0, 0, 0, 0, 0, 0];
    this.lastFilters = [0, 0, 0, 0, 0, 0];
    for (fa = 0; 3 > fa; fa++) void 0 !== qa && (this.firstFilters[fa] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * qa] / 3), this.lastFilters[fa + 3] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * qa] / 3)), void 0 !== Fa && (this.lastFilters[fa] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * Fa] / 3), this.firstFilters[fa +
      3] |= 3591 << 3 * ~~(w[(3 - fa) % 3][3 * Fa] / 3));
    this.initSearch();
    return this.search()
  };
  a.prototype.initSearch = function() {
    this.conjMask = 0;
    this.maxPreMoves = 7 < this.conjMask ? 0 : 20;
    for (var U = 0; 6 > U; U++)
      if (this.urfCubieCube[U].init(this.cc.ca, this.cc.ea), this.urfCoordCube[U].setWithPrun(this.urfCubieCube[U], 20), this.cc.URFConjugate(), 2 == U % 3) {
        var fa = (new r).invFrom(this.cc);
        this.cc.init(fa.ca, fa.ea)
      }
  };
  a.prototype.next = function(U, fa, ea) {
    this.probe = 0;
    this.probeMax = U;
    this.probeMin = Math.min(fa, U);
    this.moveSol = null;
    this.isRec = !0;
    this.verbose = ea;
    return this.search()
  };
  a.prototype.verify = function(U) {
    if (-1 == this.cc.fromFacelet(U)) return -1;
    for (var fa = U = 0, ea = 0; 12 > ea; ea++) fa |= 1 << (this.cc.ea[ea] & 15), U ^= this.cc.ea[ea] >> 4;
    if (4095 != fa) return -2;
    if (0 != U) return -3;
    for (ea = U = fa = 0; 8 > ea; ea++) fa |= 1 << (this.cc.ca[ea] & 15), U += this.cc.ca[ea] >> 4;
    return 255 != fa ? -4 : 0 != U % 3 ? -5 : 0 != (d(h(this.cc.ea, 12), 12) ^ d(this.cc.getCPerm(), 8)) ? -6 : 0
  };
  a.prototype.phase1PreMoves = function(U, fa, ea) {
    if (U == this.maxPreMoves - 1 && 0 != (this.lastFilter >> fa & 1)) return 1;
    this.preMoveLen =
      this.maxPreMoves - U;
    if (this.isRec ? this.depth1 == this.length1 - this.preMoveLen : 0 == this.preMoveLen || 0 == (225207 >> fa & 1))
      if (this.depth1 = this.length1 - this.preMoveLen, this.phase1Cubie[0].init(ea.ca, ea.ea), this.allowShorter = 7 == this.depth1 && 0 != this.preMoveLen, this.nodeUD[this.depth1 + 1].setWithPrun(ea, this.depth1) && 0 == this.phase1(this.nodeUD[this.depth1 + 1], this.depth1, -1)) return 0;
    if (0 == U || this.preMoveLen + 7 >= this.length1) return 1;
    var la = 0;
    if (1 == U || this.preMoveLen + 1 + 7 >= this.length1) la |= 225207;
    fa = 3 * ~~(fa / 3);
    for (var pa =
        0; 18 > pa; pa++)
      if (pa == fa || pa == fa - 9 || pa == fa + 9) pa += 2;
      else if (!(this.isRec && pa != this.preMoves[this.maxPreMoves - U] || 0 != (la & 1 << pa)) && (r.CornMult(S[pa], ea, this.preMoveCubes[U]), r.EdgeMult(S[pa], ea, this.preMoveCubes[U]), this.preMoves[this.maxPreMoves - U] = pa, 0 == this.phase1PreMoves(U - 1, pa, this.preMoveCubes[U]))) return 0;
    return 1
  };
  a.prototype.search = function() {
    for (this.length1 = this.isRec ? this.length1 : 0; this.length1 < this.sol; this.length1++)
      for (this.urfIdx = this.isRec ? this.urfIdx : 0; 6 > this.urfIdx; this.urfIdx++)
        if (0 ==
          (this.conjMask & 1 << this.urfIdx) && (this.firstFilter = this.firstFilters[this.urfIdx], this.lastFilter = this.lastFilters[this.urfIdx], 0 == this.phase1PreMoves(this.maxPreMoves, -30, this.urfCubieCube[this.urfIdx], 0))) return null == this.moveSol ? "Error 8" : this.moveSol;
    return null == this.moveSol ? "Error 7" : this.moveSol
  };
  a.prototype.initPhase2Pre = function() {
    this.isRec = !1;
    if (this.probe >= (null == this.moveSol ? this.probeMax : this.probeMin)) return 0;
    ++this.probe;
    for (var U = this.valid1; U < this.depth1; U++) r.CornMult(this.phase1Cubie[U],
      S[this.move[U]], this.phase1Cubie[U + 1]), r.EdgeMult(this.phase1Cubie[U], S[this.move[U]], this.phase1Cubie[U + 1]);
    this.valid1 = this.depth1;
    U = this.initPhase2(this.phase1Cubie[this.depth1]);
    if (0 == U || 0 == this.preMoveLen || 2 == U) return U;
    U = 3 * ~~(this.preMoves[this.preMoveLen - 1] / 3) + 1;
    r.CornMult(S[U], this.phase1Cubie[this.depth1], this.phase1Cubie[this.depth1 + 1]);
    r.EdgeMult(S[U], this.phase1Cubie[this.depth1], this.phase1Cubie[this.depth1 + 1]);
    this.preMoves[this.preMoveLen - 1] += 2 - this.preMoves[this.preMoveLen - 1] % 3 * 2;
    U = this.initPhase2(this.phase1Cubie[this.depth1 + 1]);
    this.preMoves[this.preMoveLen - 1] += 2 - this.preMoves[this.preMoveLen - 1] % 3 * 2;
    return U
  };
  a.prototype.initPhase2 = function(U) {
    var fa = U.getCPermSym(),
      ea = fa & 15;
    fa >>= 4;
    var la = U.getEPermSym(),
      pa = la & 15;
    la >>= 4;
    U = U.getMPerm();
    var qa = Math.max(t(ra, na, 140 * la + da[(ua[fa] & 255) << 4 | D[pa][ea]]), t(Ua, ta, 24 * fa + xa[U << 4 | ea])),
      Fa = Math.min(13, this.sol - this.length1);
    if (qa >= Fa) return qa > Fa ? 2 : 1;
    var Da;
    for (Da = Fa - 1; Da >= qa; Da--) {
      var Oa = this.phase2(la, pa, fa, ea, U, Da, this.depth1, 10);
      if (0 > Oa) break;
      Da -= Oa;
      this.moveSol = [];
      for (Oa = 0; Oa < this.depth1 + Da; Oa++) this.appendSolMove(this.move[Oa]);
      for (Oa = this.preMoveLen - 1; 0 <= Oa; Oa--) this.appendSolMove(this.preMoves[Oa]);
      this.sol = this.moveSol.length;
      this.moveSol = this.solutionToString()
    }
    return Da != Fa - 1 ? this.probe >= this.probeMin ? 0 : 1 : 1
  };
  a.prototype.phase1 = function(U, fa, ea) {
    if (fa == this.depth1 - 1 && 0 != (this.firstFilter >> ea & 1)) return 1;
    if (0 == U.prun && 5 > fa) {
      if (this.allowShorter || 0 == fa) {
        this.depth1 -= fa;
        var la = this.initPhase2Pre();
        this.depth1 += fa;
        return la
      }
      return 1
    }
    for (var pa =
        0; 18 > pa; pa += 3)
      if (pa != ea && pa != ea - 9)
        for (var qa = 0; 3 > qa; qa++)
          if (la = pa + qa, !this.isRec || la == this.move[this.depth1 - fa]) {
            var Fa = this.nodeUD[fa].doMovePrun(U, la, !0);
            if (Fa > fa) break;
            else if (Fa == fa) continue;
            Fa = this.nodeUD[fa].doMovePrunConj(U, la);
            if (Fa > fa) break;
            else if (Fa == fa) continue;
            this.move[this.depth1 - fa] = la;
            this.valid1 = Math.min(this.valid1, this.depth1 - fa);
            la = this.phase1(this.nodeUD[fa], fa - 1, pa);
            if (0 == la) return 0;
            if (2 == la) break
          } return 1
  };
  a.prototype.appendSolMove = function(U) {
    if (0 == this.moveSol.length) this.moveSol.push(U);
    else {
      var fa = ~~(U / 3),
        ea = ~~(this.moveSol.at(-1) / 3);
      fa == ea ? (U = (U % 3 + this.moveSol.at(-1) % 3 + 1) % 4, 3 == U ? this.moveSol.pop() : this.moveSol.splice(-1, 1, 3 * fa + U)) : 1 < this.moveSol.length && fa % 3 == ea % 3 && fa == ~~(this.moveSol.at(-2) / 3) ? (U = (U % 3 + this.moveSol.at(-2) % 3 + 1) % 4, 3 == U ? (this.moveSol.splice(-2, 1, this.moveSol.at(-1)), this.moveSol.pop()) : this.moveSol.splice(-2, 1, 3 * fa + U)) : this.moveSol.push(U)
    }
  };
  a.prototype.phase2 = function(U, fa, ea, la, pa, qa, Fa, Da) {
    if (0 == this.depth1 && 1 == Fa && 0 != (this.firstFilter >> L[Da] & 1)) return -1;
    if (0 ==
      U && 0 == ea && 0 == pa && (0 < this.preMoveLen || 0 == (this.lastFilter >> L[Da] & 1))) return qa;
    Da = I[Da];
    for (var Oa = 0; 10 > Oa; Oa++)
      if (0 != (Da >> Oa & 1)) Oa += 66 >> Oa & 3;
      else {
        var bb = ma[10 * pa + Oa],
          fb = ca[10 * ea + H[la][Oa]],
          Ta = m[fb & 15][la];
        fb >>= 4;
        if (!(t(Ua, ta, 24 * fb + xa[bb << 4 | Ta]) >= qa)) {
          var eb = ia[10 * U + H[fa][Oa]],
            Na = m[eb & 15][fa];
          eb >>= 4;
          if (!(t(ra, na, 140 * eb + da[(ua[fb] & 255) << 4 | D[Na][Ta]]) >= qa)) {
            var Ra = G(eb, Na, !1),
              cb = G(fb, Ta, !0);
            if (!(t(ra, na, 140 * (Ra >> 4) + da[(ua[cb >> 4] & 255) << 4 | D[Ra & 15][cb & 15]]) >= qa) && (bb = this.phase2(eb, Na, fb, Ta, bb, qa - 1, Fa +
                1, Oa), 0 <= bb)) return this.move[Fa] = L[Oa], bb
          }
        }
      } return -1
  };
  a.prototype.solutionToString = function() {
    var U = "",
      fa = 0 != (this.verbose & 2) ? (this.urfIdx + 3) % 6 : this.urfIdx;
    if (3 > fa)
      for (var ea = 0; ea < this.moveSol.length; ++ea) U += T[w[fa][this.moveSol[ea]]] + " ";
    else
      for (ea = this.moveSol.length - 1; 0 <= ea; --ea) U += T[w[fa][this.moveSol[ea]]] + " ";
    return U
  };
  var S = [],
    f = [],
    m = [],
    D = [],
    z = [],
    H = [],
    F = [],
    P = [],
    C = [],
    E = [],
    O = [],
    Q = [],
    ba = [],
    ja = [],
    wa = [],
    Ca = [],
    sa = [],
    ua = [],
    Ga = [],
    Ha = [],
    ya = [],
    ka = [],
    Y = [],
    Z = [],
    oa = [],
    V = [],
    ca = [],
    ia = [],
    ma = [],
    xa = [],
    Ba = [],
    da = [],
    ta = [],
    na = [],
    Ia = 15,
    Ka = 15,
    Ma = 15,
    Ua = 15,
    ra = 15;
  for (B = 0; 18 > B; B++) S[B] = new r;
  S[0].initCoord(15120, 0, 119750400, 0);
  S[3].initCoord(21021, 1494, 323403417, 0);
  S[6].initCoord(8064, 1236, 29441808, 550);
  S[9].initCoord(9, 0, 5880, 0);
  S[12].initCoord(1230, 412, 2949660, 0);
  S[15].initCoord(224, 137, 328552, 137);
  for (B = 0; 18 > B; B += 3)
    for (A = 0; 2 > A; A++) r.EdgeMult(S[B + A], S[B], S[B + A + 1]), r.CornMult(S[B + A], S[B], S[B + A + 1]);
  r.urf1 = (new r).initCoord(2531, 1373, 67026819, 1367);
  r.urf2 = (new r).initCoord(2089, 1906, 322752913, 2040);
  var za = -1;
  return {
    Search: a,
    solve: function(U) {
      return (new a).solution(U)
    },
    randomCube: function() {
      var U = ~~(2048 * Math.random()),
        fa = ~~(2187 * Math.random());
      do {
        var ea = ~~(Math.random() * M[12]);
        var la = ~~(Math.random() * M[8])
      } while (d(la, 8) != d(ea, 12));
      return (new r).initCoord(la, fa, ea, U).toFaceCube()
    },
    fromScramble: function(U) {
      for (var fa = -1, ea = new r, la = new r, pa = 0; pa < U.length; pa++) switch (U[pa]) {
        case "U":
        case "R":
        case "F":
        case "D":
        case "L":
        case "B":
          fa = 3 * "URFDLB".indexOf(U[pa]);
          break;
        case " ":
          -1 != fa && (r.CornMult(ea, S[fa], la),
            r.EdgeMult(ea, S[fa], la), ea.init(la.ca, la.ea));
          fa = -1;
          break;
        case "2":
          fa++;
          break;
        case "'":
          fa += 2
      } - 1 != fa && (r.CornMult(ea, S[fa], la), r.EdgeMult(ea, S[fa], la), ea.init(la.ca, la.ea));
      return la.toFaceCube()
    },
    initFull: function() {
      x = 0;
      p()
    },
    INVERSE_SOLUTION: 2
  }
}();
"undefined" !== typeof module && "undefined" !== typeof module.exports && (module.exports = min2phase);

````

### 11.3 `demo.js`

````js
// csTimer 核心打乱算法提取件 —— 最小可运行 demo
// 用法: node demo.js
const cs = require('./csmin.js');
const { mathlib, min2phase, scrMgr } = cs;

console.log('=== 1) 3x3 随机状态打乱（WCA 合规，解随机状态）===');
const t0 = Date.now();
for (let i = 0; i < 3; i++) console.log('  ', cs.scramble_333.getRandomScramble().trim());
console.log(`   ${((Date.now() - t0) / 3).toFixed(1)} ms/个\n`);

console.log('=== 2) 4x4（归约法：4x4 -> 3x3，再用 min2phase 解）===');
const t1 = Date.now();
console.log('  ', scrMgr.scramblers['444wca']().trim(), `\n   ${Date.now() - t1} ms/个\n`);

console.log('=== 3) 子集打乱：只要有算法表就能生成指定 case ===');
for (const k of ['pll', 'oll', 'zbll', 'eoline', 'roux', '2gen']) {
  try { console.log('  ', k.padEnd(7), scrMgr.scramblers[k]().trim()); } catch (e) { console.log('  ', k, 'err', e.message); }
}

console.log('\n=== 4) syncseed：两台设备输入同一口令 -> 完全相同的打乱序列 ===');
function seq(seed, n) {
  mathlib.setSeed(256, 'syncseed' + seed);
  scrMgr.setEqPr(0);
  const out = [];
  for (let i = 0; i < n; i++) out.push(cs.scramble_333.getRandomScramble().trim());
  return out;
}
const a = seq('cubing2026', 3), b = seq('cubing2026', 3);
console.log('  设备A:', a[0]);
console.log('  设备B:', b[0]);
console.log('  一致:', JSON.stringify(a) === JSON.stringify(b));

console.log('\n=== 5) min2phase 单独使用（两阶段 Kociemba 求解器）===');
const s = new min2phase.Search();
const cube = min2phase.fromScramble("R U F2 D' B L2 ");
console.log('  打乱 R U F2 D\' B L2 后的面串:', cube);
console.log('  还原解:', s.solution(cube, 21, 1e9, 0, 0));
console.log('  逆解校验:', min2phase.solve(min2phase.fromScramble("R U F2 D' B L2 ")));

````

---

## 12. 提取件的边界

- **可用**：3x3 / 4x4 打乱，`pll/oll/coll/zbll/lse/cmll/roux/2gen/half` 等子集，
  `mathlib`（CubieCube）、`grouplib`、`min2phase`、`scrMgr`；
- **不可用**：`easyc/easyxc` 需要 `cross` 模块；`222so` 系列在最小桩环境下会挂
  （依赖 UI 侧对象）；`clock / pyraminx / skewb / sq1 / megaminx` 的源码段没有拼进来，
  按 §9 同样的方法可以逐段加。
- 未注入的桩：`DEBUG`、`$`（只实现 `isArray/now/noop`）、`image`（空实现）、`kernel`（空实现）。

---

## 13. 这套提取件用在哪

已用于给一个单文件 3D 魔方应用做打乱升级：

- 「随机走 20 步再化简」（平均只剩 15 步、最短 6 步）→ random-state（20.6 步，19–21）；
- 「底层归位」打乱从 39–62 步 → 18–21 步；
- 「最短解」引擎从 cubejs（冷启动 2.4 s）换成 min2phase（75 ms），
  并且发现 cubejs 的 `initSolver()` 可以拆成 move 表 516 ms + Kociemba 剪枝表 1742 ms，
  只建 move 表就能让层先法求解器正常工作。

---

## 14. 许可与致谢

- **csTimer** © cs0x7f，[GitHub](https://github.com/cs0x7f/cstimer)，**GPL-3.0**。
- 本文件包含 csTimer 发布包的片段（§2、§6 的摘录）与提取后的源码（§11），
  属于 GPL-3.0 的衍生作品，因此**本仓库同样以 GPL-3.0 发布**（见 `LICENSE`）。
  来源、版本与修改说明见 `NOTICE.md`。
- 目的：互操作研究、算法学习。csTimer 是免费服务，本项目不含任何破解/绕过付费功能的内容。
