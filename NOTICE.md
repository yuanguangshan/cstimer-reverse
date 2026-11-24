# 来源与修改说明

## 上游

| 项 | 值 |
|---|---|
| 程序 | csTimer — Professional Rubik's Cube Speeding Timer |
| 作者 | cs0x7f |
| 仓库 | https://github.com/cs0x7f/cstimer |
| 许可证 | GNU GPL v3.0 |
| 本文分析的版本 | `CSTIMER_VERSION = 2026.11.01` |
| 抓取对象 | https://cstimer.net/js/cstimer.js |
| 文件大小 | 634,417 字节 |
| SHA-256 | `f1771bf6cb3c48b88f05ab46aa0d60e811fcabd10ba03dfc91fd52bedcc6bbfc` |
| 抓取时间 | 2026-11-24 |

## 本仓库做了什么

1. 用 `js-beautify` 把压缩后的 `cstimer.js` 格式化为 26,451 行（`analysis/cstimer.pretty.js`，未入库，可按 README §10 重现）；
2. 按模块边界截取 `isaac` / `mathlib` / `grouplib` / `min2phase` / `scrMgr` /
   `scramble_333` / `scramble_222` / `scramble_444`，拼接成可在 Node 下 `require` 的 `csmin.js`；
3. 注入最小桩（`DEBUG`、`$`、`image`、`kernel`），替换掉浏览器环境依赖；
4. 修正截取处的语法（`scrMgr` 结尾的逗号改成分号）；
5. 编写 `README.md` 与 `src/demo.js`。

## 未做的修改

- 未改动任何算法逻辑；
- 未移除版权声明；
- 未用于商业分发。

## 免责

本项目仅用于互操作研究与算法学习。csTimer 是免费服务，
本项目不包含任何破解、绕过付费或侵犯作者权益的内容。
