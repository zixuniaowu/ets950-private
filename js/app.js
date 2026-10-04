/* 私人模考（加密版）— vanilla JS, no backend. Content is AES-GCM encrypted; decrypted in the browser. */
(() => {
"use strict";
const $ = (s, el = document) => el.querySelector(s);
const app = $("#app"), hud = $("#hud"), hudTimer = $("#hudTimer"), hudSection = $("#hudSection"), overlay = $("#overlay");
const DEBUG = /[?&]debug=1/.test(location.search);
const LET = "ABCD";
const PART_ZH = {1: "Part 1 照片描述", 2: "Part 2 应答问题", 3: "Part 3 会话问题", 4: "Part 4 说明文问题", 5: "Part 5 短句填空", 6: "Part 6 长文填空", 7: "Part 7 阅读理解"};
const PART_DIR_ZH = {
  1: "听 4 个描述（不印在屏幕上），选出最符合照片的一项。原书照片受版权保护，这里用英文文字描述代替。只播放一次。",
  2: "听一个问题或陈述和 3 个回答（不印在屏幕上），选出最恰当的回答。只播放一次。",
  3: "听两人或三人的对话，回答 3 个问题。问题和选项显示在屏幕上，可边听边作答。",
  4: "听一段独白（广播、留言、讲话等），回答 3 个问题。可边听边作答。"
};
const HKEY = "ets950.history.v1", NKEY = "ets950.notebook.v1", PWKEY = "ets950.pw";

/* ---------- approximate score conversion (NOT official) ---------- */
const CONV = {
  L: [[0,5],[5,40],[10,90],[15,145],[20,205],[25,265],[30,325],[35,385],[40,445],[43,480],[45,495]],
  R: [[0,5],[5,25],[10,65],[15,115],[20,170],[25,230],[30,290],[35,355],[40,420],[43,465],[45,495]]
};
function scaled(sec, raw, max) {
  if (!max) return 0;
  const t = CONV[sec]; const r = raw * 45 / max;
  for (let i = 1; i < t.length; i++) {
    if (r <= t[i][0]) {
      const [x0, y0] = t[i-1], [x1, y1] = t[i];
      const v = y0 + (y1 - y0) * (r - x0) / (x1 - x0);
      return Math.max(5, Math.min(495, Math.round(v / 5) * 5));
    }
  }
  return 495;
}

const esc = s => String(s ?? "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const fmt = sec => { sec = Math.max(0, Math.ceil(sec)); return `${String(Math.floor(sec / 60)).padStart(2, "0")}:${String(sec % 60).padStart(2, "0")}`; };
function inline(text) {
  return esc(text)
    .replace(/\*\*(.+?)\*\*/g, "<b>$1</b>")
    .replace(/\*(.+?)\*/g, "<i>$1</i>")
    .replace(/-{5,}\((\d+)\)/g, '<span class="blank">($1)</span>')
    .replace(/-{5,}/g, '<span class="blank">　　　</span>')
    .replace(/\[([1-4])\]/g, '<span class="ins">[$1]</span>')
    .replace(/\n/g, "<br>");
}
function tableHTML(rows, title) {
  return `<table class="graphic">${title ? `<caption>${esc(title)}</caption>` : ""}<tr>${rows[0].map(c => `<th>${inline(c)}</th>`).join("")}</tr>${rows.slice(1).map(r => `<tr>${r.map(c => `<td>${inline(c)}</td>`).join("")}</tr>`).join("")}</table>`;
}
function blockHTML(b) {
  switch (b.t) {
    case "title": return `<h4>${inline(b.x)}</h4>`;
    case "p": return `<p>${inline(b.x)}</p>`;
    case "meta": return `<table class="meta">${b.rows.map(r => `<tr><td>${inline(r[0])}:</td><td>${inline(r[1])}</td></tr>`).join("")}</table>`;
    case "table": return tableHTML([b.cols, ...b.rows], b.cap);
    case "msg": return `<div class="msg"><span class="who">${esc(b.who)}</span><span class="tm">${esc(b.time || "")}</span><div>${inline(b.x)}</div></div>`;
    case "list": return `<ul>${b.items.map(i => `<li>${inline(i)}</li>`).join("")}</ul>`;
    case "sign": return `<p class="sign">${inline(b.x)}</p>`;
    default: return `<p>${inline(b.x || "")}</p>`;
  }
}
const docsHTML = g => (g.intro ? `<div class="intro">${esc(g.intro)}</div>` : "") + (g.docs || []).map(d => `<div class="passage">${d.map(blockHTML).join("")}</div>`).join("");
const loadJ = (k, d) => { try { return JSON.parse(localStorage.getItem(k)) ?? d; } catch { return d; } };
const loadHist = () => loadJ(HKEY, []);
const saveHist = h => localStorage.setItem(HKEY, JSON.stringify(h.slice(-50)));
const loadNote = () => loadJ(NKEY, {});
const saveNote = n => localStorage.setItem(NKEY, JSON.stringify(n));

/* ---------- crypto ---------- */
let META = null, KEY = null, DATA = null;
const b64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
async function deriveKey(pw) {
  const base = await crypto.subtle.importKey("raw", new TextEncoder().encode(pw), "PBKDF2", false, ["deriveKey"]);
  return crypto.subtle.deriveKey({name: "PBKDF2", hash: "SHA-256", salt: b64(META.salt), iterations: META.iter}, base, {name: "AES-GCM", length: 256}, false, ["decrypt"]);
}
async function fetchBin(file, onprog) {
  const r = await fetch("data/" + file, {cache: "no-cache"});
  if (!r.ok) throw new Error("下载失败：" + file);
  if (!onprog || !r.body || !r.headers.get("content-length")) return new Uint8Array(await r.arrayBuffer());
  const total = +r.headers.get("content-length"), out = new Uint8Array(total), rd = r.body.getReader(); let n = 0;
  for (;;) { const {done, value} = await rd.read(); if (done) break; out.set(value, n); n += value.length; onprog(n / total); }
  return n === total ? out : out.slice(0, n);
}
async function decryptBin(key, bytes) {
  return crypto.subtle.decrypt({name: "AES-GCM", iv: bytes.subarray(0, 12)}, key, bytes.subarray(12));
}
async function unlock(pw) {
  if (!META) { const r = await fetch("data/meta.json", {cache: "no-cache"}); META = await r.json(); }
  const key = await deriveKey(pw);
  const bytes = await fetchBin(META.files.data.file);
  let plain;
  try { plain = await decryptBin(key, bytes); } catch { throw new Error("BADPW"); }
  DATA = JSON.parse(new TextDecoder().decode(plain)); KEY = key;
}
/* audio: one encrypted blob per Part → decrypted → one Blob URL per clip */
const AudioStore = {
  urls: {}, pending: {},
  ensure(p, onprog) {
    if (this.urls[p]) return Promise.resolve();
    if (!this.pending[p]) this.pending[p] = (async () => {
      const bytes = await fetchBin(META.files["a" + p].file, onprog);
      const ab = await decryptBin(KEY, bytes);
      this.urls[p] = DATA.audio[p].map(c => URL.createObjectURL(new Blob([new Uint8Array(ab, c.off, c.len)], {type: "audio/mpeg"})));
    })().catch(e => { delete this.pending[p]; throw e; });
    return this.pending[p];
  },
  url(a) { return this.urls[a[0]] && this.urls[a[0]][a[1]]; }
};

/* ---------- test variants ---------- */
function buildVariant(vid) {
  const v = DATA.variants[vid];
  const sections = v.sections.map(s => ({id: s.id, units: s.units.map(u => {
    const groups = [];
    for (const gid of u.groups) {
      const g = DATA.groups[gid];
      const prev = groups.at(-1);
      if (g.part === 5 && prev && prev.part === 5 && prev.questions.length < 5) prev.questions = prev.questions.concat(g.questions);
      else groups.push(g.part === 5 ? Object.assign({}, g, {questions: g.questions.slice(), _gid: gid}) : Object.assign(g, {_gid: gid}));
    }
    return {name: u.name, time: u.time, groups};
  })}));
  return {id: vid, title: DATA.title + " · " + v.name, name: v.name, count: v.count, sections};
}
function allQuestions(test) {
  const out = [];
  for (const s of test.sections) for (const u of s.units) for (const g of u.groups) for (const q of g.questions) out.push({q, g, u, s});
  return out;
}
function groupOfQ(no) { for (const g of Object.values(DATA.groups)) for (const q of g.questions) if (q.no === no) return {g, q}; return null; }

let T = null, S = null;
function setHud(on) { hud.classList.toggle("hidden", !on); $("#foot").classList.toggle("hidden", on); }
function showOverlay(html, center = true) { overlay.innerHTML = `<div class="sheet">${html}</div>`; overlay.classList.toggle("center", center); overlay.classList.remove("hidden"); }
function hideOverlay() { overlay.classList.add("hidden"); overlay.innerHTML = ""; }
overlay.addEventListener("click", e => { if (e.target === overlay && overlay.dataset.dismiss === "1") hideOverlay(); });
window.addEventListener("beforeunload", e => { if (S && !S.done) { e.preventDefault(); e.returnValue = ""; } });

/* ---------- router ---------- */
function go(hash) { if (location.hash === hash) route(); else location.hash = hash; }
window.addEventListener("hashchange", route);
$("#brand").onclick = () => { if (S && !S.done) { if (!confirm("考试进行中，确定退出吗？本次作答不会保存。")) return; abortExam(); } go("#/"); };
async function route() {
  window.scrollTo(0, 0);
  if (!DATA) return renderLock();
  const h = location.hash || "#/";
  if (S && !S.done && !h.startsWith("#/exam")) abortExam();
  if (h.startsWith("#/intro/")) return renderIntro(h.split("/")[2]);
  if (h.startsWith("#/result/")) return renderResult(h.split("/")[2]);
  if (h.startsWith("#/review/")) return renderReview(h.split("/")[2]);
  if (h.startsWith("#/notebook")) return renderNotebook();
  if (h.startsWith("#/exam")) { if (!S) return go("#/"); return; }
  renderHome();
}

/* ---------- lock screen ---------- */
function renderLock(msg = "") {
  setHud(false);
  app.innerHTML = `<div class="card lock"><h1>🔒 请输入密码</h1>
   <p class="muted">本站内容（题目、原文、解析、音频）均已加密，输入正确密码后在本机浏览器内解密。</p>
   <form id="lockForm"><input type="password" id="pw" autocomplete="current-password" placeholder="密码" required>
   <label><input type="checkbox" id="remember"> 记住（仅在本次浏览器会话中有效，关闭标签页后失效）</label>
   <div class="err" id="err">${esc(msg)}</div>
   <button class="btn block" id="unlockBtn" type="submit">解锁</button></form></div>`;
  $("#lockForm").onsubmit = async e => {
    e.preventDefault();
    const pw = $("#pw").value, btn = $("#unlockBtn");
    btn.disabled = true; btn.textContent = "正在解密…"; $("#err").textContent = "";
    try {
      await unlock(pw);
      if ($("#remember").checked) sessionStorage.setItem(PWKEY, pw); else sessionStorage.removeItem(PWKEY);
      route();
    } catch (err) {
      btn.disabled = false; btn.textContent = "解锁";
      $("#err").textContent = err.message === "BADPW" ? "密码错误，请重新输入。" : "加载失败，请检查网络后重试。";
      $("#pw").select();
    }
  };
}

/* ---------- home ---------- */
function trendSVG(hist) {
  if (hist.length < 1) return "";
  const W = 340, H = 160, pl = 34, pr = 10, pt = 14, pb = 24;
  const pts = hist.slice(-12);
  const x = i => pts.length === 1 ? (pl + W - pr) / 2 : pl + i * (W - pl - pr) / (pts.length - 1);
  const y = v => pt + (1 - (v - 10) / 980) * (H - pt - pb);
  let g = "";
  for (const v of [200, 400, 600, 800, 990]) g += `<line x1="${pl}" x2="${W - pr}" y1="${y(v)}" y2="${y(v)}" stroke="${v === 800 ? "#f59e0b" : "#e5e7eb"}" stroke-dasharray="${v === 800 ? "4 3" : ""}"/><text x="2" y="${y(v) + 4}" font-size="10" fill="#6b7280">${v}</text>`;
  const line = pts.map((p, i) => `${x(i)},${y(p.total)}`).join(" ");
  const dots = pts.map((p, i) => `<circle cx="${x(i)}" cy="${y(p.total)}" r="4" fill="#1d6fb8"/><text x="${x(i)}" y="${y(p.total) - 8}" font-size="10" text-anchor="middle" fill="#0f3d6e">${p.total}</text><text x="${x(i)}" y="${H - 6}" font-size="9" text-anchor="middle" fill="#6b7280">${new Date(p.date).getMonth() + 1}/${new Date(p.date).getDate()}</text>`).join("");
  return `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="成绩趋势">${g}<polyline points="${line}" fill="none" stroke="#1d6fb8" stroke-width="2.5"/>${dots}</svg><div class="muted">只统计听力+阅读都做的模式。橙色虚线 = 800 分（预估分）</div>`;
}
function historyCard() {
  const h = loadHist();
  if (!h.length) return `<div class="card"><h2>📈 成绩记录</h2><p class="muted">还没有记录。完成一次模拟考试后，这里会显示预估分。记录只保存在本机浏览器里。</p></div>`;
  const rows = h.slice().reverse().slice(0, 15).map(a => `<tr><td>${new Date(a.date).toLocaleDateString("zh-CN")}</td><td>${esc(a.modeName)}</td><td>${a.lN ? `${a.lScore}<br><small>${a.lRaw}/${a.lN}</small>` : "—"}</td><td>${a.rN ? `${a.rScore}<br><small>${a.rRaw}/${a.rN}</small>` : "—"}</td><td><b>${a.lN && a.rN ? a.total : "—"}</b></td><td><a href="#/result/${a.id}">详情</a></td></tr>`).join("");
  return `<div class="card trend"><h2>📈 成绩记录</h2>${trendSVG(h.filter(a => a.lN && a.rN))}
  <table class="hist"><tr><th>日期</th><th>模式</th><th>听力</th><th>阅读</th><th>总分</th><th></th></tr>${rows}</table>
  <p class="muted">分数为预估值。记录保存在本机浏览器（localStorage）。<a href="#" id="clearHist">清除记录</a></p></div>`;
}
function renderHome() {
  setHud(false); S = null;
  const nb = Object.values(loadNote()).filter(x => !x.ok).length;
  const V = DATA.variants;
  app.innerHTML = `
  <div class="card"><h1>${esc(DATA.title)}</h1>
  <p>全真 TOEIC L&amp;R 格式：听力 100 题（约 48 分钟，音频连续播放、只播一次），阅读 100 题（75 分钟）。听力音频为语音合成（TTS）重新朗读。</p></div>
  <div class="card modes"><h2>📝 选择模式</h2>
  ${Object.keys(V).map(k => `<div class="card"><h3 style="margin-top:0">${esc(V[k].name)}</h3><p class="muted">${esc(V[k].desc)}</p><a class="btn block" href="#/intro/${k}">开始</a></div>`).join("")}</div>
  <div class="card"><h2>📒 错题本</h2><p>当前错题 <b>${nb}</b> 题（保存在本机浏览器）。</p><a class="btn ghost block" href="#/notebook">打开错题本</a></div>
  ${historyCard()}
  <div class="card"><details><summary>说明</summary><ul class="rules">${DATA.notes.map(n => `<li>${esc(n)}</li>`).join("")}</ul></details>
  <p><a href="#" id="lockNow">🔒 锁定（清除本次会话中记住的密码）</a></p></div>`;
  const c = $("#clearHist"); if (c) c.onclick = e => { e.preventDefault(); if (confirm("确定清除所有成绩记录吗？")) { localStorage.removeItem(HKEY); renderHome(); } };
  $("#lockNow").onclick = e => { e.preventDefault(); sessionStorage.removeItem(PWKEY); location.hash = "#/"; location.reload(); };
}

/* ---------- intro ---------- */
function renderIntro(vid) {
  setHud(false);
  if (!DATA.variants[vid]) return go("#/");
  const test = buildVariant(vid);
  const L = test.sections.find(s => s.id === "L"), R = test.sections.find(s => s.id === "R");
  const lQ = L ? L.units.reduce((a, u) => a + u.groups.reduce((b, g) => b + g.questions.length, 0), 0) : 0;
  const lMin = L ? Math.round(L.units.flatMap(u => u.groups).reduce((a, g) => a + g.duration, 0) / 60) : 0;
  app.innerHTML = `<div class="card"><h1>${esc(test.name)} · 考前说明</h1>
  ${L ? `<h3>🎧 听力（约 ${lMin} 分钟 · ${lQ} 题）</h3>
  <ul class="rules">
   <li>每段音频<b>只自动播放一次</b>，不能暂停、不能重听、不能回到前面的题。</li>
   <li>音频播放时就可以作答；一段音频结束后自动进入下一题。</li>
   <li>Part 1、Part 2 的选项<b>不显示文字</b>，只能靠听；Part 1 的照片以英文文字描述代替。Part 3、Part 4 的问题和选项显示在屏幕上。</li>
   <li>开始前会先下载并解密音频（约 17 MB），请在网络良好时开始。</li>
  </ul>` : ""}
  ${R ? `<h3>📖 阅读（${R.units.map(u => `${u.name} ${Math.round(u.time / 60)} 分钟`).join(" + ")}）</h3>
  <ul class="rules">
   <li>${R.units.length > 1 ? "每个 UNIT 分别计时；进入下一个 UNIT 后不能返回。" : "共 75 分钟，Part 5–7 可自由跳题。"}</li>
   <li>可修改答案、用 🚩 标记待检查的题，用“题目一览”跳转。</li>
   <li>时间到会自动${R.units.length > 1 ? "进入下一部分 / " : ""}交卷。</li>
  </ul>` : ""}
  <h3>📱 准备</h3>
  <ul class="rules">
   <li>请戴上耳机。iPhone 请关闭静音模式、调高音量；中途切到别的 App 可能会让音频暂停。</li>
   <li>考试中途退出不会保存成绩。</li>
  </ul>
  <div class="row" style="margin-top:14px"><a class="btn ghost" href="#/">返回</a><button class="btn" id="startBtn">进入考试</button></div></div>`;
  $("#startBtn").onclick = () => startExam(test);
}

let wakeLock = null;
async function requestWakeLock() {
  try { if ("wakeLock" in navigator && !wakeLock) { wakeLock = await navigator.wakeLock.request("screen"); wakeLock.addEventListener("release", () => { wakeLock = null; }); } } catch {}
}
document.addEventListener("visibilitychange", () => { if (!document.hidden && S && !S.done) requestWakeLock(); });

/* ---------- audio engine (Web Audio, unlocked by one tap for iOS) ---------- */
const AudioEng = {
  ctx: null, src: null, buffers: {}, startAt: 0, html: null,
  unlock() {
    try { if (navigator.audioSession) navigator.audioSession.type = "playback"; } catch {}
    requestWakeLock();
    const AC = window.AudioContext || window.webkitAudioContext;
    if (AC && !this.ctx) {
      this.ctx = new AC();
      const b = this.ctx.createBuffer(1, 1, 22050), s = this.ctx.createBufferSource();
      s.buffer = b; s.connect(this.ctx.destination); s.start(0);
    }
    if (this.ctx && this.ctx.state !== "running") this.ctx.resume();
    if (!this.ctx) { this.html = new Audio(); this.html.play().catch(() => {}); }
  },
  load(url) {
    if (!this.ctx || !url) return null;
    if (!this.buffers[url]) {
      this.buffers[url] = fetch(url).then(r => r.arrayBuffer()).then(ab => new Promise((res, rej) => this.ctx.decodeAudioData(ab, res, rej)));
      this.buffers[url].catch(() => delete this.buffers[url]);
    }
    return this.buffers[url];
  },
  prune(keep) { for (const k of Object.keys(this.buffers)) if (!keep.includes(k)) delete this.buffers[k]; },
  async play(url, onended) {
    this.stop();
    if (this.ctx) {
      const buf = await this.load(url);
      const s = this.ctx.createBufferSource(); s.buffer = buf; s.connect(this.ctx.destination);
      s.onended = () => { if (this.src === s) { this.src = null; onended(); } };
      this.src = s; this.startAt = this.ctx.currentTime; s.start(0);
    } else {
      const a = this.html || new Audio(); this.html = a; a.src = url; a.onended = onended; await a.play();
      this.startAt = performance.now() / 1000;
    }
  },
  elapsed() { return this.ctx ? this.ctx.currentTime - this.startAt : (this.html ? this.html.currentTime : 0); },
  stop() { if (this.src) { const s = this.src; this.src = null; try { s.onended = null; s.stop(); } catch {} } if (this.html) { this.html.onended = null; this.html.pause(); } },
  skip() { if (this.src) { const s = this.src; try { s.stop(); } catch {} } else if (this.html) { this.html.onended && this.html.onended(); } }
};
document.addEventListener("visibilitychange", () => {
  if (!document.hidden && S && S.phase === "L" && AudioEng.ctx && AudioEng.ctx.state !== "running") {
    showOverlay(`<div class="gate"><div class="big">⏸</div><p>音频因切换 App 被系统暂停了。</p><button class="btn block" id="resumeBtn">点击继续</button></div>`);
    $("#resumeBtn").onclick = () => { AudioEng.ctx.resume(); hideOverlay(); };
  }
});

/* ---------- exam ---------- */
function startExam(test) {
  T = test;
  S = {vid: test.id, answers: {}, flags: {}, phase: "L", li: 0, done: false, started: Date.now(), tick: null};
  const L = test.sections.find(s => s.id === "L");
  S.lgroups = L ? L.units.flatMap(u => u.groups.map(g => Object.assign(g, {_unit: u}))) : [];
  S.lTotal = S.lgroups.reduce((a, g) => a + g.duration, 0);
  S.lCount = S.lgroups.reduce((a, g) => a + g.questions.length, 0);
  const R = test.sections.find(s => s.id === "R");
  S.runits = R ? R.units : [];
  setHud(true);
  go("#/exam");
  if (!L) { S.tick = setInterval(tick, 250); requestWakeLock(); return startReading(); }
  hudSection.textContent = "听力 Listening";
  hudTimer.textContent = fmt(S.lTotal);
  const parts = [...new Set(S.lgroups.map(g => g.audio[0]))];
  app.innerHTML = `<div class="card gate"><div class="big">🎧</div><h2>听力部分即将开始</h2>
   <p class="muted">共 ${S.lCount} 题，约 ${Math.round(S.lTotal / 60)} 分钟。点击下方按钮后音频会自动连续播放，不能暂停。</p>
   <p id="prep">正在下载并解密音频… <b id="prepPct">0%</b></p>
   <button class="btn block" id="gateBtn" disabled>请稍候…</button></div>`;
  const sizes = parts.map(p => META.files["a" + p].size), tot = sizes.reduce((a, b) => a + b, 0), prog = parts.map(() => 0);
  const upd = () => { const e = $("#prepPct"); if (e) e.textContent = Math.round(prog.reduce((a, x, i) => a + x * sizes[i], 0) / tot * 100) + "%"; };
  (async () => {
    try {
      for (let i = 0; i < parts.length; i++) await AudioStore.ensure(parts[i], f => { prog[i] = f; upd(); });
      if (!S || S.phase !== "L") return;
      $("#prep").textContent = "✅ 音频已准备好";
      const b = $("#gateBtn"); b.disabled = false; b.textContent = "点击开始听力";
      b.onclick = () => { AudioEng.unlock(); playGroup(0); S.tick = setInterval(tick, 250); };
    } catch (e) {
      $("#prep").innerHTML = `<span style="color:#dc2626">音频加载失败，请检查网络后返回重试。</span>`;
    }
  })();
}
function releaseWake() { if (wakeLock) { wakeLock.release().catch(() => {}); wakeLock = null; } hudTimer.classList.remove("warn"); }
function abortExam() { releaseWake(); if (!S) return; AudioEng.stop(); AudioEng.prune([]); clearInterval(S.tick); S = null; hideOverlay(); setHud(false); }

function tick() {
  if (!S || S.done) return;
  if (S.phase === "L") {
    const g = S.lgroups[S.li]; if (!g) return;
    const rest = S.lgroups.slice(S.li + 1).reduce((a, x) => a + x.duration, 0);
    const left = Math.max(0, g.duration - AudioEng.elapsed()) + rest;
    hudTimer.textContent = fmt(left);
  } else if (S.phase === "R") {
    const left = (S.rDeadline - Date.now()) / 1000;
    hudTimer.textContent = fmt(left);
    hudTimer.classList.toggle("warn", left < 300);
    if (left <= 0) {
      if (S.ru < S.runits.length - 1) { alert(`${S.runits[S.ru].name} 时间到，自动进入下一部分。`); startReadingUnit(S.ru + 1); }
      else { alert("时间到，自动交卷。"); submit(); }
    }
  }
}

function optsHTML(q, showText, nopt) {
  const n = nopt || q.options.length;
  const cls = showText ? "opts" : `opts letters${n === 3 ? " three" : ""}`;
  return `<div class="${cls}">${Array.from({length: n}, (_, i) => `<button class="opt${S.answers[q.no] === i ? " sel" : ""}" data-q="${q.no}" data-i="${i}"><b>${LET[i]}</b>${showText ? `<span>${inline(q.options[i])}</span>` : ""}</button>`).join("")}</div>`;
}
function bindOpts(root) {
  root.querySelectorAll(".opt").forEach(b => b.onclick = () => {
    const no = +b.dataset.q, i = +b.dataset.i;
    S.answers[no] = i;
    root.querySelectorAll(`.opt[data-q="${no}"]`).forEach(x => x.classList.toggle("sel", +x.dataset.i === i));
    if (S.phase === "R") updatePaletteState();
  });
}
const photoHTML = g => `<div class="photo-ph"><div class="lbl">📷 照片（文字描述代替原图）</div><p>${esc(g.photo)}</p></div>`;
const gfxHTML = g => g.graphic ? tableHTML(g.graphic.rows, g.graphic.title) : "";

async function playGroup(i) {
  S.li = i;
  window.scrollTo(0, 0);
  const g = S.lgroups[i];
  if (!g) { AudioEng.prune([]); return S.runits.length ? startReading() : submit(); }
  const done = S.lgroups.slice(0, i).reduce((a, x) => a + x.questions.length, 0);
  const firstOfPart = i === 0 || S.lgroups[i - 1].part !== g.part || S.lgroups[i - 1]._unit !== g._unit;
  hudSection.textContent = `听力 · ${g._unit.name}`;
  let body = "";
  const q0 = g.questions[0];
  if (g.part === 1) body = `${photoHTML(g)}<div class="qblock"><div class="qtext"><span class="qno">${q0.no}.</span>选出最符合照片的描述</div>${optsHTML(q0, false, 4)}</div>`;
  else if (g.part === 2) body = `<div class="qblock"><div class="qtext"><span class="qno">${q0.no}.</span>选出最恰当的回答</div>${optsHTML(q0, false, 3)}</div>`;
  else body = gfxHTML(g) + g.questions.map(q => `<div class="qblock"><div class="qtext"><span class="qno">${q.no}.</span>${esc(q.q)}</div>${optsHTML(q, true)}</div>`).join("");
  app.innerHTML = `<div class="progress"><i style="width:${done / S.lCount * 100}%"></i></div>
   <div class="partbar"><span>${PART_ZH[g.part]}</span><span>${q0.no}${g.questions.length > 1 ? "–" + g.questions.at(-1).no : ""}</span></div>
   ${firstOfPart ? `<div class="dirnote">${PART_DIR_ZH[g.part]}</div>` : ""}
   <div class="card"><div class="listenstate" id="ls"><span class="wave"><i></i><i></i><i></i><i></i></span><span>正在播放…（只播放一次）</span></div>${body}</div>
   ${DEBUG ? `<button class="btn ghost small" id="dbgSkip">[debug] 跳过本段音频</button>` : ""}`;
  bindOpts(app);
  if (DEBUG) $("#dbgSkip").onclick = () => AudioEng.skip();
  const url = AudioStore.url(g.audio), next = S.lgroups[i + 1] ? AudioStore.url(S.lgroups[i + 1].audio) : null;
  AudioEng.prune([url, next]);
  if (next) AudioEng.load(next);
  try {
    await AudioEng.play(url, () => { if (S && S.phase === "L" && S.li === i) playGroup(i + 1); });
  } catch (e) {
    const ls = $("#ls"); if (!ls) return;
    ls.innerHTML = `<span style="color:#dc2626">音频播放失败。</span> <button class="btn small" id="retryA">重试</button>`;
    $("#retryA").onclick = () => playGroup(i);
  }
}

function startReading() {
  AudioEng.stop();
  S.phase = "R-gate";
  hudSection.textContent = "阅读 Reading";
  hudTimer.textContent = fmt(S.runits[0].time);
  app.innerHTML = `<div class="card gate"><div class="big">📖</div><h2>${S.lgroups.length ? "听力结束，进入阅读部分" : "阅读部分"}</h2>
   <p>${S.runits.map(u => `${u.name}：${Math.round(u.time / 60)} 分钟 · ${u.groups.reduce((a, g) => a + g.questions.length, 0)} 题`).join("<br>")}</p><p class="muted">点击开始后计时立即开始。</p>
   <button class="btn block" id="rStart">开始阅读</button></div>`;
  $("#rStart").onclick = () => { requestWakeLock(); if (!S.tick) S.tick = setInterval(tick, 250); startReadingUnit(0); };
}
function startReadingUnit(ru) {
  hideOverlay();
  S.phase = "R"; S.ru = ru; S.rg = 0;
  const u = S.runits[ru];
  S.rDeadline = Date.now() + u.time * 1000; hudTimer.textContent = fmt(u.time);
  hudSection.textContent = `阅读 · ${u.name}`;
  renderReadingGroup();
}
const lastUnit = () => S.ru === S.runits.length - 1;
function renderReadingGroup(scrollToNo) {
  const u = S.runits[S.ru], g = u.groups[S.rg];
  const last = S.rg === u.groups.length - 1;
  const qs = g.questions.map(q => `<div class="qblock" id="q${q.no}"><div class="qhead"><div class="qtext"><span class="qno">${q.no}.</span>${q.q ? inline(q.q) : `为空格 (${q.no}) 选择最佳选项`}</div>
     <button class="flagbtn${S.flags[q.no] ? " on" : ""}" data-flag="${q.no}">🚩 ${S.flags[q.no] ? "已标记" : "标记"}</button></div>${optsHTML(q, true)}</div>`).join("");
  const all = u.groups.flatMap(x => x.questions);
  const answered = all.filter(q => S.answers[q.no] !== undefined).length;
  app.innerHTML = `<div class="partbar"><span>${PART_ZH[g.part]}</span><span>已答 <b id="ansCount">${answered}</b> / ${all.length}</span></div>
   ${g.part === 5 && (S.rg === 0 || u.groups[S.rg - 1].part !== 5) ? `<div class="dirnote">选出最适合填入句子空格的选项。</div>` : ""}
   ${g.part === 6 ? `<div class="dirnote">阅读文章，为每个空格选出最佳选项（包括单词、短语或句子）。</div>` : ""}
   ${g.part === 7 ? `<div class="dirnote">阅读下面的文章并回答问题。</div>` : ""}
   <div class="card">${docsHTML(g)}${qs}</div>
   <div class="navbar">
    <button class="btn ghost" id="prevG" ${S.rg === 0 ? "disabled" : ""}>‹ 上一页</button>
    <button class="btn ghost" id="palBtn">题目一览</button>
    ${last ? `<button class="btn ${lastUnit() ? "warn" : ""}" id="endUnit">${lastUnit() ? "交卷" : `完成 ${esc(u.name)}`}</button>` : `<button class="btn" id="nextG">下一页 ›</button>`}
   </div>`;
  bindOpts(app);
  app.querySelectorAll("[data-flag]").forEach(b => b.onclick = () => {
    const no = +b.dataset.flag; S.flags[no] = !S.flags[no];
    b.classList.toggle("on", S.flags[no]); b.textContent = `🚩 ${S.flags[no] ? "已标记" : "标记"}`;
  });
  $("#prevG").onclick = () => { S.rg--; renderReadingGroup(); };
  if ($("#nextG")) $("#nextG").onclick = () => { S.rg++; renderReadingGroup(); };
  if ($("#endUnit")) $("#endUnit").onclick = () => openPalette();
  $("#palBtn").onclick = () => openPalette();
  if (scrollToNo) { const el = $("#q" + scrollToNo); if (el) el.scrollIntoView({block: "center"}); } else window.scrollTo(0, 0);
}
function updatePaletteState() {
  const u = S.runits[S.ru]; const c = $("#ansCount");
  if (c) c.textContent = u.groups.flatMap(x => x.questions).filter(q => S.answers[q.no] !== undefined).length;
}
function openPalette() {
  const u = S.runits[S.ru];
  const items = u.groups.flatMap((g, gi) => g.questions.map(q => ({q, gi})));
  const un = items.filter(x => S.answers[x.q.no] === undefined).length;
  const fl = items.filter(x => S.flags[x.q.no]).length;
  const endTxt = lastUnit() ? "交卷" : `进入 ${S.runits[S.ru + 1].name}`;
  overlay.dataset.dismiss = "1";
  showOverlay(`<h2>${esc(u.name)} 题目一览</h2>
   <p class="muted">蓝色 = 已作答，橙点 = 已标记。点击题号跳转。</p>
   <div class="palette">${items.map(x => `<button class="pal${S.answers[x.q.no] !== undefined ? " done" : ""}${S.flags[x.q.no] ? " flag" : ""}${x.gi === S.rg ? " cur" : ""}" data-gi="${x.gi}" data-no="${x.q.no}">${x.q.no}</button>`).join("")}</div>
   <p>未作答：<b>${un}</b> 题 · 已标记：<b>${fl}</b> 题</p>
   <p class="muted">${lastUnit() ? "交卷后不能再修改答案。" : "进入下一部分后不能再回来。"}</p>
   <div class="row"><button class="btn ghost" id="palClose">继续作答</button>
   <button class="btn ${lastUnit() ? "warn" : ""}" id="palEnd">${endTxt}</button></div>`, false);
  overlay.querySelectorAll(".pal").forEach(b => b.onclick = () => { hideOverlay(); S.rg = +b.dataset.gi; renderReadingGroup(+b.dataset.no); });
  $("#palClose").onclick = hideOverlay;
  $("#palEnd").onclick = () => {
    if (un && !confirm(`还有 ${un} 题未作答，确定${endTxt}吗？`)) return;
    hideOverlay();
    if (!lastUnit()) startReadingUnit(S.ru + 1); else submit();
  };
}

function submit() {
  if (!S || S.done) return;
  S.done = true; clearInterval(S.tick); AudioEng.stop(); AudioEng.prune([]); hideOverlay(); releaseWake();
  const qs = allQuestions(T);
  const parts = {}; let l = 0, r = 0, lN = 0, rN = 0;
  const nb = loadNote(), now = new Date().toISOString();
  for (const {q, g, s} of qs) {
    const ok = S.answers[q.no] === q.answer;
    parts[g.part] = parts[g.part] || {c: 0, n: 0}; parts[g.part].n++; if (ok) parts[g.part].c++;
    if (s.id === "L") { lN++; if (ok) l++; } else { rN++; if (ok) r++; }
    if (!ok) { const e = nb[q.no] || {n: 0}; e.n++; e.last = now; e.ok = false; nb[q.no] = e; }
  }
  saveNote(nb);
  const lScore = scaled("L", l, lN), rScore = scaled("R", r, rN);
  const att = {id: String(Date.now()), vid: T.id, modeName: T.name, date: now,
    lRaw: l, lN, rRaw: r, rN, lScore, rScore, total: lScore + rScore, parts, answers: S.answers, flags: S.flags,
    minutes: Math.round((Date.now() - S.started) / 60000)};
  const h = loadHist(); h.push(att); saveHist(h);
  S = null; setHud(false);
  go("#/result/" + att.id);
}

/* ---------- results ---------- */
function barColor(p) { return p >= 0.8 ? "#16a34a" : p >= 0.6 ? "#1d6fb8" : p >= 0.4 ? "#f59e0b" : "#dc2626"; }
function renderResult(aid) {
  setHud(false);
  const a = loadHist().find(x => x.id === aid);
  if (!a) return renderHome();
  const parts = Object.keys(a.parts).sort().map(p => {
    const {c, n} = a.parts[p]; const pct = c / n;
    return `<div class="bar"><span>${PART_ZH[p]}</span><span class="track"><i style="width:${pct * 100}%;background:${barColor(pct)}"></i></span><span>${c}/${n} · ${Math.round(pct * 100)}%</span></div>`;
  }).join("");
  const weakest = Object.keys(a.parts).sort((x, y) => a.parts[x].c / a.parts[x].n - a.parts[y].c / a.parts[y].n)[0];
  const both = a.lN && a.rN;
  app.innerHTML = `<div class="card"><h1>考试结果</h1><p class="muted">${esc(a.modeName)} · ${new Date(a.date).toLocaleString("zh-CN")} · 用时约 ${a.minutes} 分钟</p>
   <div class="scorebig">
    ${a.lN ? `<div><small>听力 Listening</small><div class="n">${a.lScore}</div><small>答对 ${a.lRaw}/${a.lN}</small></div>` : ""}
    ${a.rN ? `<div><small>阅读 Reading</small><div class="n">${a.rScore}</div><small>答对 ${a.rRaw}/${a.rN}</small></div>` : ""}
    ${both ? `<div class="total"><small>总分（预估）</small><div class="n">${a.total}</div><small>${a.total >= 950 ? "950+ ✅" : `距 950 还差 ${950 - a.total}`}</small></div>` : ""}
   </div>
   <div class="estimate">⚠️ 以上为<b>预估分</b>，根据答对题数用近似换算表推算，<b>不是官方分数</b>。</div></div>
  <div class="card bars"><h2>📊 各 Part 正确率</h2>${parts}
   <p class="muted">最需要加强：<b>${PART_ZH[weakest]}</b></p></div>
  <div class="card"><div class="row"><a class="btn" href="#/review/${a.id}">查看解析</a><a class="btn ghost" href="#/intro/${a.vid}">再考一次</a></div>
   <div class="row" style="margin-top:10px"><a class="btn ghost" href="#/notebook">错题本</a><a class="btn ghost" href="#/">返回首页</a></div></div>
  ${historyCard()}`;
  const c = $("#clearHist"); if (c) c.onclick = e => { e.preventDefault(); if (confirm("确定清除所有成绩记录吗？")) { localStorage.removeItem(HKEY); go("#/"); } };
}

/* ---------- review / notebook shared ---------- */
function scriptHTML(g) { return g.script.map(x => `<p><span class="spk">${esc(x.spk)}:</span> ${esc(x.text)}</p>`).join(""); }
function ctxHTML(g, aid) {
  if (g.sec === "L") return `${g.part === 1 ? photoHTML(g) : ""}${gfxHTML(g)}
    <details ${g.part <= 2 ? "open" : ""}><summary>听力原文 & 重听音频</summary><div class="aud" data-p="${g.audio[0]}" data-i="${g.audio[1]}"><button class="btn small ghost loadA">▶ 加载音频</button></div><div class="script">${scriptHTML(g)}</div></details>`;
  return `<details><summary>查看文章（${g.questions[0].no}${g.questions.length > 1 ? "–" + g.questions.at(-1).no : ""}）</summary>${docsHTML(g)}</details>`;
}
function bindAudioButtons(root) {
  root.querySelectorAll(".aud").forEach(d => {
    const b = d.querySelector(".loadA"); if (!b) return;
    b.onclick = async () => {
      const p = +d.dataset.p, i = +d.dataset.i;
      b.disabled = true; b.textContent = "正在解密音频…";
      try { await AudioStore.ensure(p); d.innerHTML = `<audio controls preload="auto" src="${AudioStore.url([p, i])}"></audio>`; d.querySelector("audio").play().catch(() => {}); }
      catch { b.disabled = false; b.textContent = "加载失败，点击重试"; }
    };
  });
}
function qCard(q, g, mine, extraTop = "", extraBottom = "") {
  const ok = mine === q.answer;
  const opts = q.options.map((o, i) => `<div class="opt${i === q.answer ? " correct" : ""}${i === mine && !ok ? " wrong" : ""}"><b>${LET[i]}</b><span>${o === null ? "（听力选项，见原文）" : inline(o)}</span></div>`).join("");
  return `<div class="qtext"><span class="qno">${q.no}.</span>${q.q ? inline(q.q) : (g.part === 6 ? "（长文填空）" : g.part === 1 ? "选出最符合照片的描述" : g.part === 2 ? "选出最恰当的回答" : "")}</div>
    ${extraTop}<div class="opts">${opts}</div>${extraBottom}
    <div class="exp">💡 ${esc(q.exp)}${q.vocab ? `<div class="vocab">📚 词汇：${esc(q.vocab)}</div>` : ""}${g.sec === "R" ? `<div class="srcnote">（阅读解析由 AI 助手编写，非原书解析）</div>` : ""}</div>`;
}
function renderReview(aid, filter = "all") {
  setHud(false);
  const a = loadHist().find(x => x.id === aid);
  if (!a || !DATA.variants[a.vid]) return renderHome();
  const test = buildVariant(a.vid);
  const qs = allQuestions(test);
  const wrong = qs.filter(x => a.answers[x.q.no] !== x.q.answer).length;
  const flagged = qs.filter(x => a.flags && a.flags[x.q.no]).length;
  let html = `<div class="card"><h1>解析</h1><div class="tabs">
    <button data-f="all" class="${filter === "all" ? "on" : ""}">全部 ${qs.length}</button>
    <button data-f="wrong" class="${filter === "wrong" ? "on" : ""}">错题 ${wrong}</button>
    <button data-f="flag" class="${filter === "flag" ? "on" : ""}">已标记 ${flagged}</button>
    ${a.lN ? `<button data-f="L" class="${filter === "L" ? "on" : ""}">听力</button>` : ""}
    ${a.rN ? `<button data-f="R" class="${filter === "R" ? "on" : ""}">阅读</button>` : ""}</div>
    <a href="#/result/${a.id}" class="muted">‹ 返回结果</a></div>`;
  let lastG = null;
  for (const {q, g, s} of qs) {
    const mine = a.answers[q.no], ok = mine === q.answer;
    if (filter === "wrong" && ok) continue;
    if (filter === "flag" && !(a.flags && a.flags[q.no])) continue;
    if ((filter === "L" || filter === "R") && s.id !== filter) continue;
    let ctx = "";
    if (g !== lastG) { ctx = (g.part === 5 && g.sec === "R") ? "" : ctxHTML(g); lastG = g; }
    html += `<div class="card rv${ok ? "" : " ng"}"><div class="qhead"><span class="tag">${PART_ZH[g.part]}</span>
      <span class="status ${ok ? "ok" : "ng"}">${ok ? "✓ 正确" : mine === undefined ? "✗ 未作答" : "✗ 错误"}</span></div>
      ${ctx}${qCard(q, g, mine, "", `<p class="muted">你的答案：<b>${mine === undefined ? "未作答" : LET[mine]}</b> · 正确答案：<b>${LET[q.answer]}</b></p>`)}</div>`;
  }
  app.innerHTML = html;
  bindAudioButtons(app);
  app.querySelectorAll(".tabs button").forEach(b => b.onclick = () => renderReview(aid, b.dataset.f));
}
function renderNotebook(filter = "all") {
  setHud(false);
  const nb = loadNote();
  const items = Object.keys(nb).map(Number).filter(n => !nb[n].ok).sort((x, y) => x - y)
    .filter(n => filter === "all" || (filter === "L" ? n <= 100 : n > 100));
  const all = Object.keys(nb).filter(n => !nb[n].ok);
  let html = `<div class="card"><h1>📒 错题本</h1>
   <p class="muted">考试中答错或未作答的题会自动加入（只保存题号和次数，在本机 localStorage）。复习后点“已掌握”移出。</p>
   <div class="tabs"><button data-f="all" class="${filter === "all" ? "on" : ""}">全部 ${all.length}</button>
   <button data-f="L" class="${filter === "L" ? "on" : ""}">听力 ${all.filter(n => +n <= 100).length}</button>
   <button data-f="R" class="${filter === "R" ? "on" : ""}">阅读 ${all.filter(n => +n > 100).length}</button></div>
   <div class="row"><a class="btn ghost small" href="#/">‹ 首页</a>${all.length ? `<button class="btn ghost small" id="nbClear">清空错题本</button>` : ""}</div></div>`;
  if (!items.length) html += `<div class="card"><p class="muted">这里还没有错题。</p></div>`;
  for (const n of items) {
    const f = groupOfQ(n); if (!f) continue;
    const {g, q} = f;
    const ctx = (g.part === 5) ? "" : ctxHTML(g);
    html += `<div class="card rv ng"><div class="qhead"><span class="tag">${PART_ZH[g.part]}</span><span class="status ng">错 ${nb[n].n} 次</span></div>
      ${ctx}${qCard(q, g, undefined, "", `<p class="muted">正确答案：<b>${LET[q.answer]}</b> · 最近一次：${new Date(nb[n].last).toLocaleDateString("zh-CN")}</p>`)}
      <button class="btn small" data-ok="${n}">✓ 已掌握</button></div>`;
  }
  app.innerHTML = html;
  bindAudioButtons(app);
  app.querySelectorAll(".tabs button").forEach(b => b.onclick = () => renderNotebook(b.dataset.f));
  app.querySelectorAll("[data-ok]").forEach(b => b.onclick = () => { const x = loadNote(); x[b.dataset.ok].ok = true; saveNote(x); b.closest(".card").remove(); });
  const c = $("#nbClear"); if (c) c.onclick = () => { if (confirm("确定清空错题本吗？")) { localStorage.removeItem(NKEY); renderNotebook(filter); } };
}

/* ---------- boot ---------- */
(async () => {
  const pw = sessionStorage.getItem(PWKEY);
  if (pw) {
    app.innerHTML = `<div class="card gate"><p>正在解密…</p></div>`;
    try { await unlock(pw); } catch (e) { sessionStorage.removeItem(PWKEY); return renderLock(e.message === "BADPW" ? "已保存的密码无效，请重新输入。" : ""); }
  }
  route();
})();
})();
