/* 私人模考（加密版）— vanilla JS, no backend. Content is AES-GCM encrypted; decrypted in the browser. */
(() => {
"use strict";
const $ = (s, el = document) => el.querySelector(s);
const app = $("#app"), hud = $("#hud"), hudTimer = $("#hudTimer"), hudSection = $("#hudSection"), overlay = $("#overlay");
const DEBUG = /[?&]debug=1/.test(location.search);
const FAST = /[?&]fast=1/.test(location.search);  // smoke-test only: shorten timers
const LET = "ABCD";
const t = (k, ...a) => window.I18N.t(k, ...a), pick = (o, k) => window.I18N.pick(o, k), loc = () => window.I18N.locale();
const PART_ZH = new Proxy({}, {get: (_, p) => t("part" + String(p))});      // localized part names
const PART_DIR_ZH = new Proxy({}, {get: (_, p) => t("pdir" + String(p))});  // localized Part 1–4 directions
const dTitle = d => pick(d, "title");                                          // localized test title
const vName = v => pick(v, "name"), vDesc = v => pick(v, "desc");
function bindLang(rerender) {
  document.querySelectorAll(".langsw [data-lang]").forEach(b => b.onclick = e => { e.preventDefault(); if (b.dataset.lang !== window.I18N.lang) { window.I18N.set(b.dataset.lang); rerender(); } });
}
const HKEY = "ets950.history.v1", NKEY = "ets950.notebook.v1", PWKEY = "ets950.pw", PWMKEY = "ets950.pwMonth", TKEY = "ets950.tid", VKEY = "ets950.vol";
const SHELL = window.examShell || null;   // set by the Electron preload (desktop exam app)
let SIM = !!SHELL;                          // IP-online style full-screen simulation mode

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
const fmtHMS = sec => { sec = Math.max(0, Math.ceil(sec)); const h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), s = sec % 60; return `${String(h).padStart(2, "0")}:${String(m).padStart(2, "0")}:${String(s).padStart(2, "0")}`; };
const ANSWER_GAP = {1: 5, 2: 5, 3: 8, 4: 8};   // seconds after each listening clip (matches existing TOEIC gaps)
const AKEY = "ets950.ansTimer";                 // optional per-question remaining-seconds (default off)
const showAnsTimer = () => localStorage.getItem(AKEY) === "1";
const setAnsTimer = on => localStorage.setItem(AKEY, on ? "1" : "0");
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
let META = null, KEY = null, DATA = null, TESTS = {}, TID = null, UNLOCK_YM = null;
const b64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
/** Asia/Tokyo calendar parts: YYYY-MM for session expiry; MM for password wrap. */
function tokyoParts(d = new Date()) {
  const parts = new Intl.DateTimeFormat("en-CA", { timeZone: "Asia/Tokyo", year: "numeric", month: "2-digit" }).formatToParts(d);
  const y = parts.find(p => p.type === "year").value, m = parts.find(p => p.type === "month").value;
  return { ym: y + "-" + m, mm: m };
}
function tokyoYM(d) { return tokyoParts(d).ym; }
function tokyoMM(d) { return tokyoParts(d).mm; }
function clearSavedPw() { sessionStorage.removeItem(PWKEY); sessionStorage.removeItem(PWMKEY); }
function savePwSession(pw, ym) { sessionStorage.setItem(PWKEY, pw); sessionStorage.setItem(PWMKEY, ym); }
function loadSavedPw() {
  const pw = sessionStorage.getItem(PWKEY), ym = sessionStorage.getItem(PWMKEY), cur = tokyoYM();
  if (!pw || !ym || ym !== cur) { clearSavedPw(); return null; }
  return pw;
}
async function fetchBin(file, onprog) {
  const r = await fetch("data/" + file, {cache: "no-cache"});
  if (!r.ok) throw new Error(t("dlFail", file));
  if (!onprog || !r.body || !r.headers.get("content-length")) return new Uint8Array(await r.arrayBuffer());
  const total = +r.headers.get("content-length"), out = new Uint8Array(total), rd = r.body.getReader(); let n = 0;
  for (;;) { const {done, value} = await rd.read(); if (done) break; out.set(value, n); n += value.length; onprog(n / total); }
  return n === total ? out : out.slice(0, n);
}
async function decryptBin(key, bytes) {
  return crypto.subtle.decrypt({name: "AES-GCM", iv: bytes.subarray(0, 12)}, key, bytes.subarray(12));
}
async function unwrapDataKey(pw, mm) {
  const w = META.wraps && META.wraps[mm];
  if (!w) throw new Error("BADPW");
  const salt = b64(w.salt), wrap = b64(w.wrap);
  const base = await crypto.subtle.importKey("raw", new TextEncoder().encode(pw), "PBKDF2", false, ["deriveKey"]);
  const wk = await crypto.subtle.deriveKey(
    {name: "PBKDF2", hash: "SHA-256", salt, iterations: META.iter},
    base, {name: "AES-GCM", length: 256}, false, ["decrypt"]
  );
  let raw;
  try { raw = await crypto.subtle.decrypt({name: "AES-GCM", iv: wrap.subarray(0, 12)}, wk, wrap.subarray(12)); }
  catch { throw new Error("BADPW"); }
  return crypto.subtle.importKey("raw", raw, {name: "AES-GCM"}, false, ["decrypt"]);
}
function metaTests() { return META.tests || [{id: "t1", label: "Test 1", files: META.files}]; }
async function unlock(pw) {
  if (!META) { const r = await fetch("data/meta.json", {cache: "no-cache"}); META = await r.json(); }
  const { ym, mm } = tokyoParts();
  const key = await unwrapDataKey(pw, mm);
  const out = {};
  for (const tt of metaTests()) {
    const bytes = await fetchBin(tt.files.data.file);
    let plain;
    try { plain = await decryptBin(key, bytes); } catch { throw new Error("BADPW"); }
    const d = JSON.parse(new TextDecoder().decode(plain));
    Object.assign(d, {_id: tt.id, _label: tt.label, _files: tt.files, _urls: {}, _pending: {}, _img: {}});
    out[tt.id] = d;
  }
  TESTS = out; KEY = key; UNLOCK_YM = ym;
  for (const d of Object.values(TESTS)) await loadImages(d);
  const last = localStorage.getItem(TKEY);
  selectTest(TESTS[last] ? last : metaTests()[0].id);
}
function selectTest(id) { TID = id; DATA = TESTS[id]; localStorage.setItem(TKEY, id); }
/* Part 1 photos: one encrypted blob per test → Blob URL per photo */
async function loadImages(d) {
  if (!d._files.p1img || !d.p1img) return;
  const ab = await decryptBin(KEY, await fetchBin(d._files.p1img.file));
  for (const [n, c] of Object.entries(d.p1img)) d._img[n] = URL.createObjectURL(new Blob([new Uint8Array(ab, c.off, c.len)], {type: "image/jpeg"}));
}
/* audio: one encrypted blob per Part (per test) → decrypted → one Blob URL per clip */
const AudioStore = {
  ensure(p, onprog) {
    const d = DATA;
    if (d._urls[p]) return Promise.resolve();
    if (!d._pending[p]) d._pending[p] = (async () => {
      const bytes = await fetchBin(d._files["a" + p].file, onprog);
      const ab = await decryptBin(KEY, bytes);
      d._urls[p] = d.audio[p].map(c => URL.createObjectURL(new Blob([new Uint8Array(ab, c.off, c.len)], {type: "audio/mpeg"})));
    })().catch(e => { delete d._pending[p]; throw e; });
    return d._pending[p];
  },
  url(a) { return DATA._urls[a[0]] && DATA._urls[a[0]][a[1]]; }
};
/* wrong-answer notebook keys: Test 1 keeps bare question numbers (backward compatible), other tests use "t2:105" */
const nkey = no => TID === "t1" ? String(no) : `${TID}:${no}`;
const noteNo = k => { const m = String(k).match(/^(?:(\w+):)?(\d+)$/); return m && (m[1] || "t1") === TID ? +m[2] : null; };

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
  return {id: vid, title: dTitle(DATA) + " · " + vName(v), name: vName(v), count: v.count, sections};
}
function allQuestions(test) {
  const out = [];
  for (const s of test.sections) for (const u of s.units) for (const g of u.groups) for (const q of g.questions) out.push({q, g, u, s});
  return out;
}
function groupOfQ(no) { for (const g of Object.values(DATA.groups)) for (const q of g.questions) if (q.no === no) return {g, q}; return null; }

let T = null, S = null;
function setHud(on) { hud.classList.toggle("hidden", !on); $("#foot").classList.toggle("hidden", on || SIM); $("#hudQ").textContent = ""; }
function showOverlay(html, center = true) { overlay.innerHTML = `<div class="sheet">${html}</div>`; overlay.classList.toggle("center", center); overlay.classList.remove("hidden"); }
function hideOverlay() { overlay.classList.add("hidden"); overlay.innerHTML = ""; }
overlay.addEventListener("click", e => { if (e.target === overlay && overlay.dataset.dismiss === "1") hideOverlay(); });
window.addEventListener("beforeunload", e => { if (S && !S.done) { e.preventDefault(); e.returnValue = ""; } });

/* ---------- router ---------- */
function go(hash) { if (location.hash === hash) route(); else location.hash = hash; }
window.addEventListener("hashchange", route);
$("#brand").onclick = () => { if (S && !S.done) { if (!confirm(t("confirmQuitExam"))) return; abortExam(); } go("#/"); };
async function route() {
  window.scrollTo(0, 0);
  if (!DATA) return renderLock();
  const h = location.hash || "#/";
  if (S && !S.done && !h.startsWith("#/exam")) abortExam();
  if (h.startsWith("#/intro/")) return renderIntro(h.split("/")[2]);
  if (h.startsWith("#/result/")) return renderResult(h.split("/")[2]);
  if (h.startsWith("#/review/")) return renderReview(h.split("/")[2]);
  if (h.startsWith("#/notebook")) return renderNotebook();
  if (h.startsWith("#/history")) return renderHistoryPage();
  if (h.startsWith("#/exam")) { if (!S) return go("#/"); return; }
  renderHome();
}

/* ---------- lock screen ---------- */
function renderLock(msg = "") {
  setHud(false);
  if (SIM) document.body.classList.add("sim");
  app.innerHTML = SIM ? `<div class="simpanel lock">${window.I18N.switchHTML()}<h1>TOEIC® Listening &amp; Reading Test <small>${t("simLockSub")}</small></h1>
   <p>${t("simLockP")}</p>
   <form id="lockForm"><input type="password" id="pw" autocomplete="current-password" placeholder="${t("simLockPh")}" required>
   ${SHELL ? "" : `<label><input type="checkbox" id="remember"> ${t("rememberShort")}</label>`}
   <div class="err" id="err">${esc(msg)}</div>
   <button class="btn block" id="unlockBtn" type="submit">SUBMIT</button></form>${SHELL ? `<p style="margin-top:18px"><button class="btn ghost small" type="button" id="lockExit">${t("exitBtn")}</button></p>` : ""}</div>` : `<div class="card lock hero">${window.I18N.switchHTML()}<div class="eyebrow">Private Mock Exam</div>
   <h1>${t("lockTitle")}</h1>
   <p class="muted">${t("lockDesc")}</p>
   <form id="lockForm"><input type="password" id="pw" autocomplete="current-password" placeholder="${t("pwPh")}" required>
   <label><input type="checkbox" id="remember"> ${t("rememberLong")}</label>
   <div class="err" id="err">${esc(msg)}</div>
   <button class="btn block" id="unlockBtn" type="submit">${t("unlockBtn")}</button></form></div>`;
  bindLang(() => { const v = $("#pw").value, r = $("#remember") && $("#remember").checked; renderLock(); $("#pw").value = v; if (r && $("#remember")) $("#remember").checked = true; });
  const le = $("#lockExit"); if (le) le.onclick = () => simConfirmExit();
  $("#lockForm").onsubmit = async e => {
    e.preventDefault();
    const pw = $("#pw").value, btn = $("#unlockBtn");
    btn.disabled = true; btn.textContent = t("verifying"); $("#err").textContent = "";
    try {
      await unlock(pw);
      if ($("#remember") && $("#remember").checked) savePwSession(pw, UNLOCK_YM); else clearSavedPw();
      route();
    } catch (err) {
      btn.disabled = false; btn.textContent = SIM ? "SUBMIT" : t("unlockBtn");
      const code = err && err.message;
      $("#err").textContent = code === "BADPW" ? t("badPwMonth") : t("loadFail");
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
  return `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="${t("trendAria")}">${g}<polyline points="${line}" fill="none" stroke="#1d6fb8" stroke-width="2.5"/>${dots}</svg><div class="muted">${t("trendNote")}</div>`;
}
/* history entries store the mode name in the language used at the time; show it in the current language when possible */
function modeNameOf(a) { const d = TESTS[a.tid || "t1"], v = d && d.variants[a.vid]; return v ? vName(v) : a.modeName; }
function historyCard() {
  const h = loadHist();
  if (!h.length) return `<div class="card"><h2>${t("histTitle")}</h2><p class="muted">${t("histEmpty")}</p></div>`;
  const rows = h.slice().reverse().slice(0, 15).map(a => `<tr><td>${new Date(a.date).toLocaleDateString(loc())}</td><td>${esc(modeNameOf(a))}</td><td>${a.lN ? `${a.lScore}<br><small>${a.lRaw}/${a.lN}</small>` : "—"}</td><td>${a.rN ? `${a.rScore}<br><small>${a.rRaw}/${a.rN}</small>` : "—"}</td><td><b>${a.lN && a.rN ? a.total : "—"}</b></td><td><a href="#/result/${a.id}">${t("detail")}</a></td></tr>`).join("");
  return `<div class="card trend"><h2>${t("histTitle")}</h2>${trendSVG(h.filter(a => a.lN && a.rN))}
  <table class="hist"><tr><th>${t("thDate")}</th><th>${t("thMode")}</th><th>${t("thL")}</th><th>${t("thR")}</th><th>${t("thTotal")}</th><th></th></tr>${rows}</table>
  <p class="muted">${t("histFoot")}<a href="#" id="clearHist">${t("clearHist")}</a></p></div>`;
}
function renderHome() {
  setHud(false); S = null;
  if (SIM) return simHome();
  const nbo = loadNote(), nb = Object.keys(nbo).filter(k => !nbo[k].ok && noteNo(k) !== null).length;
  const V = DATA.variants;
  const modeChip = k => {
    if (k === "ip") return `<span class="chip">⏱ 60 min</span><span class="chip">90 Q</span><span class="chip">IP Online</span>`;
    if (k === "full") return `<span class="chip">⏱ ~120 min</span><span class="chip">200 Q</span><span class="chip">Full L&R</span>`;
    if (k === "L") return `<span class="chip">🎧 Listening</span><span class="chip">~45 min</span>`;
    if (k === "R") return `<span class="chip">📖 Reading</span><span class="chip">75 min</span>`;
    return "";
  };
  app.innerHTML = `
  <div class="card hero">${window.I18N.switchHTML()}<div class="eyebrow">TOEIC® L&R Mock</div>
  <h1>${esc(dTitle(DATA))}</h1>
  <p class="muted">${t("homeDesc")}</p></div>
  ${testPicker()}
  <div class="card"><h2>${t("simCardTitle")}</h2><p class="muted">${t("simCardDesc")}</p>
   <button class="btn block" id="simEnter">${t("simEnter")}</button></div>
  <div class="card modes"><h2>${t("chooseMode")}</h2>
  <div class="mode-grid main">${["ip","full"].filter(k => V[k]).map(k => `<a class="mode-card primary" href="#/intro/${k}"><div class="mode-kicker">${k === "ip" ? "IP Online" : "Full Test"}</div><h3>${esc(vName(V[k]))}</h3><p class="muted">${esc(vDesc(V[k]))}</p><div class="mode-meta">${modeChip(k)}</div><span class="btn block" style="margin-top:10px;pointer-events:none">${t("start")}</span></a>`).join("")}</div>
  <h3 class="mode-sec">${t("practiceModes")}</h3>
  <div class="nav-tiles">${["L","R"].filter(k => V[k]).map(k => `<a class="nav-tile" href="#/intro/${k}"><strong>${esc(vName(V[k]))}</strong><span>${esc(vDesc(V[k]))}</span></a>`).join("")}</div></div>
  <div class="nav-tiles" style="margin:14px 0">
   <a class="nav-tile" href="#/notebook"><strong>${t("nbTitle")}</strong><span>${t("nbCount", nb)}</span></a>
   <a class="nav-tile" href="#/history"><strong>${t("simHist")}</strong><span>${t("histTitle")}</span></a>
  </div>
  ${historyCard()}
  <div class="card"><details><summary>${t("notes")}</summary><ul class="rules">${pick(DATA, "notes").map(n => `<li>${esc(n)}</li>`).join("")}</ul></details>
  <p><a href="#" id="lockNow">${t("lockNow")}</a></p></div>`;
  bindLang(renderHome);
  const c = $("#clearHist"); if (c) c.onclick = e => { e.preventDefault(); if (confirm(t("confirmClearHist"))) { localStorage.removeItem(HKEY); renderHome(); } };
  bindTestPicker(renderHome);
  $("#simEnter").onclick = () => enterSim();
  $("#lockNow").onclick = e => { e.preventDefault(); clearSavedPw(); location.hash = "#/"; location.reload(); };
}

/* ---------- intro ---------- */
function renderIntro(vid) {
  setHud(false);
  if (!DATA.variants[vid]) return go("#/");
  const test = buildVariant(vid);
  const L = test.sections.find(s => s.id === "L"), R = test.sections.find(s => s.id === "R");
  const lQ = L ? L.units.reduce((a, u) => a + u.groups.reduce((b, g) => b + g.questions.length, 0), 0) : 0;
  const lMin = L ? Math.round(L.units.flatMap(u => u.groups).reduce((a, g) => a + g.duration, 0) / 60) : 0;
  app.innerHTML = `<div class="card"><h1>${esc(t("introTitle", test.name))}</h1>
  ${L ? `<h3>${t("introL", lMin, lQ)}</h3>
  <ul class="rules">
   <li>${t("introL1")}</li>
   <li>${t("introL2")}</li>
   <li>${t("introL3")}</li>
   <li>${t("introL4")}</li>
  </ul>` : ""}
  ${R ? `<h3>${t("introR", R.units.map(u => t("unitMin", u.name, Math.round(u.time / 60))).join(" + "))}</h3>
  <ul class="rules">
   <li>${R.units.length > 1 ? t("introR1multi") : t("introR1single")}</li>
   <li>${t("introR2")}</li>
   <li>${t("introR3", R.units.length > 1)}</li>
  </ul>` : ""}
  <h3>${t("introPrep")}</h3>
  <ul class="rules">
   <li>${t("introP1")}</li>
   <li>${t("introP2")}</li>
  </ul>
  <div class="row" style="margin-top:14px"><a class="btn ghost" href="#/">${t("back")}</a><button class="btn" id="startBtn">${t("enterExam")}</button></div></div>`;
  $("#startBtn").onclick = () => startExam(test);
}

let wakeLock = null;
async function requestWakeLock() {
  try { if ("wakeLock" in navigator && !wakeLock) { wakeLock = await navigator.wakeLock.request("screen"); wakeLock.addEventListener("release", () => { wakeLock = null; }); } } catch {}
}
document.addEventListener("visibilitychange", () => { if (!document.hidden && S && !S.done) requestWakeLock(); });

/* ---------- audio engine (Web Audio, unlocked by one tap for iOS) ---------- */
const AudioEng = {
  ctx: null, src: null, buffers: {}, startAt: 0, html: null, gain: null, vol: Math.min(1, Math.max(0, +(localStorage.getItem(VKEY) ?? 1))),
  setVolume(v) { this.vol = v; localStorage.setItem(VKEY, v); if (this.gain) this.gain.gain.value = v; if (this.html) this.html.volume = v; },
  unlock() {
    try { if (navigator.audioSession) navigator.audioSession.type = "playback"; } catch {}
    requestWakeLock();
    const AC = window.AudioContext || window.webkitAudioContext;
    if (AC && !this.ctx) {
      this.ctx = new AC();
      const b = this.ctx.createBuffer(1, 1, 22050), s = this.ctx.createBufferSource();
      s.buffer = b; s.connect(this.ctx.destination); s.start(0);
      this.gain = this.ctx.createGain(); this.gain.gain.value = this.vol; this.gain.connect(this.ctx.destination);
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
      const s = this.ctx.createBufferSource(); s.buffer = buf; s.connect(this.gain || this.ctx.destination);
      s.onended = () => { if (this.src === s) { this.src = null; onended(); } };
      this.src = s; this.startAt = this.ctx.currentTime; s.start(0);
    } else {
      const a = this.html || new Audio(); this.html = a; a.volume = this.vol; a.src = url; a.onended = onended; await a.play();
      this.startAt = performance.now() / 1000;
    }
  },
  elapsed() { return this.ctx ? this.ctx.currentTime - this.startAt : (this.html ? this.html.currentTime : 0); },
  stop() { if (this.src) { const s = this.src; this.src = null; try { s.onended = null; s.stop(); } catch {} } if (this.html) { this.html.onended = null; this.html.pause(); } },
  skip() { if (this.src) { const s = this.src; try { s.stop(); } catch {} } else if (this.html) { this.html.onended && this.html.onended(); } }
};
document.addEventListener("visibilitychange", () => {
  if (!document.hidden && S && S.phase === "L" && AudioEng.ctx && AudioEng.ctx.state !== "running") {
    showOverlay(`<div class="gate"><div class="big">⏸</div><p>${t("audioPaused")}</p><button class="btn block" id="resumeBtn">${t("tapResume")}</button></div>`);
    $("#resumeBtn").onclick = () => { AudioEng.ctx.resume(); hideOverlay(); };
  }
});

/* ---------- exam ---------- */
function startExam(test) {
  T = test;
  S = {vid: test.id, answers: {}, flags: {}, phase: "L", li: 0, lu: 0, done: false, started: Date.now(), tick: null, sim: SIM, ansLeft: null, ansDeadline: 0};
  if (SHELL) SHELL.setExamActive(true);
  simBar(S.sim ? "" : null);
  const L = test.sections.find(s => s.id === "L");
  S.lunits = L ? L.units.map(u => ({name: u.name, groups: u.groups.map(g => Object.assign(g, {_unit: u}))})) : [];
  S.lgroups = S.lunits.flatMap(u => u.groups);
  S.lTotal = S.lgroups.reduce((a, g) => a + g.duration, 0);
  S.lCount = S.lgroups.reduce((a, g) => a + g.questions.length, 0);
  const R = test.sections.find(s => s.id === "R");
  S.runits = R ? R.units.map(u => FAST ? Object.assign({}, u, {time: Math.min(u.time, 25)}) : u) : [];
  // Display numbers for reading (1..N across the section) and listening
  S.rDisp = {}; let ri = 0;
  for (const u of S.runits) for (const g of u.groups) for (const q of g.questions) S.rDisp[q.no] = ++ri;
  S.rTotal = ri;
  S.lDisp = {}; let li = 0;
  for (const g of S.lgroups) for (const q of g.questions) S.lDisp[q.no] = ++li;
  setHud(true);
  go("#/exam");
  if (!L) { S.tick = setInterval(tick, 250); requestWakeLock(); return startReading(); }
  hideListeningTimer();
  hudSection.textContent = t("hudListening");
  const parts = [...new Set(S.lgroups.map(g => g.audio[0]))];
  const ansToggle = `<label class="ans-tog"><input type="checkbox" id="ansTimerChk" ${showAnsTimer() ? "checked" : ""}> ${t("ansTimerLbl")}</label>`;
  app.innerHTML = S.sim ? `<div class="simpanel"><h2>Listening Test <small>${t("simLSub")}</small></h2>
   <p>${t("simLOnlineP", S.vid === "ip" ? 25 : 45)}</p>
   <p class="muted">${t("simLInfo", S.lCount, Math.round(S.lTotal / 60))}</p>
   ${ansToggle}
   <p id="prep">${t("simPrep")} <b id="prepPct">0%</b></p>
   <button class="btn block" id="gateBtn" disabled>${t("simWait")}</button></div>` :
   `<div class="card gate"><div class="big">🎧</div><h2>${t("lGateTitle")}</h2>
   <p class="muted">${t("lGateInfo", S.lCount, Math.round(S.lTotal / 60))}</p>
   ${ansToggle}
   <p id="prep">${t("prepDl")} <b id="prepPct">0%</b></p>
   <button class="btn block" id="gateBtn" disabled>${t("wait")}</button></div>`;
  const chk = $("#ansTimerChk"); if (chk) chk.onchange = e => setAnsTimer(e.target.checked);
  const sizes = parts.map(p => DATA._files["a" + p].size), tot = sizes.reduce((a, b) => a + b, 0), prog = parts.map(() => 0);
  const upd = () => { const e = $("#prepPct"); if (e) e.textContent = Math.round(prog.reduce((a, x, i) => a + x * sizes[i], 0) / tot * 100) + "%"; };
  (async () => {
    try {
      for (let i = 0; i < parts.length; i++) await AudioStore.ensure(parts[i], f => { prog[i] = f; upd(); });
      if (!S || S.phase !== "L") return;
      $("#prep").textContent = t("audioReady");
      const b = $("#gateBtn"); b.disabled = false; b.textContent = S.sim ? t("simNextStart") : t("startListening");
      b.onclick = () => { AudioEng.unlock(); S.tick = setInterval(tick, 250); if (S.sim) listenOverview(); else playGroup(0); };
    } catch (e) {
      $("#prep").innerHTML = `<span style="color:#dc2626">${t("audioLoadFail")}</span>`;
    }
  })();
}
function hideListeningTimer() {
  hudTimer.textContent = "";
  hudTimer.classList.add("hidden");
  hudTimer.classList.remove("warn", "reading");
}
function showReadingTimer(sec) {
  hudTimer.classList.remove("hidden");
  hudTimer.classList.add("reading");
  hudTimer.textContent = fmtHMS(sec);
}
function releaseWake() { if (wakeLock) { wakeLock.release().catch(() => {}); wakeLock = null; } hudTimer.classList.remove("warn", "reading"); hudTimer.classList.remove("hidden"); }
function abortExam() { releaseWake(); simBar(null); if (SHELL) SHELL.setExamActive(false); if (!S) return; AudioEng.stop(); AudioEng.prune([]); clearInterval(S.tick); clearTimeout(S.ansTimer); S = null; hideOverlay(); setHud(false); }

function tick() {
  if (!S || S.done) return;
  if (S.phase === "L" || S.phase === "L-dir" || S.phase === "L-gap") {
    hideListeningTimer();
    // Optional per-question remaining-seconds during the post-audio answer window
    if (S.phase === "L-gap" && S.ansDeadline) {
      const left = Math.max(0, (S.ansDeadline - Date.now()) / 1000);
      S.ansLeft = left;
      const el = $("#ansLeft");
      if (el) el.textContent = showAnsTimer() ? t("ansLeft", Math.ceil(left)) : "";
      if (showAnsTimer() && el) el.classList.toggle("hidden", false);
    }
  } else if (S.phase === "R" || S.phase === "R-dir" || S.phase === "R-rev") {
    const left = (S.rDeadline - Date.now()) / 1000;
    showReadingTimer(left);
    hudTimer.classList.toggle("warn", left < 300);
    if (left <= 0 && !S.timeupShown) {
      S.timeupShown = true;
      const more = S.ru < S.runits.length - 1;
      showTimeUpPage(more ? t("unitTimeUp", S.runits[S.ru].name) : t("allTimeUp"), () => {
        if (more) startReadingUnit(S.ru + 1); else submit();
      });
    }
  }
}

function showTimeUpPage(msg, then) {
  AudioEng.stop();
  clearTimeout(S.ansTimer);
  S.phase = "timeup";
  hideOverlay();
  app.innerHTML = `<div class="simpanel center timeup"><div class="big">⏰</div><h1>${t("timeUpTitle")}</h1><p>${esc(msg)}</p><p class="muted">${t("timeUpNext")}</p></div>`;
  simBar(S.sim ? `<span></span><button class="btn" id="timeupGo">Next ›</button>` : null);
  const goNext = () => { if (S) { S.timeupShown = false; then(); } };
  if ($("#timeupGo")) $("#timeupGo").onclick = goNext;
  else setTimeout(goNext, 1800);
}
function timeUpNote(msg) {   // fallback toast (non-sim)
  const n = document.createElement("div"); n.className = "toast"; n.textContent = "⏰ " + msg;
  document.body.appendChild(n); setTimeout(() => n.remove(), 5000);
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
    if (S.phase === "R" || S.phase === "R-dir" || S.phase === "R-rev") updatePaletteState();
  });
}
const photoImg = g => DATA._img[g.questions[0].no] ? `<img class="scene p1photo" src="${DATA._img[g.questions[0].no]}" alt="${t("photoAlt", g.questions[0].no)}">` : `<div class="photo-ph"><div class="lbl">${t("photoFail")}</div></div>`;
const photoHTML = photoImg;
const photoReviewHTML = g => `${photoImg(g)}${g.photo ? `<div class="photo-ph refdesc"><div class="lbl">${t("refDesc")}</div><p>${esc(g.photo)}</p></div>` : ""}`;
const gfxHTML = g => g.graphic ? tableHTML(g.graphic.rows, g.graphic.title) : "";

function dirAudioUrl(key) { return "audio/" + key + ".mp3"; }

/** Listening overview directions (online style). Overview audio auto-advances when it finishes. */
function listenOverview() {
  S.phase = "L-dir"; hideListeningTimer();
  const isIp = S.vid === "ip";
  const clip = isIp ? "dir_overview_ip" : "dir_overview_full";
  const mins = isIp ? 25 : 45;
  $("#hudQ").textContent = "Directions";
  hudSection.textContent = t("hudListening");
  app.innerHTML = `<div class="simpanel"><h2>Listening Test <small>${t("simLSub")}</small></h2>
   <p><b>Directions:</b> ${t("dirListenOnline", mins)}</p>
   <div class="listenstate" id="ls"><span class="wave"><i></i><i></i><i></i><i></i></span><span>${t("simNowPlaying")}</span></div>
   <p class="muted">${t("dirOverviewAuto")}</p></div>`;
  simBar(`<span class="muted">${t("simAutoPlay")}</span><button class="btn" id="simNext">Next ›</button>`);
  let advanced = false;
  const advance = () => { if (advanced || !S) return; advanced = true; AudioEng.stop(); listenUnitIntro(0); };
  $("#simNext").onclick = advance;
  AudioEng.play(dirAudioUrl(clip), () => { const ls = $("#ls"); if (ls) ls.innerHTML = `<span>${t("dirAudioDone")}</span>`; setTimeout(advance, 600); }).catch(() => {});
}

/** UNIT intro / UNIT TWO transition for listening. */
function listenUnitIntro(lu) {
  S.lu = lu; S.phase = "L-dir"; hideListeningTimer();
  const u = S.lunits[lu];
  if (!u) return S.runits.length ? startReading() : submit();
  const first = S.lgroups.indexOf(u.groups[0]);
  const q0 = u.groups[0].questions[0];
  const qN = u.groups.at(-1).questions.at(-1);
  const d0 = S.lDisp[q0.no], d1 = S.lDisp[qN.no];
  $("#hudQ").textContent = "Directions";
  hudSection.textContent = t("hudL", u.name);
  app.innerHTML = `<div class="simpanel"><h2>Listening · ${esc(u.name)}</h2>
   <p>${t("lUnitIntro", u.name, d0, d1, S.lCount)}</p>
   <p class="muted">${t("lUnitIntroNote")}</p>
   <div class="listenstate" id="ls"><span class="wave"><i></i><i></i><i></i><i></i></span><span>${t("simNowPlaying")}</span></div></div>`;
  simBar(`<span></span><button class="btn" id="simNext">Next ›</button>`);
  // Replay overview directions briefly for UNIT TWO; UNIT ONE continues to Part 1 directions.
  const clip = lu > 0 ? (S.vid === "ip" ? "dir_overview_ip" : "dir_overview_full") : null;
  let ready = false;
  const goPart = () => { if (!S) return; AudioEng.stop(); listenPartDir(first); };
  $("#simNext").onclick = goPart;
  if (clip) {
    AudioEng.play(dirAudioUrl(clip), () => { const ls = $("#ls"); if (ls) ls.innerHTML = `<span>${t("dirAudioDone")}</span>`; }).catch(() => {});
  } else {
    const ls = $("#ls"); if (ls) ls.innerHTML = `<span class="muted">${t("clickNextPart")}</span>`;
  }
}

/** Part directions screen (Next). Plays part direction audio. */
function listenPartDir(groupIndex) {
  const g = S.lgroups[groupIndex];
  if (!g) return listenAfterGroup(groupIndex - 1);
  S.phase = "L-dir"; S.li = groupIndex; hideListeningTimer();
  $("#hudQ").textContent = "Directions";
  hudSection.textContent = t("hudL", g._unit.name);
  const partClip = "dir_part" + g.part;
  app.innerHTML = `<div class="simpanel"><h2>${PART_ZH[g.part]}</h2>
   <p><b>Directions:</b> ${PART_DIR_ZH[g.part]}</p>
   <p class="muted">${t("dirClickNext")}</p>
   <div class="listenstate" id="ls"><span class="wave"><i></i><i></i><i></i><i></i></span><span>${t("simNowPlaying")}</span></div></div>`;
  simBar(`<span></span><button class="btn" id="simNext">Next ›</button>`);
  $("#simNext").onclick = () => { AudioEng.stop(); playGroup(groupIndex); };
  AudioEng.play(dirAudioUrl(partClip), () => { const ls = $("#ls"); if (ls) ls.innerHTML = `<span>${t("dirAudioDone")}</span>`; }).catch(() => {});
}

function listenAfterGroup(i) {
  const g = S.lgroups[i], next = S.lgroups[i + 1];
  if (!next) {
    // End of listening: answer window already elapsed — go straight to reading (no end-audio / dead air).
    AudioEng.stop(); AudioEng.prune([]);
    return S.runits.length ? startReading() : submit();
  }
  // Unit boundary → UNIT TWO transition (repeat directions)
  if (g._unit !== next._unit) {
    const lu = S.lunits.findIndex(u => u === next._unit);
    return listenUnitIntro(lu);
  }
  // Part boundary → part directions
  if (g.part !== next.part) return listenPartDir(i + 1);
  return playGroup(i + 1);
}

async function playGroup(i) {
  S.li = i; S.phase = "L"; clearTimeout(S.ansTimer); S.ansDeadline = 0;
  window.scrollTo(0, 0);
  const g = S.lgroups[i];
  if (!g) { AudioEng.prune([]); return S.runits.length ? startReading() : submit(); }
  hideListeningTimer();
  const done = S.lgroups.slice(0, i).reduce((a, x) => a + x.questions.length, 0);
  hudSection.textContent = t("hudL", g._unit.name);
  let body = "";
  const q0 = g.questions[0];
  if (g.part === 1) body = `${photoHTML(g)}<div class="qblock"><div class="qtext"><span class="qno">${S.lDisp[q0.no] || q0.no}.</span>${t("p1Prompt")}</div>${optsHTML(q0, false, 4)}</div>`;
  else if (g.part === 2) body = `<div class="qblock"><div class="qtext"><span class="qno">${S.lDisp[q0.no] || q0.no}.</span>${t("p2Prompt")}</div>${optsHTML(q0, false, 3)}</div>`;
  else body = gfxHTML(g) + g.questions.map(q => `<div class="qblock"><div class="qtext"><span class="qno">${S.lDisp[q.no] || q.no}.</span>${esc(q.q)}</div>${optsHTML(q, true)}</div>`).join("");
  const ansBox = `<div class="ansleft${showAnsTimer() ? "" : " hidden"}" id="ansLeft"></div>`;
  if (S.sim) {
    $("#hudQ").textContent = `Question ${S.lDisp[q0.no] || q0.no}${g.questions.length > 1 ? "–" + (S.lDisp[g.questions.at(-1).no] || g.questions.at(-1).no) : ""}`;
    simBar(`<span class="muted">Listening · ${PART_ZH[g.part]} · ${t("simAutoPlay")}</span>${ansBox}`);
  }
  app.innerHTML = S.sim ? `<div class="simpanel listen">
   <div class="qhead" style="margin-bottom:8px"><div class="qnum">Question ${S.lDisp[q0.no] || q0.no}${g.questions.length > 1 ? "–" + (S.lDisp[g.questions.at(-1).no] || g.questions.at(-1).no) : ""}</div><span class="muted">${PART_ZH[g.part]}</span></div>
   <div class="listenstate" id="ls"><span class="wave"><i></i><i></i><i></i><i></i></span><span>${t("simNowPlaying")}</span></div>
   ${g.part === 2 ? `<div class="qtext">${t("p2OnlinePrompt")}</div>${optsHTML(q0, false, 3)}` : body}</div>
   ${DEBUG ? `<button class="btn ghost small" id="dbgSkip">${t("dbgSkip")}</button>` : ""}` : `<div class="progress"><i style="width:${done / S.lCount * 100}%"></i></div>
   <div class="partbar"><span>${PART_ZH[g.part]}</span><span>${S.lDisp[q0.no] || q0.no}${g.questions.length > 1 ? "–" + (S.lDisp[g.questions.at(-1).no] || g.questions.at(-1).no) : ""}</span></div>
   <div class="card"><div class="listenstate" id="ls"><span class="wave"><i></i><i></i><i></i><i></i></span><span>${t("nowPlaying")}</span></div>${body}${ansBox}</div>
   ${DEBUG ? `<button class="btn ghost small" id="dbgSkip">${t("dbgSkip")}</button>` : ""}`;
  bindOpts(app);
  if (DEBUG) $("#dbgSkip").onclick = () => { clearTimeout(S.ansTimer); AudioEng.skip(); };
  const url = AudioStore.url(g.audio), next = S.lgroups[i + 1] ? AudioStore.url(S.lgroups[i + 1].audio) : null;
  AudioEng.prune([url, next].filter(Boolean));
  if (next) AudioEng.load(next);
  const afterAudio = () => {
    if (!S || S.li !== i) return;
    // Fixed answer window after audio; unanswered stay undefined
    const gap = FAST ? 2 : (ANSWER_GAP[g.part] || 5);
    S.phase = "L-gap";
    S.ansDeadline = Date.now() + gap * 1000;
    const ls = $("#ls");
    if (ls) ls.innerHTML = `<span>${t("ansWindow")}</span>`;
    if (showAnsTimer()) {
      const el = $("#ansLeft"); if (el) { el.classList.remove("hidden"); el.textContent = t("ansLeft", gap); }
    }
    S.ansTimer = setTimeout(() => {
      if (!S || S.li !== i) return;
      S.ansDeadline = 0;
      if (S.sim) listenAfterGroup(i); else playGroup(i + 1);
    }, gap * 1000);
  };
  try {
    await AudioEng.play(url, afterAudio);
  } catch (e) {
    const ls = $("#ls"); if (!ls) return;
    ls.innerHTML = `<span style="color:#dc2626">${t("playFail")}</span> <button class="btn small" id="retryA">${t("retry")}</button>`;
    $("#retryA").onclick = () => playGroup(i);
  }
}

function startReading() {
  AudioEng.stop();
  if (S.sim) return simReadingIntro();
  S.phase = "R-gate";
  hudSection.textContent = t("hudReading");
  showReadingTimer(S.runits[0].time);
  app.innerHTML = `<div class="card gate"><div class="big">📖</div><h2>${S.lgroups.length ? t("rGateAfterL") : t("rGateOnly")}</h2>
   <p>${S.runits.map(u => t("rUnitLine", u.name, Math.round(u.time / 60), u.groups.reduce((a, g) => a + g.questions.length, 0))).join("<br>")}</p><p class="muted">${t("rGateNote")}</p>
   <button class="btn block" id="rStart">${t("rStart")}</button></div>`;
  $("#rStart").onclick = () => { requestWakeLock(); if (!S.tick) S.tick = setInterval(tick, 250); startReadingUnit(0); };
}
function startReadingUnit(ru) {
  hideOverlay();
  S.phase = "R"; S.ru = ru; S.rg = 0; S.ri = 0; S.timeupShown = false;
  const u = S.runits[ru];
  S.rDeadline = Date.now() + u.time * 1000;
  showReadingTimer(u.time);
  hudSection.textContent = t("hudR", u.name);
  if (S.sim) return simUnitDir();
  renderReadingGroup();
}
const lastUnit = () => S.ru === S.runits.length - 1;
function unitRange(u) {
  const nos = u.groups.flatMap(g => g.questions.map(q => S.rDisp[q.no]));
  return [Math.min(...nos), Math.max(...nos)];
}
function renderReadingGroup(scrollToNo) {
  const u = S.runits[S.ru], g = u.groups[S.rg];
  const last = S.rg === u.groups.length - 1;
  const qs = g.questions.map(q => `<div class="qblock" id="q${q.no}"><div class="qhead"><div class="qtext"><span class="qno">${S.rDisp[q.no] || q.no}.</span>${q.q ? inline(q.q) : t("blankPrompt", S.rDisp[q.no] || q.no)}</div>
     <button class="flagbtn${S.flags[q.no] ? " on" : ""}" data-flag="${q.no}">🚩 ${S.flags[q.no] ? t("flagged") : t("flag")}</button></div>${optsHTML(q, true)}</div>`).join("");
  const all = u.groups.flatMap(x => x.questions);
  const answered = all.filter(q => S.answers[q.no] !== undefined).length;
  const [a, b] = unitRange(u);
  app.innerHTML = `<div class="partbar"><span>${PART_ZH[g.part]}</span><span>${t("answered", answered, all.length)}</span><span class="muted">${t("rRange", a, b, S.rTotal)}</span></div>
   ${g.part === 5 && (S.rg === 0 || u.groups[S.rg - 1].part !== 5) ? `<div class="dirnote">${t("dir5")}</div>` : ""}
   ${g.part === 6 ? `<div class="dirnote">${t("dir6")}</div>` : ""}
   ${g.part === 7 ? `<div class="dirnote">${t("dir7")}</div>` : ""}
   <div class="card">${docsHTML(g)}${qs}</div>
   <div class="navbar">
    <button class="btn ghost" id="prevG" ${S.rg === 0 ? "disabled" : ""}>${t("prevPage")}</button>
    <button class="btn ghost" id="palBtn">${t("palette")}</button>
    ${last ? `<button class="btn ${lastUnit() ? "warn" : ""}" id="endUnit">${lastUnit() ? t("submitBtn") : esc(t("finishUnit", u.name))}</button>` : `<button class="btn" id="nextG">${t("nextPage")}</button>`}
   </div>`;
  bindOpts(app);
  app.querySelectorAll("[data-flag]").forEach(b => b.onclick = () => {
    const no = +b.dataset.flag; S.flags[no] = !S.flags[no];
    b.classList.toggle("on", S.flags[no]); b.textContent = `🚩 ${S.flags[no] ? t("flagged") : t("flag")}`;
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
  const un = items.filter(x => S.answers[x.q.no] === undefined);
  const fl = items.filter(x => S.flags[x.q.no]).length;
  const endTxt = lastUnit() ? t("submitBtn") : t("enterUnit", S.runits[S.ru + 1].name);
  overlay.dataset.dismiss = "1";
  showOverlay(`<h2>${esc(t("palTitle", u.name))}</h2>
   <p class="muted">${t("palNote")}</p>
   <div class="palette">${items.map(x => `<button class="pal${S.answers[x.q.no] !== undefined ? " done" : ""}${S.flags[x.q.no] ? " flag" : ""}${x.gi === S.rg ? " cur" : ""}" data-gi="${x.gi}" data-no="${x.q.no}">${S.rDisp[x.q.no] || x.q.no}</button>`).join("")}</div>
   <p>${t("palCounts", un.length, fl)}</p>
   ${un.length ? `<p class="muted">${t("unansweredList", un.map(x => S.rDisp[x.q.no] || x.q.no).join(", "))}</p>` : ""}
   <p class="muted">${lastUnit() ? t("noChangeAfterSubmit") : t("noReturnNext")}</p>
   <div class="row"><button class="btn ghost" id="palClose">${t("continueAnswer")}</button>
   <button class="btn ${lastUnit() ? "warn" : ""}" id="palEnd">${endTxt}</button></div>`, false);
  overlay.querySelectorAll(".pal").forEach(b => b.onclick = () => { hideOverlay(); S.rg = +b.dataset.gi; renderReadingGroup(+b.dataset.no); });
  $("#palClose").onclick = hideOverlay;
  $("#palEnd").onclick = () => {
    if (un.length && !confirm(t("confirmUnanswered", un.length, endTxt))) return;
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
    if (!ok) { const k = nkey(q.no), e = nb[k] || {n: 0}; e.n++; e.last = now; e.ok = false; nb[k] = e; }
  }
  saveNote(nb);
  const lScore = scaled("L", l, lN), rScore = scaled("R", r, rN);
  const att = {id: String(Date.now()), tid: TID, testLabel: DATA._label, vid: T.id, modeName: T.name, date: now,
    lRaw: l, lN, rRaw: r, rN, lScore, rScore, total: lScore + rScore, parts, answers: S.answers, flags: S.flags,
    minutes: Math.round((Date.now() - S.started) / 60000)};
  const h = loadHist(); h.push(att); saveHist(h);
  const wasSim = S.sim; S = null; setHud(false); simBar(null);
  if (SHELL) SHELL.setExamActive(false);
  if (wasSim) return simCongrats(att.id);
  go("#/result/" + att.id);
}

/* ---------- results ---------- */
function barColor(p) { return p >= 0.8 ? "#16a34a" : p >= 0.6 ? "#1d6fb8" : p >= 0.4 ? "#f59e0b" : "#dc2626"; }
function renderResult(aid) {
  setHud(false);
  const a = loadHist().find(x => x.id === aid);
  if (!a) return renderHome();
  if (a.tid && TESTS[a.tid] && a.tid !== TID) selectTest(a.tid);
  const parts = Object.keys(a.parts).sort().map(p => {
    const {c, n} = a.parts[p]; const pct = c / n;
    return `<div class="bar"><span>${PART_ZH[p]}</span><span class="track"><i style="width:${pct * 100}%;background:${barColor(pct)}"></i></span><span>${c}/${n} · ${Math.round(pct * 100)}%</span></div>`;
  }).join("");
  const weakest = Object.keys(a.parts).sort((x, y) => a.parts[x].c / a.parts[x].n - a.parts[y].c / a.parts[y].n)[0];
  const both = a.lN && a.rN;
  app.innerHTML = `<div class="card hero"><div class="eyebrow">Results</div><h1>${t("resultTitle")}</h1>
   <p class="muted">${esc(modeNameOf(a))} · ${new Date(a.date).toLocaleString(loc())} · ${t("usedMin", a.minutes)}</p>
   <div class="scorebig">
    ${a.lN ? `<div><small>${t("lLabel")}</small><div class="n">${a.lScore}</div><small>${t("correctN", a.lRaw, a.lN)}</small></div>` : ""}
    ${a.rN ? `<div><small>${t("rLabel")}</small><div class="n">${a.rScore}</div><small>${t("correctN", a.rRaw, a.rN)}</small></div>` : ""}
    ${both ? `<div class="total"><small>${t("totalEst")}</small><div class="n">${a.total}</div><small>${a.total >= 950 ? "950+ ✅" : t("gap950", 950 - a.total)}</small></div>` : ""}
   </div>
   <div class="estimate">${t("estimateNote")}</div></div>
  <div class="card bars"><h2>${t("partRate")}</h2>${parts}
   <p class="muted">${t("weakest")}<b>${PART_ZH[weakest]}</b></p></div>
  <div class="card"><div class="row"><a class="btn" href="#/review/${a.id}">${t("viewReview")}</a><a class="btn ghost" href="#/intro/${a.vid}">${t("retake")}</a></div>
   <div class="row" style="margin-top:10px"><a class="btn ghost" href="#/notebook">${t("nbTitle")}</a><a class="btn ghost" href="#/">${t("homeBtn")}</a></div></div>
  ${historyCard()}`;
  const c = $("#clearHist"); if (c) c.onclick = e => { e.preventDefault(); if (confirm(t("confirmClearHist"))) { localStorage.removeItem(HKEY); go("#/"); } };
}

/* ---------- review / notebook shared ---------- */
function scriptHTML(g) { return g.script.map(x => `<p><span class="spk">${esc(x.spk)}:</span> ${esc(x.text)}</p>`).join(""); }
function ctxHTML(g, aid) {
  if (g.sec === "L") return `${g.part === 1 ? photoReviewHTML(g) : ""}${gfxHTML(g)}
    <details ${g.part <= 2 ? "open" : ""}><summary>${t("listenScript")}</summary><div class="aud" data-p="${g.audio[0]}" data-i="${g.audio[1]}"><button class="btn small ghost loadA">${t("loadAudio")}</button></div><div class="script">${scriptHTML(g)}</div></details>`;
  return `<details><summary>${t("viewPassage", g.questions[0].no + (g.questions.length > 1 ? "–" + g.questions.at(-1).no : ""))}</summary>${docsHTML(g)}</details>`;
}
function bindAudioButtons(root) {
  root.querySelectorAll(".aud").forEach(d => {
    const b = d.querySelector(".loadA"); if (!b) return;
    b.onclick = async () => {
      const p = +d.dataset.p, i = +d.dataset.i;
      b.disabled = true; b.textContent = t("decryptingAudio");
      try { await AudioStore.ensure(p); d.innerHTML = `<audio controls preload="auto" src="${AudioStore.url([p, i])}"></audio>`; d.querySelector("audio").play().catch(() => {}); }
      catch { b.disabled = false; b.textContent = t("loadFailRetry"); }
    };
  });
}
function qCard(q, g, mine, extraTop = "", extraBottom = "") {
  const ok = mine === q.answer;
  const opts = q.options.map((o, i) => `<div class="opt${i === q.answer ? " correct" : ""}${i === mine && !ok ? " wrong" : ""}"><b>${LET[i]}</b><span>${o === null ? t("listenOpt") : inline(o)}</span></div>`).join("");
  return `<div class="qtext"><span class="qno">${q.no}.</span>${q.q ? inline(q.q) : (g.part === 6 ? t("p6Prompt") : g.part === 1 ? t("p1Prompt") : g.part === 2 ? t("p2Prompt") : "")}</div>
    ${extraTop}<div class="opts">${opts}</div>${extraBottom}
    <div class="exp" lang="${window.I18N.lang === "ja" && q.exp_ja ? "ja" : "zh-CN"}">💡 ${esc(pick(q, "exp"))}${q.vocab ? `<div class="vocab">${t("vocab")}${esc(pick(q, "vocab"))}</div>` : ""}${g.sec === "R" ? `<div class="srcnote">${t("aiNoteR")}</div>` : (t("aiNoteL") ? `<div class="srcnote">${t("aiNoteL")}</div>` : "")}</div>`;
}
function renderReview(aid, filter = "all") {
  setHud(false);
  const a = loadHist().find(x => x.id === aid);
  if (a && a.tid && TESTS[a.tid] && a.tid !== TID) selectTest(a.tid);
  if (!a || !DATA.variants[a.vid]) return renderHome();
  const test = buildVariant(a.vid);
  const qs = allQuestions(test);
  const wrong = qs.filter(x => a.answers[x.q.no] !== x.q.answer).length;
  const flagged = qs.filter(x => a.flags && a.flags[x.q.no]).length;
  let html = `<div class="card">${window.I18N.switchHTML()}<h1>${t("reviewTitle")}</h1><div class="tabs">
    <button data-f="all" class="${filter === "all" ? "on" : ""}">${t("tabAll", qs.length)}</button>
    <button data-f="wrong" class="${filter === "wrong" ? "on" : ""}">${t("tabWrong", wrong)}</button>
    <button data-f="flag" class="${filter === "flag" ? "on" : ""}">${t("tabFlag", flagged)}</button>
    ${a.lN ? `<button data-f="L" class="${filter === "L" ? "on" : ""}">${t("tabL")}</button>` : ""}
    ${a.rN ? `<button data-f="R" class="${filter === "R" ? "on" : ""}">${t("tabR")}</button>` : ""}</div>
    <a href="#/result/${a.id}" class="muted">${t("backResult")}</a></div>`;
  let lastG = null;
  for (const {q, g, s} of qs) {
    const mine = a.answers[q.no], ok = mine === q.answer;
    if (filter === "wrong" && ok) continue;
    if (filter === "flag" && !(a.flags && a.flags[q.no])) continue;
    if ((filter === "L" || filter === "R") && s.id !== filter) continue;
    let ctx = "";
    if (g !== lastG) { ctx = (g.part === 5 && g.sec === "R") ? "" : ctxHTML(g); lastG = g; }
    html += `<div class="card rv${ok ? "" : " ng"}"><div class="qhead"><span class="tag">${PART_ZH[g.part]}</span>
      <span class="status ${ok ? "ok" : "ng"}">${ok ? t("stOk") : mine === undefined ? t("stNone") : t("stNg")}</span></div>
      ${ctx}${qCard(q, g, mine, "", `<p class="muted">${t("yourAns")}<b>${mine === undefined ? t("noAns") : LET[mine]}</b> · ${t("correctAns")}<b>${LET[q.answer]}</b></p>`)}</div>`;
  }
  app.innerHTML = html;
  bindAudioButtons(app);
  app.querySelectorAll(".tabs button").forEach(b => b.onclick = () => renderReview(aid, b.dataset.f));
  bindLang(() => { const y = window.scrollY; renderReview(aid, filter); window.scrollTo(0, y); });
}
function renderNotebook(filter = "all") {
  setHud(false);
  const nb = loadNote();
  const mine = Object.keys(nb).filter(k => !nb[k].ok && noteNo(k) !== null);   // current test only
  const all = mine.map(noteNo);
  const items = all.slice().sort((x, y) => x - y).filter(n => filter === "all" || (filter === "L" ? n <= 100 : n > 100));
  let html = `<div class="card">${window.I18N.switchHTML()}<h1>${t("nbTitle")} <small class="muted">${esc(DATA._label)}</small></h1>
   <p class="muted">${t("nbDesc")}</p>
   <div class="tabs"><button data-f="all" class="${filter === "all" ? "on" : ""}">${t("tabAll", all.length)}</button>
   <button data-f="L" class="${filter === "L" ? "on" : ""}">${t("tabL")} ${all.filter(n => +n <= 100).length}</button>
   <button data-f="R" class="${filter === "R" ? "on" : ""}">${t("tabR")} ${all.filter(n => +n > 100).length}</button></div>
   <div class="row"><a class="btn ghost small" href="#/">${t("homeBack")}</a>${all.length ? `<button class="btn ghost small" id="nbClear">${t("nbClear")}</button>` : ""}</div></div>`;
  if (!items.length) html += `<div class="card"><p class="muted">${t("nbEmpty")}</p></div>`;
  for (const n of items) {
    const f = groupOfQ(n); if (!f) continue;
    const {g, q} = f;
    const ctx = (g.part === 5) ? "" : ctxHTML(g);
    const e = nb[nkey(n)];
    html += `<div class="card rv ng"><div class="qhead"><span class="tag">${PART_ZH[g.part]}</span><span class="status ng">${t("wrongTimes", e.n)}</span></div>
      ${ctx}${qCard(q, g, undefined, "", `<p class="muted">${t("correctAns")}<b>${LET[q.answer]}</b> · ${t("lastTime")}${new Date(e.last).toLocaleDateString(loc())}</p>`)}
      <button class="btn small" data-ok="${nkey(n)}">${t("mastered")}</button></div>`;
  }
  app.innerHTML = html;
  bindAudioButtons(app);
  app.querySelectorAll(".tabs button").forEach(b => b.onclick = () => renderNotebook(b.dataset.f));
  bindLang(() => renderNotebook(filter));
  app.querySelectorAll("[data-ok]").forEach(b => b.onclick = () => { const x = loadNote(); x[b.dataset.ok].ok = true; saveNote(x); b.closest(".card").remove(); });
  const c = $("#nbClear"); if (c) c.onclick = () => { if (confirm(t("confirmNbClear"))) { const x = loadNote(); for (const k of Object.keys(x)) if (noteNo(k) !== null) delete x[k]; saveNote(x); renderNotebook(filter); } };
}


/* ---------- multi-test picker ---------- */
function testPicker() {
  const ids = Object.keys(TESTS); if (ids.length < 2) return "";
  return `<div class="card"><h2>${t("pickerTitle")}</h2><div class="tabs">${ids.map(id => `<button data-tid="${id}" class="${id === TID ? "on" : ""}">${esc(TESTS[id]._label)}</button>`).join("")}</div></div>`;
}
function bindTestPicker(rerender) { app.querySelectorAll("[data-tid]").forEach(b => b.onclick = () => { selectTest(b.dataset.tid); rerender(); }); }
function renderHistoryPage() {
  setHud(false);
  app.innerHTML = `${historyCard()}<div class="card"><a class="btn ghost" href="#/">${t("backBack")}</a></div>`;
  const c = $("#clearHist"); if (c) c.onclick = e => { e.preventDefault(); if (confirm(t("confirmClearHist"))) { localStorage.removeItem(HKEY); renderHistoryPage(); } };
}

/* ---------- IP-online style simulation (desktop exe + web 全屏仿真模式) ---------- */
const simbarEl = $("#simbar");
function simBar(html) {             // null = hide the bottom bar
  if (html === null) { simbarEl.classList.add("hidden"); simbarEl.innerHTML = ""; return; }
  simbarEl.classList.remove("hidden"); simbarEl.innerHTML = html;
}
function enterSim() {
  SIM = true; sessionStorage.setItem("ets950.sim", "1");
  document.body.classList.add("sim");
  const el = document.documentElement, rq = el.requestFullscreen || el.webkitRequestFullscreen;
  if (rq && !SHELL) { try { const r = rq.call(el, {navigationUI: "hide"}); if (r && r.catch) r.catch(() => {}); } catch {} }
  requestWakeLock();
  go("#/");
}
function exitSim() {
  SIM = false; sessionStorage.removeItem("ets950.sim"); document.body.classList.remove("sim"); simBar(null);
  if (document.fullscreenElement && document.exitFullscreen) document.exitFullscreen().catch(() => {});
  else if (document.webkitFullscreenElement && document.webkitExitFullscreen) document.webkitExitFullscreen();
  go("#/");
}
function simConfirmExit() {
  const inExam = S && !S.done;
  overlay.dataset.dismiss = "0";
  showOverlay(`<h2>${inExam ? t("endExamQ") : t("exitQ")}</h2><p class="muted">${inExam ? t("endExamSub") : t("exitSub")}</p>
   <div class="row"><button class="btn ghost" id="cxNo">${inExam ? t("contExam") : t("cancel")}</button><button class="btn warn" id="cxYes">${inExam ? t("endExam") : t("exitBtn")}</button></div>`);
  $("#cxNo").onclick = hideOverlay;
  $("#cxYes").onclick = () => { hideOverlay(); abortExam(); if (SHELL) SHELL.quit(); else exitSim(); };
}
if (SHELL) {
  SHELL.onCloseRequest(() => simConfirmExit());
  document.addEventListener("contextmenu", e => e.preventDefault());
  document.addEventListener("dragstart", e => e.preventDefault());
}
document.addEventListener("fullscreenchange", () => {
  if (SIM && !SHELL && !document.fullscreenElement && S && !S.done) {
    const b = document.createElement("button"); b.className = "btn small refs"; b.textContent = t("refs");
    b.onclick = () => { b.remove(); document.documentElement.requestFullscreen().catch(() => {}); }; document.body.appendChild(b);
  }
});
/* header volume control */
$("#volBtn").onclick = e => {
  e.stopPropagation();
  const pop = $("#volPop"); pop.classList.toggle("hidden");
  $("#volRange").value = Math.round(AudioEng.vol * 100);
};
$("#volRange").oninput = e => AudioEng.setVolume(e.target.value / 100);
document.addEventListener("click", e => { const pop = $("#volPop"); if (!pop.contains(e.target) && !e.target.closest("#volBtn")) pop.classList.add("hidden"); });

function simHome() {
  document.body.classList.add("sim"); setHud(false); simBar(null);
  const nbo = loadNote(), nb = Object.keys(nbo).filter(k => !nbo[k].ok && noteNo(k) !== null).length;
  app.innerHTML = `<div class="simpanel">
   ${window.I18N.switchHTML()}<h1>TOEIC® Listening &amp; Reading Test <small>${esc(t("simHomeSub", dTitle(DATA)))}</small></h1>
   ${testPicker()}
   <p>${t("simFlow")}</p>
   <button class="btn block big" id="simStart">${t("simStart")}</button>
   <div class="row" style="margin-top:12px"><a class="btn ghost" href="#/notebook">${t("simNb", nb)}</a><a class="btn ghost" href="#/history">${t("simHist")}</a></div>
   <div class="row" style="margin-top:12px">${SHELL ? `<button class="btn ghost" id="simQuit">${t("exitBtn")}</button>` : `<button class="btn ghost" id="simLeave">${t("simLeave")}</button>`}</div></div>`;
  bindTestPicker(simHome); bindLang(simHome);
  $("#simStart").onclick = () => { AudioEng.unlock(); simSound(); };
  if ($("#simQuit")) $("#simQuit").onclick = () => simConfirmExit();
  if ($("#simLeave")) $("#simLeave").onclick = () => exitSim();
}
function simSound() {
  app.innerHTML = `<div class="simpanel"><h2>Testing the Volume <small>${t("sndSub")}</small></h2>
   <p>Put on your headphones. You will hear a sample recording. Adjust the volume until you can hear it clearly, then click <b>Next</b>.</p>
   <p class="muted">${t("sndNote")}</p>
   <div class="volrow">🔈 <input type="range" id="sndVol" min="0" max="100" value="${Math.round(AudioEng.vol * 100)}"> 🔊 <b id="sndPct">${Math.round(AudioEng.vol * 100)}%</b></div>
   <p><button class="btn ghost" id="sndPlay">${t("sndPlay")}</button> <span id="sndState" class="muted"></span></p></div>`;
  simBar(`<span></span><button class="btn" id="simNext">Next ›</button>`);
  const play = async () => {
    $("#sndState").textContent = t("sndPlaying");
    try { await AudioEng.play("audio/soundcheck.mp3", () => { const e = $("#sndState"); if (e) e.textContent = t("sndEnded"); }); }
    catch { $("#sndState").textContent = t("sndFail"); }
  };
  $("#sndVol").oninput = e => { AudioEng.setVolume(e.target.value / 100); $("#sndPct").textContent = e.target.value + "%"; };
  $("#sndPlay").onclick = play; play();
  $("#simNext").onclick = () => { AudioEng.stop(); simAgree(); };
}
function simAgree() {
  app.innerHTML = `<div class="simpanel"><h2>Test Rules <small>${t("rulesSub")}</small></h2>
   <ol class="rules">
    <li>${t("rule1")}<br><span class="muted">Do not use dictionaries, notes, phones, or any other materials.</span></li>
    <li>${t("rule2")}<br><span class="muted">Each recording is played only once.</span></li>
    <li>${t("rule3")}<br><span class="muted">You cannot return to a previous unit.</span></li>
    <li>${t("rule4")}<br><span class="muted">The test ends automatically when time runs out.</span></li>
    <li>${t("rule5")}<br><span class="muted">Practice only; scores are estimates.</span></li>
   </ol>
   <p>${t("agreeQ")}</p>
   <label class="radio"><input type="radio" name="agree" value="1"> ${t("yes")}</label>
   <label class="radio"><input type="radio" name="agree" value="0"> ${t("no")}</label></div>`;
  simBar(`<button class="btn ghost" id="simBack">‹ Back</button><button class="btn" id="simNext" disabled>Next ›</button>`);
  app.querySelectorAll("[name=agree]").forEach(r => r.onchange = () => { $("#simNext").disabled = r.value !== "1" || !r.checked; });
  $("#simBack").onclick = simSound;
  $("#simNext").onclick = simOverview;
}
function simOverview() {
  app.innerHTML = `<div class="simpanel"><h2>Test Overview <small>${t("ovSub")}</small></h2>
   <table class="fmt"><tr><th>Section</th><th>${t("ovFull")}</th><th>${t("ovIP")}</th></tr>
    <tr><td>${t("ovListen")}<br><span class="muted">Part 1–4</span></td><td>${t("ovL1")}</td><td>${t("ovL2")}</td></tr>
    <tr><td>${t("ovRead")}<br><span class="muted">Part 5–7</span></td><td>${t("ovR1")}</td><td>${t("ovR2")}</td></tr></table>
   <ul class="rules"><li>${t("ov1")}</li>
    <li>${t("ov2")}</li>
    <li>${t("ov3")}</li></ul></div>`;
  simBar(`<button class="btn ghost" id="simBack">‹ Back</button><button class="btn" id="simNext">Next ›</button>`);
  $("#simBack").onclick = simAgree; $("#simNext").onclick = simMode;
}
function simMode() {
  const V = DATA.variants, main = ["ip", "full"].filter(k => V[k]), practice = ["L", "R"].filter(k => V[k]);
  const chips = k => {
    if (k === "ip") return `<div class="mode-meta"><span class="chip">⏱ 60 min</span><span class="chip">90 Q</span><span class="chip">L 45 · R 45</span></div>`;
    if (k === "full") return `<div class="mode-meta"><span class="chip">⏱ ~120 min</span><span class="chip">200 Q</span><span class="chip">L 100 · R 100</span></div>`;
    if (k === "L") return `<div class="mode-meta"><span class="chip">🎧 ~45 min</span></div>`;
    if (k === "R") return `<div class="mode-meta"><span class="chip">📖 75 min</span></div>`;
    return "";
  };
  app.innerHTML = `<div class="simpanel"><h2>Select Test Mode <small>${t("modeSub")}</small></h2>
   <p class="muted">${t("modeMainHint")}</p>
   <div class="mode-grid main">${main.map((k, i) => `<label class="mode-card primary"><input type="radio" name="mode" value="${k}" ${i === 0 ? "checked" : ""} style="accent-color:#1a6bb5;margin:0 8px 8px 0"> <b>${esc(vName(V[k]))}</b>${chips(k)}<p class="muted" style="margin:6px 0 0">${esc(vDesc(V[k]))}</p></label>`).join("")}</div>
   ${practice.length ? `<h3 class="mode-sec">${t("practiceModes")}</h3><div class="mode-grid">${practice.map(k => `<label class="mode-card"><input type="radio" name="mode" value="${k}" style="accent-color:#1a6bb5;margin:0 8px 8px 0"> <b>${esc(vName(V[k]))}</b>${chips(k)}<p class="muted" style="margin:6px 0 0">${esc(vDesc(V[k]))}</p></label>`).join("")}</div>` : ""}</div>`;
  simBar(`<button class="btn ghost" id="simBack">‹ Back</button><button class="btn" id="simNext">${t("startGo")}</button>`);
  $("#simBack").onclick = simOverview;
  $("#simNext").onclick = () => { const v = app.querySelector("[name=mode]:checked").value; AudioEng.unlock(); startExam(buildVariant(v)); };
}
function simReadingIntro() {
  S.phase = "R-gate"; hudSection.textContent = t("hudReadingSim"); showReadingTimer(S.runits[0].time); $("#hudQ").textContent = "";
  app.innerHTML = `<div class="simpanel"><h2>Reading Test <small>${t("rSub")}</small></h2>
   <p>In the Reading test, you will read a variety of texts and answer several types of reading comprehension questions. Answer as many questions as possible within the time allowed.</p>
   <p class="muted">${S.lgroups.length ? t("lDone") : ""}${t("rInfo", S.runits.map(u => t("rUnitSlash", u.name, Math.round(u.time / 60), u.groups.reduce((a, g) => a + g.questions.length, 0))).join(t("listSep")))}</p></div>`;
  simBar(`<span></span><button class="btn" id="simNext">Next ›</button>`);
  $("#simNext").onclick = () => { requestWakeLock(); if (!S.tick) S.tick = setInterval(tick, 250); startReadingUnit(0); };
}
function simUnitDir() {
  const u = S.runits[S.ru];
  S.ritems = u.groups.flatMap(g => g.questions.map(q => ({q, g})));
  S.phase = "R-dir";
  const [a, b] = unitRange(u);
  $("#hudQ").textContent = "Directions";
  hudSection.textContent = `Reading · Questions ${a}–${b} of ${S.rTotal}`;
  app.innerHTML = `<div class="simpanel"><h2>Reading · ${esc(u.name)}</h2>
   <h3>Part 5 · Incomplete Sentences ${t("p5Sub")}</h3>
   <p><b>Directions:</b> Each sentence below is missing a word or phrase. Four answer choices are given. Select the choice that best completes the sentence, then click on your answer.</p>
   <p class="muted">${t("unitInfo", S.ritems.length, Math.round(u.time / 60))} · ${t("rRange", a, b, S.rTotal)}</p></div>`;
  simBar(`<span></span><button class="btn" id="simNext">Next ›</button>`);
  $("#simNext").onclick = () => simQ(0);
}
const SIM_DIR = new Proxy({}, {get: (_, p) => t("simDir" + String(p))});
function simQ(i) {
  S.ri = i; S.phase = "R";
  const {q, g} = S.ritems[i], prev = S.ritems[i - 1];
  const newPart = g.part !== 5 && (!prev || prev.g.part !== g.part);
  const hasDoc = g.docs && g.docs.length;
  const u = S.runits[S.ru];
  const [a, b] = unitRange(u);
  const dno = S.rDisp[q.no] || q.no;
  $("#hudQ").textContent = `Question ${dno}`;
  hudSection.textContent = `Reading · Questions ${a}–${b} of ${S.rTotal}`;
  app.innerHTML = `<div class="simq${hasDoc ? " split" : ""}">
   ${hasDoc ? `<div class="simdoc">${newPart ? `<div class="dirnote">${SIM_DIR[g.part]}</div>` : ""}${docsHTML(g)}</div>` : ""}
   <div class="simask">
    <div class="qhead"><div class="qnum">Question ${dno} <span class="muted">(${i + 1} / ${S.ritems.length})</span></div>
     <label class="mark"><input type="checkbox" id="markQ" ${S.flags[q.no] ? "checked" : ""}> ${t("markLbl")}</label></div>
    <div class="qtext">${q.q ? inline(q.q) : t("simBlank", dno)}</div>
    ${optsHTML(q, true)}</div></div>`;
  bindOpts(app);
  $("#markQ").onchange = e => { S.flags[q.no] = e.target.checked; };
  simBar(`<button class="btn ghost" id="simBack" ${i === 0 ? "disabled" : ""}>‹ Back</button><label class="mark simbar-mark"><input type="checkbox" id="markQ2" ${S.flags[q.no] ? "checked" : ""}> Mark item for review</label><button class="btn ghost" id="simRev">Review</button><button class="btn" id="simNext">Next ›</button>`);
  const syncMark = e => { S.flags[q.no] = e.target.checked; const o = $("#markQ"); if (o) o.checked = e.target.checked; };
  $("#markQ2").onchange = syncMark;
  $("#simBack").onclick = () => simQ(i - 1);
  $("#simRev").onclick = () => simReview("all");
  $("#simNext").onclick = () => i + 1 < S.ritems.length ? simQ(i + 1) : simReview("all");
  window.scrollTo(0, 0); const sd = app.querySelector(".simdoc"); if (sd) sd.scrollTop = 0;
}
function simReview(filter = "all") {
  S.phase = "R-rev";
  const u = S.runits[S.ru], items = S.ritems;
  const unItems = items.filter(x => S.answers[x.q.no] === undefined);
  const flItems = items.filter(x => S.flags[x.q.no]);
  const un = unItems.length, fl = flItems.length;
  const [a, b] = unitRange(u);
  $("#hudQ").textContent = "Review";
  hudSection.textContent = `Reading · Questions ${a}–${b} of ${S.rTotal}`;
  const shown = filter === "marked" ? items.filter(x => S.flags[x.q.no])
              : filter === "unanswered" ? items.filter(x => S.answers[x.q.no] === undefined)
              : items;
  const status = x => {
    const done = S.answers[x.q.no] !== undefined, mark = !!S.flags[x.q.no];
    return `<span class="rv-ico">${done ? "✓" : "!"}</span>${mark ? '<span class="rv-flag">⚑</span>' : ""}`;
  };
  app.innerHTML = `<div class="simpanel"><h2>Review · ${esc(u.name)}</h2>
   <p class="muted">${t("revNote", un, fl)}</p>
   <div class="revfilters">
    <button class="btn small${filter === "all" ? "" : " ghost"}" data-f="all">${t("revAll")}</button>
    <button class="btn small${filter === "marked" ? "" : " ghost"}" data-f="marked">${t("revMarked")} (${fl})</button>
    <button class="btn small${filter === "unanswered" ? "" : " ghost"}" data-f="unanswered">${t("revUnanswered")} (${un})</button>
   </div>
   <table class="revtable"><thead><tr><th>#</th><th>${t("revStatus")}</th><th></th></tr></thead>
   <tbody>${shown.length ? shown.map((x) => {
     const idx = items.indexOf(x); const dno = S.rDisp[x.q.no] || x.q.no;
     const done = S.answers[x.q.no] !== undefined;
     return `<tr class="rrow${done ? " done" : " miss"}${S.flags[x.q.no] ? " flag" : ""}" data-i="${idx}"><td><b>${dno}</b></td><td>${status(x)} <span class="muted">${done ? "Answered" : "Not Answered"}</span></td><td>›</td></tr>`;
   }).join("") : `<tr><td colspan="3" class="muted">${t("revEmpty")}</td></tr>`}</tbody></table></div>`;
  app.querySelectorAll(".revfilters [data-f]").forEach(b => b.onclick = () => simReview(b.dataset.f));
  app.querySelectorAll(".rrow").forEach(b => b.onclick = () => simQ(+b.dataset.i));
  const last = lastUnit();
  simBar(`<button class="btn ghost" id="simRet">${t("simRet")}</button><button class="btn ${last ? "warn" : ""}" id="simEnd">${last ? t("finishTest") : t("nextUnit")}</button>`);
  $("#simRet").onclick = () => simQ(Math.min(S.ri || 0, items.length - 1));
  $("#simEnd").onclick = () => {
    overlay.dataset.dismiss = "1";
    const unList = unItems.map(x => S.rDisp[x.q.no] || x.q.no);
    showOverlay(`<h2>${last ? t("feTitleLast") : t("feTitleUnit")}</h2>
     <p>${un ? t("feUn", un) : t("feAll")}${last ? t("noChangeAfterSubmit") : t("feUnit")}</p>
     ${un && last ? `<p class="muted">${t("unansweredList", unList.join(", "))}</p>` : ""}
     <div class="row"><button class="btn ghost" id="feNo">${t("cancel2")}</button><button class="btn warn" id="feYes">${last ? "Finish Test" : "Finish Unit"}</button></div>`);
    $("#feNo").onclick = hideOverlay;
    $("#feYes").onclick = () => { hideOverlay(); if (last) submit(); else startReadingUnit(S.ru + 1); };
  };
}

function simCongrats(aid) {
  document.body.classList.add("sim");
  app.innerHTML = `<div class="simpanel center"><div class="big">🎉</div><h1>Congratulations!</h1><p>${t("congrats")}</p><p class="muted">${t("congratsNext")}</p></div>`;
  simBar(`<span></span><button class="btn" id="simNext">Next ›</button>`);
  $("#simNext").onclick = () => { simBar(null); go("#/result/" + aid); };
}

if (DEBUG || FAST) window.__t = {get S() { return S; }, set S(v) { S = v; }, AudioEng, loadHist, FAST, ANSWER_GAP, showAnsTimer, playGroup, listenAfterGroup, startReading, listenUnitIntro, tokyoYM, tokyoMM, unlock, clearSavedPw, startExam, buildVariant, abortExam, go, simQ, simReview, get DATA() { return DATA; }};   // test hook
/* ---------- boot ---------- */
(async () => {
  if (!SIM && sessionStorage.getItem("ets950.sim") === "1") SIM = true;
  if (SIM) document.body.classList.add("sim");
  const pw = SHELL ? null : loadSavedPw();
  if (pw) {
    app.innerHTML = `<div class="card gate"><p>${t("decrypting")}</p></div>`;
    try { await unlock(pw); }
    catch (e) {
      clearSavedPw();
      const code = e && e.message;
      return renderLock(code === "BADPW" ? t("savedPwBad") : "");
    }
  }
  route();
})();

})();
