'use strict';
// FILE TỰ SINH bằng `node build.js` từ src/server.js + src/sim.js — hãy sửa trong src/ rồi build lại.
/*
 * EGO FUTSAL · server.js (v2) — chạy trên Render.
 *
 * Một cổng HTTP duy nhất phục vụ:
 *   GET /            game (tự nén brotli/gzip, ETag → 304)
 *   GET /healthz     kiểm tra sức khỏe cho Render
 *   WS  /ws          mọi tính năng online, phân loại theo tin nhắn đầu tiên:
 *       hubJoin      sảnh Ego City + hàng chờ ghép cặp (queueJoin/queueCancel)
 *       matchJoin    trận 1v1 do SERVER tính vật lý (lib/sim.js), client chỉ gửi phím/hành động
 *       h / g        phòng mã PIN: server chỉ chuyển tiếp tin giữa chủ phòng và khách
 *
 * Giảm độ trễ: vòng mô phỏng cố định 60 Hz có bù trôi thời gian, gửi trạng thái 40 Hz dưới dạng
 * khung văn bản, tắt permessage-deflate, TCP_NODELAY, bỏ gói cũ khi đường truyền nghẽn,
 * stringify một lần rồi gửi cho cả hai người chơi, giữ kết nối bằng ping/pong.
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const crypto = require('crypto');
const { performance, monitorEventLoopDelay } = require('perf_hooks');
const { WebSocketServer } = require('ws');
// ── mô phỏng trận đấu (gộp từ src/sim.js) ──
const { Match } = (() => {
  /*
   * Ego Futsal · mô phỏng trận đấu chạy trên server.
   * Cổng lại từ vòng lặp vật lý/AI của game (step, ball, shoot, passPlayer, skillApply...) để
   * bản chơi online cho cùng cảm giác với bản chơi một mình. Không phụ thuộc THREE hay DOM.
   * Trục: đội 0 (Xanh, slot 0) tấn công về phía z âm, đội 1 (Đỏ, slot 1) về phía z dương.
   */
  const HX = 34, HZ = 52, GW = 7.32, GH = 2.44, R = 0.29;
  const KN_SWAY = 36, KN_FREQ = 10.5;
  const FB_STAT = 15, SPN = 0.9, RAIN_DUR = 1.05;
  const D = 0.75; // độ khó AI: giống nhau cho cả hai đội để trận người-với-người công bằng
  
  const cl = (v, a, z) => Math.max(a, Math.min(z, v));
  const ang = (a, t, k) => a + (((t - a + 9.4248) % 6.2832) - 3.1416) * k;
  const rnd = Math.random;
  const r2 = (v) => Math.round(v * 100) / 100;
  
  // chỉ số: [tốc độ, lực sút, kỹ thuật, tranh chấp, không chiến]
  const CHAR = [
    { n: 'Kaze', s: [10, 6, 7, 5, 4] }, { n: 'Goro', s: [5, 10, 6, 6, 5] }, { n: 'Sora', s: [7, 6, 10, 4, 5] },
    { n: 'Tetsu', s: [6, 5, 4, 10, 7] }, { n: 'Haru', s: [6, 6, 5, 5, 10] }, { n: 'Mio', s: [7, 6, 7, 6, 6] },
  ];
  const SKL = { Kaze: { cd: 45, du: 30 }, Goro: { cd: 100, du: 0 }, Sora: { cd: 20, du: 0 }, Haru: { cd: 50, du: 0 }, Mio: { cd: 25, du: 7 }, Tetsu: { cd: 50, du: 0 } };
  const SORA_RAIN = { cd: 20 };
  const AX = [-3.25, -2.75, -2.25, -1.7, -1.15, -0.6, 0, 0.6, 1.15, 1.7, 2.25, 2.75, 3.25], AY = [0.55, 1.25, 1.95];
  const LAYOUT = [ // t, role, sx, sd
    [0, 'f', 0, 13.8], [0, 'f', -5, 10.5], [0, 'f', 5, 10.5], [0, 'f', 0, 6.5], [0, 'gk', 0, 1.1],
    [1, 'f', -2.2, 13.8], [1, 'f', 2.2, 13.8], [1, 'f', -5, 9], [1, 'f', 5, 9], [1, 'gk', 0, 1.1],
  ];
  
  function mkPlayer(i) {
    const [t, role, sx, sd] = LAYOUT[i];
    return {
      i, t, role, sx: sx * HX / 9, sd: sd * HZ / 15, human: false, slot: -1, stamina: 100, charIndex: -1,
      p: { x: 0, y: 0, z: 0 }, v: { x: 0, z: 0 }, a: 0, cd: 0, sl: 0, slc: 0, stun: 0, vy: 0, hd: 0, hit: 0, hold: 0, pw: 0, gx: 0, gn: 0, imm: 0,
      spin: 0, spinType: '', sa: 0, dr: { x: 0, z: 1 }, sv: { x: 0, z: 0 }, rf: null, ego: false,
      s: { spd: 7, sht: 7, tec: 7, def: 7, air: 7 },
      _skillMainCd: 0, _skillRainCd: 0, _skillBoost: 0, _haruMeteor: 0, _mioTouch: 0, _mioBallLock: false, _tetsuWall: 0, _tetsuUsed: 0,
    };
  }
  
  class Match {
    /** players: [{sel,name},{sel,name}] */
    constructor(players, opts = {}) {
      this.P = LAYOUT.map((_, i) => mkPlayer(i));
      this.b = { p: { x: 0, y: R, z: 0 }, v: { x: 0, y: 0, z: 0 }, ct: 0, cv: 0, cd: 0, fire: 0, knuckle: 0, knuckleT: 0, knucklePhase: 0, rainVolley: 0, rainPhase: 0, rainBounces: 0, soraShield: 0, soraShieldTeam: undefined };
      this.I = [{ k: 0, y: 0, sl: 0, t: 0, seq: 0 }, { k: 0, y: Math.PI, sl: 0, t: 0, seq: 0 }];
      this.now = 0; this.aiDt = 1 / 60;
      this.s0 = 0; this.s1 = 0; this.tl = opts.seconds || 180; this.gt = 0; this.ph = 'play';
      this.kteam = rnd() < 0.5 ? 0 : 1; this.klock = 0; this.lastScorer = -1; this.events = [];
      [0, 5].forEach((idx, slot) => {
        const o = this.P[idx], sel = cl((players[slot] && Number(players[slot].sel)) | 0, 0, 5);
        o.human = true; o.slot = slot; o.charIndex = sel; o.s = this.statsOf(sel);
      });
      this.P.forEach((o) => { if (!o.human) o.s = { spd: 7, sht: 7, tec: 7, def: 7, air: 7 }; });
      this.reset();
      this.ph = 'play';
    }
    statsOf(sel) { const s = CHAR[sel].s; return { spd: s[0], sht: s[1], tec: s[2], def: s[3], air: s[4] }; }
  
    // ---------- điều khiển từ người chơi ----------
    input(slot, m) {
      const I = this.I[slot]; if (!I) return;
      const seq = Number(m.seq) || 0; if (seq && seq <= I.seq && I.seq - seq < 1000) return;
      I.seq = seq; I.k = (Number(m.k) | 0) & 63; if (Number.isFinite(Number(m.y))) I.y = Number(m.y); I.t = this.now;
    }
    action(slot, m) {
      if (this.ph !== 'play') return;
      const o = this.P[slot === 0 ? 0 : 5], I = this.I[slot]; if (!o || !o.human) return;
      const yaw = Number.isFinite(Number(m.yaw)) ? Number(m.yaw) : I.y;
      if (m.action === 'slide') { I.sl = 1; return; }
      if (o.sl > 0 || o.stun > 0) { if (m.action !== 'shoot') return; }
      if (m.action === 'shoot') { I.y = yaw; this.shoot(o, cl(Number(m.charge) || 0, 0, 1), cl(Number(m.mode) | 0, 0, 3), yaw, (Number(m.k) | 0) & 63, Number(m.pitch) || 0); return; }
      if (m.action === 'pass') { this.pass(o); return; }
      if (m.action === 'skill') { this.skillApply(m.which === 'rain' ? 'rain' : 'main', o, yaw, (Number(m.k) | 0) & 63); }
    }
    removeHuman(slot) {
      const o = this.P[slot === 0 ? 0 : 5]; if (!o || !o.human) return;
      o.human = false; o.slot = -1; o.s = { spd: 7, sht: 7, tec: 7, def: 7, air: 7 }; this.I[slot].k = 0;
    }
  
    // ---------- đặt lại thế trận ----------
    reset() {
      const b = this.b;
      for (const o of this.P) {
        const dz = o.t ? 1 : -1;
        o.p.x = o.sx; o.p.y = 0; o.p.z = -dz * HZ + dz * o.sd; o.v.x = o.v.z = 0; o.a = o.t ? 0 : Math.PI;
        o.cd = 0; o.sl = o.slc = o.stun = 0; o.hit = 0; o.sv = { x: 0, z: 0 }; o.vy = o.hd = 0; o.hold = 0; o.gx = 0; o.spin = 0; o.spinType = ''; o.imm = 0; o.sa = 0;
        o._haruMeteor = 0; o._mioTouch = 0; o._mioBallLock = false; o._tetsuWall = 0; o._tetsuUsed = 0; o.stamina = 100;
      }
      b.p.x = 0; b.p.y = R; b.p.z = 0; b.v.x = b.v.y = b.v.z = 0; b.ct = b.cv = b.cd = 0; b.fire = 0; b.knuckle = b.knuckleT = b.knucklePhase = 0;
      b.rainVolley = b.rainPhase = b.rainBounces = 0; b.soraShield = 0; b.soraShieldTeam = undefined;
      for (const I of this.I) { I.k = 0; I.sl = 0; }
      this.klock = 5; this.kickerSet();
    }
    kickerSet() {
      let k = null, m = 1e9;
      for (const o of this.P) { if (o.t !== this.kteam || o.role === 'gk') continue; const d = Math.hypot(o.p.x, o.p.z); if (d < m) { m = d; k = o; } }
      if (k) { k.p.x = 0; k.p.z = (k.t ? -1 : 1) * 1.1; k.a = k.t ? 0 : Math.PI; }
    }
    koTick(dt) {
      if (this.klock <= 0) return; const b = this.b;
      this.klock -= dt; if (this.klock <= 0 || Math.hypot(b.p.x, b.p.z) > 0.5) { this.klock = 0; return; }
      for (const o of this.P) {
        if (o.t === this.kteam) continue; const s = o.t ? -1 : 1; let x = o.p.x, z = s * Math.max(0.4, o.p.z * s); const d = Math.hypot(x, z);
        if (d < 4.5) { x *= 4.5 / d; z *= 4.5 / d; }
        if (x !== o.p.x || z !== o.p.z) { o.p.x = x; o.p.z = z; o.v.x *= 0.2; o.v.z *= 0.2; }
      }
    }
    goal(t) {
      this.ph = 'goal'; this.gt = 2.8; if (t) this.s1++; else this.s0++; this.kteam = t ? 0 : 1; this.lastScorer = t;
      this.events.push({ e: 'goal', t, s0: this.s0, s1: this.s1 });
    }
    end() { this.ph = 'end'; this.events.push({ e: 'end', s0: this.s0, s1: this.s1 }); }
  
    // ---------- vòng lặp chính ----------
    step(dt) {
      this.now += dt * 1000; this.aiDt = dt;
      if (this.ph === 'goal') { this.ball(dt); this.gt -= dt; if (this.gt <= 0) { this.reset(); this.ph = 'play'; } return; }
      if (this.ph !== 'play') return;
      const P = this.P, b = this.b;
      for (const o of P) if (o.human) this.rctl(o, this.I[o.slot], dt);
      // đội nào có NPC gần bóng nhất thì NPC đó đuổi bóng, trừ khi người thật ở gần hơn
      const ch = [null, null], cd = [1e9, 1e9];
      for (const o of P) { if (o.human || o.role === 'gk') continue; const d = Math.hypot(b.p.x - o.p.x, b.p.z - o.p.z); if (d < cd[o.t]) { cd[o.t] = d; ch[o.t] = o; } }
      for (const h of P) if (h.human && h.role !== 'gk' && Math.hypot(b.p.x - h.p.x, b.p.z - h.p.z) < cd[h.t] - 1) ch[h.t] = null;
      for (const o of P) { if (!o.human) this.ai(o, dt, ch); }
      this.contact(dt);
      for (let i = 0; i < P.length; i++) for (let j = i + 1; j < P.length; j++) {
        const A = P[i], B = P[j];
        if ((A._mioTouch > 0 || B._mioTouch > 0) && A.t !== B.t) continue;
        if (A.spin > 0 || B.spin > 0) continue;
        const ex = B.p.x - A.p.x, ez = B.p.z - A.p.z, d = Math.hypot(ex, ez);
        if (d < 0.7 && d > 0) { const u = (0.7 - d) / 2 / d; A.p.x -= ex * u; A.p.z -= ez * u; B.p.x += ex * u; B.p.z += ez * u; }
      }
      this.koTick(dt); this.skTick(dt); this.ball(dt);
      this.tl -= dt; if (this.tl <= 0 && this.ph === 'play') { this.tl = 0; this.end(); }
    }
  
    // người chơi: giống rctl() của game
    rctl(o, I, dt) {
      const f = { x: Math.sin(I.y), z: -Math.cos(I.y) }, r = { x: Math.cos(I.y), z: Math.sin(I.y) }, S = o.s, k = (this.now - I.t) < 450 ? I.k : 0; o.rf = f;
      if (o.spin > 0) { const dash = o.spinType === 'rain' ? 5.2 : 2.2; this.move(o, o.dr.x * dash, o.dr.z * dash, dt, 34); return; }
      const ix = (k >> 3 & 1) - (k >> 1 & 1), iz = (k & 1) - (k >> 2 & 1), l = Math.hypot(ix, iz);
      const sprinting = !!((k & 16) && l > 0.05 && o.stamina > 0 && o.sl <= 0 && o.stun <= 0);
      if (sprinting) o.stamina = Math.max(0, o.stamina - 27 * dt); else o.stamina = Math.min(100, o.stamina + 18 * dt);
      const boost = o._skillBoost > 0 ? 1.5 : 1, mio = o._mioTouch > 0 ? 1.28 : 1, sp = (sprinting ? 1.31 : 1) * boost * mio * (6.6 + 0.28 * S.spd);
      let dx = 0, dz = 0;
      if (l) { dx = (f.x * iz + r.x * ix) / l; dz = (f.z * iz + r.z * ix) / l; if (o.sl <= 0 && o.stun <= 0) o.a = ang(o.a, Math.atan2(dx, dz), 1 - Math.exp(-12 * dt)); }
      if (I.sl) { I.sl = 0; this.slide(o, l ? dx : f.x, l ? dz : f.z); }
      if ((k & 32) && o.p.y <= 0 && o.sl <= 0 && o.stun <= 0) o.vy = 7.4 * (0.85 + 0.03 * S.air);
      this.move(o, dx * sp, dz * sp, dt, 7 + 0.4 * S.tec);
    }
    move(o, tx, tz, dt, acc) {
      if (o.sl > 0) { tx = o.sv.x * (0.4 + o.sl); tz = o.sv.z * (0.4 + o.sl); acc = 30; } else if (o.stun > 0) { tx = tz = 0; acc = 10; }
      const k = Math.min(1, acc * dt); o.v.x += (tx - o.v.x) * k; o.v.z += (tz - o.v.z) * k;
      o.p.x = cl(o.p.x + o.v.x * dt, -HX + 0.5, HX - 0.5); o.p.z = cl(o.p.z + o.v.z * dt, -HZ + 0.5, HZ - 0.5);
    }
    slide(o, dx, dz) {
      if (o.sl > 0 || o.slc > 0 || o.stun > 0) return;
      const n = Math.hypot(dx, dz) || 1, sv = 10.5 * (0.8 + 0.04 * o.s.def);
      o.sl = 0.55; o.slc = 1.7 - 0.08 * o.s.def; o.hit = 0; o.sv = { x: dx / n * sv, z: dz / n * sv }; o.a = Math.atan2(dx, dz);
    }
  
    // ---------- AI NPC (cổng từ game) ----------
    aiRun(o, k) { return k === 'gk' ? 7.6 + 2.2 * D : k === 'chase' ? 9.6 : k === 'carry' ? 9.2 : 7.8; }
    gkReach() { return 1.15 + 0.3 * D; }
    aiSpd(o, L0) { const pm = 0.7 + 0.06 * o.s.sht; o.ego = L0 > 11 && o.pw < 0.05 + 0.45 * D * D; return Math.min(56, pm * (o.ego ? 42 : 24 + 7 * D + Math.min(L0, 20) * 0.3)); }
    aiHeadX(o) { const gk = this.P.find(q => q.t !== o.t && q.role === 'gk'), s = gk ? (gk.p.x > 0 ? -1 : 1) : (rnd() < 0.5 ? -1 : 1); return s * (1.6 + rnd() * 1.4); }
    aiPlan(o, spd) {
      const b = this.b, P = this.P, dz2 = o.t ? 1 : -1, gz = dz2 * HZ, sx = b.p.x, sz = b.p.z, sy = Math.max(R, b.p.y);
      const gk = P.find(q => q.t !== o.t && q.role === 'gk'), rch = gk ? this.gkReach() : 1.3, gs = gk ? this.aiRun(gk, 'gk') : 8;
      const sg = 0.55 - 0.045 * o.s.tec, best = { sc: -9, tx: 0, ty: 1.2, sg, m: 0 }, lag = 0.2, bl = P.filter(q => q !== o && q.role !== 'gk'), aiDt = this.aiDt;
      for (const tx of AX) for (const ty of AY) {
        const dx = tx - sx, dz = gz - sz, L = Math.hypot(dx, dz); if (L < 1.5) continue;
        const T = L / spd, vy = (ty - sy + 10 * T * T + 10 * aiDt * T) / T, sig = sg * (0.35 + L / 30);
        let m = 3, pen = 0;
        if (gk) m = Math.abs(tx - gk.p.x) - rch - gs * Math.max(0, T - lag);
        for (const q of bl) {
          const u = cl(((q.p.x - sx) * dx + (q.p.z - sz) * dz) / (L * L), 0, 1), t = u * T, y = sy + vy * t - 10 * t * t;
          if (u * L > 0.8 && Math.hypot(sx + dx * u - q.p.x, sz + dz * u - q.p.z) < 0.95 && y < 2.35) { pen = 3; break; }
        }
        const risk = Math.max(0, 1.8 * sig - (GW / 2 - 0.1 - Math.abs(tx))) * 2 + Math.max(0, 1.8 * sig - (GH - 0.1 - ty)) * 2;
        const sc = Math.min(m, 2) - pen - risk - 0.01 * Math.abs(ty - 1.2);
        if (sc > best.sc) { best.sc = sc; best.tx = tx; best.ty = ty; best.m = m; }
      }
      return best;
    }
    aiShoot(o, pl, spd) {
      const b = this.b, dz2 = o.t ? 1 : -1, gz = dz2 * HZ, sx = b.p.x, sz = b.p.z, sy = Math.max(R, b.p.y), L = Math.hypot(pl.tx - sx, gz - sz);
      const sig = pl.sg * (0.35 + L / 30), rn = () => rnd() + rnd() - 1, tx = pl.tx + rn() * sig * 1.3, ty = cl(pl.ty + rn() * sig * 0.9, 0.45, 2.25);
      const dx = tx - sx, dz = gz - sz, T = Math.hypot(dx, dz) / spd;
      b.v.x = dx / T; b.v.y = (ty - sy + 10 * T * T + 10 * this.aiDt * T) / T; b.v.z = dz / T; b.ct = 0; o.cd = 0.9; o.a = Math.atan2(dx, dz); o.hold = 0;
    }
    aiPass(o) {
      const b = this.b, P = this.P, f = o.t ? 1 : -1; let best = null, bs = 2.6;
      for (const q of P) {
        if (q === o || q.t !== o.t || q.role === 'gk') continue;
        const dx = q.p.x - o.p.x, dz = q.p.z - o.p.z, L = Math.hypot(dx, dz); if (L < 4 || L > 15 || dz * f < -0.5) continue;
        let free = 9, blk = 0;
        for (const e of P) {
          if (e.t === o.t || e.role === 'gk') continue; free = Math.min(free, Math.hypot(e.p.x - q.p.x, e.p.z - q.p.z));
          const u = cl(((e.p.x - o.p.x) * dx + (e.p.z - o.p.z) * dz) / (L * L), 0, 1); if (Math.hypot(o.p.x + dx * u - e.p.x, o.p.z + dz * u - e.p.z) < 1) blk = 1;
        }
        const sc = free + dz * f * 0.15; if (!blk && sc > bs) { bs = sc; best = q; }
      }
      if (!best) return 0;
      const dx = best.p.x + best.v.x * 0.4 - b.p.x, dz = best.p.z + best.v.z * 0.4 - b.p.z, L = Math.hypot(dx, dz) || 1, s = Math.min(24, 9 + L * 0.9);
      b.v.x = dx / L * s; b.v.y = 0.8; b.v.z = dz / L * s; b.ct = 0; o.cd = 0.7; o.hold = 0; o.a = Math.atan2(dx, dz); return 1;
    }
    ai(o, dt, ch) {
      const b = this.b, P = this.P, dz2 = o.t ? 1 : -1, own = -dz2 * HZ, opp = dz2 * HZ, d = Math.hypot(b.p.x - o.p.x, b.p.z - o.p.z), isCh = o === ch[o.t];
      let tx, tz, sp2 = this.aiRun(o, 'run');
      if (!isCh || d > 2.2) o.hold = 0;
      if (o.role === 'gk') {
        const gl = own + dz2, vt = -b.v.z * dz2; let px = b.p.x * 0.6, run = 1; sp2 = this.aiRun(o, 'gk');
        if (vt > 3) {
          const tt = (gl - b.p.z) / b.v.z;
          if (tt > 0 && tt < 1.6) { if (!o.gn) o.gn = (rnd() - 0.5) * 2 * (1.1 - 0.7 * D); px = cl(b.p.x + b.v.x * tt + o.gn, -3.8, 3.8); if (tt < 0.5) run = 1.1; }
        } else o.gn = 0;
        o.gx += (px - o.gx) * (1 - Math.exp(-(4.5 + 5 * D) * dt)); tx = cl(o.gx, -3.8, 3.8); tz = gl; sp2 *= run;
        if (d < 5 && Math.abs(b.p.z - own) < 8 && vt <= 3) { tx = b.p.x; tz = b.p.z; }
      } else if (isCh) {
        sp2 = this.aiRun(o, 'chase'); const lead = Math.min(0.55, d / sp2 * 0.9); tx = b.p.x + b.v.x * lead; tz = b.p.z + b.v.z * lead;
        const bk = (b.p.z - o.p.z) * dz2 < -0.3 && b.v.z * dz2 < 4 && d < 4.5;
        if (bk) { let sd = Math.abs(b.p.x - o.p.x) > 0.3 ? Math.sign(o.p.x - b.p.x) : (o.p.x > 0 ? 1 : -1); if (Math.abs(b.p.x + sd * 2.2) > HX - 1) sd = -sd; tx = cl(b.p.x + sd * 2.2, -HX + 1, HX - 1); tz = b.p.z - dz2 * 1.2; }
        if ((b.p.z - o.p.z) * dz2 > -0.4 && d > 0.9 && d < 2.2 && rnd() < (o.t ? 0.007 + 0.01 * D : 0.012)) this.slide(o, b.p.x - o.p.x, b.p.z - o.p.z);
        if (b.p.y > 1.4 && d < 2.5 && o.p.y <= 0 && rnd() < 0.08) o.vy = 7.2;
        if (!bk && d < 1.3 && b.p.y < 1.6) {
          const L0 = Math.hypot(b.p.x, opp - b.p.z); if (!o.hold) o.pw = rnd(); o.hold += dt;
          if (L0 < 17 + 9 * D) {
            const spd = this.aiSpd(o, L0), pl = this.aiPlan(o, spd), press = P.some(q => q.t !== o.t && q.role !== 'gk' && Math.hypot(q.p.x - o.p.x, q.p.z - o.p.z) < 2.4);
            const need = (L0 < 9 ? -0.2 : L0 < 16 ? 0.15 : 0.45) - (press ? 0.4 : 0);
            if (o.cd <= 0 && o.hold > 0.3 - 0.2 * D && (pl.sc > need || o.hold > 1.6 || L0 < 4)) this.aiShoot(o, pl, spd);
            else if (press && L0 > 9 && o.cd <= 0 && o.hold > 0.25 && this.aiPass(o)) { /* đã chuyền */ }
            else { tx = o.p.x * 0.55 + pl.tx * 0.5; tz = opp; sp2 = this.aiRun(o, 'carry'); }
          } else { tx = o.p.x * 0.6; tz = opp; sp2 = this.aiRun(o, 'carry'); }
        }
      } else {
        const db = (b.p.z - own) * dz2; tz = own + dz2 * cl(o.sd + (db - HZ) * 0.6, 3, HZ * 2 - 3); tx = cl(o.sx + b.p.x * 0.3, -HX + 1.5, HX - 1.5);
      }
      const ex = tx - o.p.x, ez = tz - o.p.z, dd = Math.hypot(ex, ez) || 1, s = Math.min(sp2, dd * 3);
      this.move(o, ex / dd * s, ez / dd * s, dt, o.role === 'gk' ? 11 : 7 + 3 * D);
      if (Math.hypot(o.v.x, o.v.z) > 0.6) o.a = ang(o.a, Math.atan2(o.v.x, o.v.z), 1 - Math.exp(-10 * dt));
    }
  
    // ---------- va chạm cầu thủ - bóng, soạc, đánh đầu, thủ môn ----------
    head(o, dx, dz, pw) {
      const b = this.b, n = Math.hypot(dx, dz) || 1, hy = b.p.y - o.p.y, meteor = o._haruMeteor > 0 && o.charIndex === 4, k = pw * (0.8 + 0.04 * o.s.air) * (meteor ? 1.75 : 1);
      b.v.x = dx / n * k * (meteor ? 1.18 : 1); b.v.y = meteor ? -1.0 : (hy > 1.9 ? -1.5 : 2.2); b.v.z = dz / n * k * (meteor ? 1.18 : 1); b.ct = 0; o.cd = 0.45; o.hd = 0.35;
      if (meteor) o._haruMeteor = 0;
    }
    gkHit(o) { const b = this.b; b.v.x = (rnd() - 0.5) * 14; b.v.y = 3; b.v.z = (o.t ? 1 : -1) * 18; b.ct = 0; b.fire = 0; b.knuckle = 0; b.knuckleT = 0; o.cd = 0.6; }
    contact(dt) {
      const P = this.P, b = this.b;
      const spinner = P.find(q => q.human && q.spin > 0) || null, shieldTeam = b.soraShieldTeam === undefined ? 0 : b.soraShieldTeam;
      for (const o of P) {
        o.cd -= dt; o._haruMeteor = Math.max(0, o._haruMeteor - dt); o._mioTouch = Math.max(0, o._mioTouch - dt); if (o._mioTouch <= 0) o._mioBallLock = false; o._tetsuWall = Math.max(0, o._tetsuWall - dt);
        const ex = b.p.x - o.p.x, ez = b.p.z - o.p.z, d = Math.hypot(ex, ez);
        o.sl -= dt; o.slc -= dt; o.stun -= dt; o.hd -= dt; o.imm -= dt;
        if (o.p.y > 0 || o.vy > 0) { o.vy -= 20 * dt; o.p.y = Math.max(0, o.p.y + o.vy * dt); if (o.p.y <= 0) o.vy = 0; }
        if (o.sl > 0 && !o.hit) {
          let h = 0;
          if (!(b.soraShield > 0 && o.t !== shieldTeam) && !P.some(q => q._mioTouch > 0 && q.t !== o.t && Math.hypot(q.p.x - o.p.x, q.p.z - o.p.z) < 1.35) && d < 1.3 && b.p.y < 1) { b.v.x = o.sv.x * 0.9; b.v.y = 1.5; b.v.z = o.sv.z * 0.9; b.ct = 0; h = 1; }
          for (const q of P) if (q.t !== o.t && q.role !== 'gk' && q.sl <= 0 && !(q.imm > 0) && !(q._mioTouch > 0) && Math.hypot(q.p.x - o.p.x, q.p.z - o.p.z) < 1.1) { q.stun = 0.8 * (0.8 + 0.04 * o.s.def) * (1.35 - 0.07 * q.s.def); q.cd = 0.8; h = 1; }
          if (h) o.hit = 1;
        }
        if (o.role === 'gk') { if (d < this.gkReach() && b.p.y < 2.2 && o.cd <= 0) this.gkHit(o); continue; }
        if (b.soraShield > 0 && o.t !== shieldTeam) {
          if (spinner && Math.hypot(o.p.x - spinner.p.x, o.p.z - spinner.p.z) < 1.55 && o.stun <= 0) {
            const sx = o.p.x - spinner.p.x, sz = o.p.z - spinner.p.z, side = Math.sign(sx * spinner.dr.z - sz * spinner.dr.x) || 1;
            o.stun = 0.78; o.cd = Math.max(o.cd, 0.8); o.v.x += spinner.dr.x * 1.3 + spinner.dr.z * side * 2.2; o.v.z += spinner.dr.z * 1.3 - spinner.dr.x * side * 2.2;
          }
          continue;
        }
        const phantom = P.find(q => q._mioTouch > 0 && q.t !== o.t && Math.hypot(b.p.x - q.p.x, b.p.z - q.p.z) < 1.35);
        if (phantom && d < 1.15) { if (o.stun <= 0) { const sx = o.p.x - phantom.p.x, sz = o.p.z - phantom.p.z, L = Math.hypot(sx, sz) || 1; o.v.x += sx / L * 1.1; o.v.z += sz / L * 1.1; } continue; }
        if (o._tetsuWall > 0) {
          for (const q of P) if (q.t !== o.t && q.role !== 'gk' && q.stun <= 0 && Math.hypot(q.p.x - o.p.x, q.p.z - o.p.z) < 1.35) { const sx = q.p.x - o.p.x, sz = q.p.z - o.p.z, L = Math.hypot(sx, sz) || 1; q.stun = 0.48; q.v.x += sx / L * 2.5; q.v.z += sz / L * 2.5; }
          if (!o._tetsuUsed && d < 1.55 && b.p.y < 1.35) { const fx = Math.sin(o.a), fz = Math.cos(o.a); b.p.x = o.p.x + fx * 0.72; b.p.z = o.p.z + fz * 0.72; b.p.y = R; b.v.x = fx * 8.2; b.v.y = 1.0; b.v.z = fz * 8.2; b.ct = 0; b.cv = 0; b.knuckle = 0; o._tetsuUsed = 1; }
          continue;
        }
        if (b.fire > 0 && Math.hypot(b.v.x, b.v.z) > 22) { if (o.t !== (b.fireTeam | 0) && d < 1 && b.p.y < 1.8 && o.stun <= 0) { o.stun = 0.9; o.cd = 0.8; o.v.x *= 0.2; o.v.z *= 0.2; } continue; }
        const meteorHead = o._haruMeteor > 0 && o.charIndex === 4 && d < 0.95 && Math.abs(b.p.y - (o.p.y + 1.6)) < 0.82;
        if (!(o.human && b.rainVolley > 0) && (meteorHead || (d < 0.7 + 0.05 * o.s.air && o.cd <= 0 && o.sl <= 0 && o.stun <= 0 && b.p.y - o.p.y > 1.15 && b.p.y - o.p.y < 2.4))) {
          const f = o.rf || { x: 0, z: -1 };
          this.head(o, o.human ? f.x : this.aiHeadX(o) - o.p.x, o.human ? f.z : (o.t ? HZ : -HZ) - o.p.z, o.human ? 12 + Math.min(8, Math.hypot(b.v.x, b.v.z) * 0.3) : 17 + rnd() * 8);
          continue;
        }
        const touchRadius = o.human ? 1.3 : 0.8;
        if (!(spinner && o !== spinner && o.t !== spinner.t && Math.hypot(o.p.x - spinner.p.x, o.p.z - spinner.p.z) < 1.5) && d < touchRadius && b.p.y < 1 && o.cd <= 0) {
          const n = d || 1; b.v.x = o.v.x * 1.15 + ex / n * 1.6; b.v.z = o.v.z * 1.15 + ez / n * 1.6; b.v.y *= 0.3;
          if (!o.human) { const af = o.t ? 1 : -1; if (b.v.z * af < 0.5) b.v.z = af * (Math.abs(b.v.z) + 1.5); }
          b.ct = 0;
        }
      }
    }
  
    // ---------- bóng ----------
    ball(dt) {
      const b = this.b, v = b.v, p = b.p;
      b.rainVolley = Math.max(0, b.rainVolley - dt); b.soraShield = Math.max(0, b.soraShield - dt); if (b.rainVolley <= 0 && b.rainPhase !== 0) b.rainPhase = 0;
      const mio = this.P.find(o => o.charIndex === 5 && o._mioTouch > 0 && o._mioBallLock);
      if (mio) {
        p.x = mio.p.x + Math.sin(mio.a) * 0.47; p.y = mio.p.y + R; p.z = mio.p.z + Math.cos(mio.a) * 0.47; v.x = mio.v.x; v.y = 0; v.z = mio.v.z;
        b.ct = b.cv = b.cd = 0; b.knuckle = b.knuckleT = 0; b.fire = 0; b.rainVolley = 0; b.rainPhase = 0; b.soraShield = 0; return;
      }
      v.y -= 20 * dt;
      if (b.knuckle > 0) {
        const speed = Math.hypot(v.x, v.z) || 1, side = Math.sin(b.knuckleT * KN_FREQ + b.knucklePhase) * KN_SWAY, nx = -v.z / speed, nz = v.x / speed;
        v.x += nx * side * dt; v.z += nz * side * dt; b.knuckle = Math.max(0, b.knuckle - dt); b.knuckleT += dt;
      } else if (b.ct > 0) {
        b.ct -= dt;
        if (b.cd > 0) b.cd -= dt; else { const s = Math.hypot(v.x, v.z) || 1, vx = v.x; v.x += -v.z / s * b.cv * dt; v.z += vx / s * b.cv * dt; }
      }
      p.x += v.x * dt; p.y += v.y * dt; p.z += v.z * dt;
      if (p.y < R) {
        p.y = R;
        if (b.rainVolley > 0 && b.rainPhase === 1 && b.rainBounces === 0 && v.y < 0) { v.y = Math.abs(v.y) * 0.62; b.rainPhase = 2; b.rainBounces = 1; v.x *= 0.88; v.z *= 0.88; b.ct = 0; b.cv = 0; }
        else if (b.rainVolley > 0 && b.rainPhase === 2 && b.rainBounces === 1) { v.y = 0; b.rainVolley = 0; b.rainPhase = 0; v.x *= 0.72; v.z *= 0.72; }
        else { if (v.y < -1.5) v.y *= -0.55; else v.y = 0; b.rainVolley = 0; b.rainPhase = 0; const k = Math.max(0, 1 - 0.7 * dt); v.x *= k; v.z *= k; }
      }
      const az = Math.abs(p.z), sg = Math.sign(p.z), mouth = Math.abs(p.x) < GW / 2 - 0.05 && p.y < GH;
      if (this.ph === 'play') { if (az > HZ && mouth) this.goal(p.z < 0 ? 0 : 1); else if (az > HZ - R && !mouth) { p.z = sg * (HZ - R); v.z *= -0.6; } }
      if (this.ph === 'goal' && az > HZ + 2 - R) { p.z = sg * (HZ + 2 - R); v.z *= -0.4; }
      const lim = Math.abs(p.z) > HZ ? GW / 2 : HX;
      if (Math.abs(p.x) > lim - R) { p.x = Math.sign(p.x) * (lim - R); v.x *= -0.6; }
    }
  
    // ---------- sút / chuyền / kỹ năng của người chơi ----------
    shoot(o, c, md, yaw, k, pitchIn) {
      const b = this.b; if (this.ph !== 'play') return;
      const locked = !!(o.charIndex === 5 && o._mioBallLock), gap = locked ? 0 : Math.hypot(b.p.x - o.p.x, b.p.z - o.p.z); if (locked) o._mioBallLock = false;
      const volley = md === 0 && o.charIndex === 2 && b.rainVolley > 0 && b.rainPhase === 2 && gap < 2.85 && b.p.y > R + 0.12 && b.p.y < R + 1.55;
      const pitch = cl(Number.isFinite(pitchIn) ? pitchIn : 0, -0.2, 0.62), flat = Math.cos(pitch), lift = Math.tan(pitch);
      const f = { x: Math.sin(yaw), z: -Math.cos(yaw) }, r = { x: Math.cos(yaw), z: Math.sin(yaw) }, ego = md === 0 && c > 0.95, S = o.s;
      const pm = 0.7 + 0.06 * S.sht, cm = 0.6 + 0.08 * S.tec, shotMul = o.charIndex === 1 ? 1.7 : 1, er = (rnd() - 0.5) * (10 - S.tec) * 0.022;
      let sd = (k & 8 ? 1 : 0) - (k & 2 ? 1 : 0); if (!sd) sd = ((-o.p.x) * r.x + (HZ * Math.sign(f.z) - o.p.z) * r.z) > 0 ? 1 : -1;
      if (volley) {
        o.spin = 0; o.spinType = ''; o.sa = 0; b.knuckle = 0; b.knuckleT = 0; b.fire = 0;
        const power = Math.min(56, (29 + c * 12) * pm) * shotMul;
        b.v.x = f.x * power * flat; b.v.y = 5.2 + c * 2.8 + power * lift; b.v.z = f.z * power * flat; b.cv = sd * 6.5 * cm * (0.8 + c * 1.25); b.ct = 0.5; b.cd = 0.12;
        b.rainVolley = 0; b.rainPhase = 0; b.rainBounces = 0; b.soraShield = 0; o.v.x += f.x * 1.8; o.v.z += f.z * 1.8; o.cd = 0.42; o.a = Math.atan2(f.x, f.z); return;
      }
      if (gap > 2.05 || b.p.y > 1.65) return;
      o.spin = 0; o.spinType = ''; o.sa = 0; b.knuckle = 0; b.knuckleT = 0; b.fire = 0;
      if (md === 0) { const s = Math.min(56, (ego ? 42 : 12 + c * 24) * pm) * shotMul; b.v.x = f.x * s * flat; b.v.y = 1.2 + c * 3.5 + s * lift; b.v.z = f.z * s * flat; b.ct = 0; }
      else if (md === 1 || md === 2) {
        const off = md === 1 ? 0.22 : 0.3, s = Math.min(52, ((md === 1 ? 16 : 19) + c * 14) * pm) * shotMul, x = f.x - r.x * sd * off, z = f.z - r.z * sd * off, n = Math.hypot(x, z);
        const loft = (md === 1 ? 2.2 : 1.3) + c * (md === 1 ? 5.2 : 6.0) + s * lift;
        b.v.x = x / n * s * flat; b.v.y = loft; b.v.z = z / n * s * flat; b.cv = sd * (md === 1 ? 10 : 16) * cm * (1 + c * 0.72); b.ct = 1.25 + c * 0.35; b.cd = md === 1 ? 0 : 0.16;
      } else { const s = Math.min(38, (18 + c * 13) * pm) * shotMul; b.v.x = f.x * s * flat; b.v.y = 7.8 + c * 5.2 + s * lift; b.v.z = f.z * s * flat; b.ct = 0; b.cv = 0; }
      const ce = Math.cos(er), se = Math.sin(er), vx = b.v.x, vz = b.v.z; b.v.x = vx * ce - vz * se; b.v.z = vx * se + vz * ce;
      o.cd = 0.4; o.a = Math.atan2(f.x, f.z);
    }
    pass(actor) {
      const b = this.b, P = this.P; if (this.ph !== 'play' || actor.sl > 0 || actor.stun > 0 || actor.spin > 0) return false;
      const gap = actor.charIndex === 5 && actor._mioBallLock ? 0 : Math.hypot(b.p.x - actor.p.x, b.p.z - actor.p.z);
      if (gap > 2.05 || b.p.y > 1.35) return false;
      const f = { x: Math.sin(actor.a), z: Math.cos(actor.a) }, team = actor.t; let best = null, bestScore = -1e9;
      for (const q of P) {
        if (q === actor || q.t !== team || q.role === 'gk') continue;
        const dx = q.p.x - actor.p.x, dz = q.p.z - actor.p.z, L = Math.hypot(dx, dz); if (L < 3 || L > 23) continue;
        const forward = (dx * f.x + dz * f.z) / L; let lane = 0, open = 8;
        for (const e of P) {
          if (e.t === team || e.role === 'gk') continue;
          const u = cl(((e.p.x - actor.p.x) * dx + (e.p.z - actor.p.z) * dz) / (L * L), 0, 1);
          if (Math.hypot(actor.p.x + dx * u - e.p.x, actor.p.z + dz * u - e.p.z) < 1.35) lane += 1.4;
          open = Math.min(open, Math.hypot(e.p.x - q.p.x, e.p.z - q.p.z));
        }
        const score = forward * 7 + open * 0.65 - L * 0.11 - lane; if (score > bestScore) { bestScore = score; best = q; }
      }
      if (!best) return false;
      if (actor.charIndex === 5) actor._mioBallLock = false;
      const dx = best.p.x + best.v.x * 0.32 - b.p.x, dz = best.p.z + best.v.z * 0.32 - b.p.z, L = Math.hypot(dx, dz) || 1, speed = cl(12 + L * 0.65, 15, 25);
      b.v.x = dx / L * speed; b.v.y = 0.85; b.v.z = dz / L * speed; b.ct = 0; b.cv = 0; b.cd = 0; actor.cd = 0.4; actor.a = Math.atan2(dx, dz); return true;
    }
    skillApply(which, actor, angle, keyMask) {
      const b = this.b, name = CHAR[actor.charIndex] ? CHAR[actor.charIndex].n : null; if (!name) return false;
      const k = which === 'rain' ? (name === 'Sora' ? SORA_RAIN : null) : SKL[name];
      if (!k || this.ph !== 'play' || actor.role === 'gk' || actor.sl > 0 || actor.stun > 0 || actor.spin > 0) return false;
      if ((which === 'rain' ? actor._skillRainCd : actor._skillMainCd) > 0) return false;
      const setCd = (v) => { if (which === 'rain') actor._skillRainCd = v; else actor._skillMainCd = v; };
      const f = { x: Math.sin(angle), z: -Math.cos(angle) }, r = { x: Math.cos(angle), z: Math.sin(angle) };
      const ix = (keyMask >> 3 & 1) - (keyMask >> 1 & 1), iz = (keyMask & 1) - (keyMask >> 2 & 1), l = Math.hypot(ix, iz), x = l ? (f.x * iz + r.x * ix) / l : f.x, z = l ? (f.z * iz + r.z * ix) / l : f.z;
      const near = (m) => Math.hypot(b.p.x - actor.p.x, b.p.z - actor.p.z) <= m + 0.35 && b.p.y <= 1.4; // +0.35 bù độ trễ mạng
      if ((name === 'Goro' || name === 'Sora') && !near(name === 'Goro' ? 1.7 : 2.8)) return false;
      if (name === 'Mio' && !near(2.25)) return false;
      if (name === 'Haru' && !near(3.0)) return false;
      if (name === 'Kaze') { actor._skillBoost = k.du; setCd(k.cd); return true; }
      if (name === 'Goro') {
        const power = 42 * (0.7 + 0.06 * FB_STAT) * 1.7; b.v.x = f.x * power; b.v.y = 4.2; b.v.z = f.z * power; b.ct = 0; b.cv = 0; b.knuckle = 1.8; b.knuckleT = 0; b.knucklePhase = rnd() * Math.PI * 2; b.fire = 0;
        actor.cd = 0.45; actor.a = Math.atan2(f.x, f.z); setCd(k.cd); return true;
      }
      if (name === 'Sora') {
        actor.dr = { x, z }; actor.spin = which === 'rain' ? RAIN_DUR : SPN; actor.spinType = which === 'rain' ? 'rain' : 'spin'; actor.imm = actor.spin + 0.55; actor.sa = 0; actor.a = Math.atan2(x, z);
        b.ct = 0; b.cv = 0; b.knuckle = 0; b.knuckleT = 0; b.fire = 0; b.soraShield = actor.spin + 0.4; b.soraShieldTeam = actor.t; b.rainVolley = 0; b.rainPhase = 0; b.rainBounces = 0;
        setCd(k.cd); return true;
      }
      if (name === 'Haru') {
        actor.a = Math.atan2(f.x, f.z); actor.vy = Math.max(actor.vy || 0, 7.2); actor._haruMeteor = 3.2; actor.imm = Math.max(actor.imm || 0, 1.8);
        b.v.x = f.x * 5.4; b.v.y = 10.4; b.v.z = f.z * 5.4; b.ct = 0; b.cv = 0; b.knuckle = 0; b.knuckleT = 0; b.fire = 0; b.rainVolley = 0; b.rainPhase = 0;
        actor.cd = 0.25; setCd(k.cd); return true;
      }
      if (name === 'Mio') {
        actor.dr = { x, z }; actor.a = Math.atan2(x, z); actor._mioTouch = k.du; actor._mioBallLock = true; actor.imm = Math.max(actor.imm || 0, k.du); actor.v.x += x * 2.4; actor.v.z += z * 2.4; setCd(k.cd); return true;
      }
      if (name === 'Tetsu') {
        actor._tetsuWall = 3.2; actor._tetsuUsed = 0; actor.imm = Math.max(actor.imm || 0, 3.2); actor.v.x *= 0.35; actor.v.z *= 0.35; actor.a = Math.atan2(f.x, f.z); setCd(k.cd); return true;
      }
      return false;
    }
    skTick(dt) {
      for (const o of this.P) {
        if (!o.human) continue;
        o._skillMainCd = Math.max(0, o._skillMainCd - dt); o._skillRainCd = Math.max(0, o._skillRainCd - dt); o._skillBoost = Math.max(0, o._skillBoost - dt);
        this.skillBallTick(o, dt);
      }
    }
    skillBallTick(actor, dt) {
      if (!(actor.spin > 0)) return; const b = this.b;
      const type = actor.spinType || 'spin', dur = type === 'rain' ? RAIN_DUR : SPN, p = cl(1 - actor.spin / dur, 0, 1), k = 1 - Math.exp(-28 * dt);
      if (type === 'rain') {
        const turn = p * Math.PI * 4.2, rad = 0.025 + 0.34 * p, ease = p * p * (3 - 2 * p), lead = 0.18 + 0.58 * p;
        const tx = actor.p.x + actor.dr.x * lead + Math.cos(turn) * rad, tz = actor.p.z + actor.dr.z * lead + Math.sin(turn) * rad, ty = R + 0.05 + 0.48 * ease;
        actor.sa = Math.sin(p * Math.PI) * 0.22 + p * 0.08; b.p.x += (tx - b.p.x) * k; b.p.z += (tz - b.p.z) * k; b.p.y += (ty - b.p.y) * k; b.v.x = b.v.y = b.v.z = 0; b.ct = 0; b.cv = 0;
      } else {
        const turn = p * Math.PI * 2, bodyA = actor.a + turn, tx = actor.p.x + Math.sin(bodyA) * 0.52, tz = actor.p.z + Math.cos(bodyA) * 0.52;
        actor.sa = turn; b.p.x += (tx - b.p.x) * k; b.p.z += (tz - b.p.z) * k; b.p.y += (R - b.p.y) * k; b.v.x = b.v.y = b.v.z = 0; b.ct = 0; b.cv = 0;
      }
      actor.spin -= dt;
      if (actor.spin <= 0) {
        const rain = type === 'rain'; actor.spin = 0; actor.spinType = ''; actor.sa = 0; actor.imm = 0.25; b.soraShield = 0.28; b.soraShieldTeam = actor.t;
        if (rain) {
          const L = Math.hypot(actor.dr.x, actor.dr.z) || 1, dx = actor.dr.x / L, dz = actor.dr.z / L;
          b.p.x = actor.p.x + dx * 0.82; b.p.y = R + 0.48; b.p.z = actor.p.z + dz * 0.82; b.v.x = dx * 7.0; b.v.y = 10.2; b.v.z = dz * 7.0; b.cv = 0; b.ct = 0; b.cd = 0.1;
          b.rainVolley = 2.5; b.rainPhase = 1; b.rainBounces = 0; actor.v.x = dx * 4.5; actor.v.z = dz * 4.5; actor.cd = 0.45;
        } else {
          b.p.x = actor.p.x + actor.dr.x * 0.72; b.p.y = R; b.p.z = actor.p.z + actor.dr.z * 0.72; b.v.x = actor.dr.x * 9.5; b.v.y = 0.55; b.v.z = actor.dr.z * 9.5; b.cv = 0; b.ct = 0;
          actor.v.x = actor.dr.x * 3.2; actor.v.z = actor.dr.z * 3.2; actor.cd = 0.35;
        }
      }
    }
  
    // ---------- trạng thái gửi cho client ----------
    snapshot() {
      const b = this.b;
      return {
        players: this.P.map((o) => [r2(o.p.x), r2(o.p.y), r2(o.p.z), r2(o.a), r2(o.v.x), r2(o.vy || 0), r2(o.v.z), Math.round(o.stamina), r2(Math.max(0, o.sl)), r2(Math.max(0, o.stun)), r2(Math.max(0, o.cd)), r2(o._skillBoost), r2(o._skillMainCd), o.human ? o.charIndex : null]),
        ball: [r2(b.p.x), r2(b.p.y), r2(b.p.z), r2(b.v.x), r2(b.v.y), r2(b.v.z), r2(b.cv || 0), r2(b.ct || 0), r2(b.knuckle || 0)],
        score: [this.s0, this.s1], time: r2(this.tl), phase: this.ph,
      };
    }
    drainEvents() { const e = this.events; this.events = []; return e; }
  }
  return { Match };
})();

// ───────────────────────── cấu hình (đặt bằng biến môi trường trên Render) ─────────────────────────
const E = process.env;
const num = (k, d, lo, hi) => { const v = Number(E[k]); return Number.isFinite(v) && E[k] !== '' ? Math.min(hi, Math.max(lo, v)) : d; };
const CFG = {
  port: num('PORT', 3000, 1, 65535),
  simHz: num('SIM_HZ', 60, 30, 120),             // tần số mô phỏng vật lý
  stateHz: num('STATE_HZ', 40, 10, 120),         // tần số gửi trạng thái trận cho client
  matchSeconds: num('MATCH_SECONDS', 180, 10, 1800),
  hubMax: num('HUB_MAX', 120, 2, 1000),          // số người tối đa trong sảnh
  maxMatches: num('MAX_MATCHES', 60, 1, 500),
  maxRooms: num('MAX_ROOMS', 300, 1, 5000),
  maxConnPerIp: num('MAX_CONN_PER_IP', 16, 1, 500),
  joinTimeoutMs: num('MATCH_JOIN_TIMEOUT_MS', 30000, 5000, 120000),
  rejoinGraceMs: num('REJOIN_GRACE_MS', 8000, 0, 60000),   // mất mạng quá lâu thì máy điều khiển thay
  endKeepMs: num('MATCH_END_KEEP_MS', 60000, 5000, 600000),
  helloTimeoutMs: num('HELLO_TIMEOUT_MS', 15000, 3000, 120000),
  hubIdleMs: num('HUB_IDLE_MS', 90000, 15000, 600000),
  pingMs: num('PING_MS', 25000, 5000, 55000),
  maxPayload: num('MAX_PAYLOAD', 8192, 512, 65536),
  dropBuffer: num('DROP_BUFFER', 96 * 1024, 4096, 4 * 1024 * 1024), // bufferedAmount vượt mức này thì bỏ gói trạng thái cũ
  msgRate: num('MSG_RATE', 240, 20, 2000),       // tin/giây mỗi kết nối (token bucket)
  msgBurst: num('MSG_BURST', 480, 40, 4000),
  checkOrigin: E.CHECK_ORIGIN !== '0',
  allowedOrigins: (E.ALLOWED_ORIGINS || '').split(',').map((s) => s.trim().toLowerCase()).filter(Boolean),
};
const STEP_MS = 1000 / CFG.simHz, STEP = 1 / CFG.simHz, STATE_MS = 1000 / CFG.stateHz;
const START = Date.now();
const log = (...a) => console.log(new Date().toISOString().slice(11, 19), ...a);

// ───────────────────────── tệp tĩnh (game) ─────────────────────────
const ROOT = __dirname, PUBLIC = path.join(ROOT, 'public');
const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.mjs': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8', '.txt': 'text/plain; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg', '.webp': 'image/webp', '.gif': 'image/gif', '.ico': 'image/x-icon', '.mp3': 'audio/mpeg', '.ogg': 'audio/ogg',
  '.wav': 'audio/wav', '.woff2': 'font/woff2', '.woff': 'font/woff', '.wasm': 'application/wasm', '.webmanifest': 'application/manifest+json',
};
const COMPRESSIBLE = /\.(html|js|mjs|css|json|txt|svg|webmanifest)$/;
const files = new Map(); // đường dẫn tuyệt đối → {buf,etag,type,gz,br,mtime,checked}

function findIndex() {
  const pick = (dir, name) => { try { const f = path.join(dir, name); return fs.statSync(f).isFile() ? f : null; } catch (_) { return null; } };
  const anyHtml = (dir) => { try { const n = fs.readdirSync(dir).filter((x) => /\.html?$/i.test(x)).sort(); return n.length ? path.join(dir, n[0]) : null; } catch (_) { return null; } };
  return pick(PUBLIC, 'index.html') || pick(ROOT, 'index.html') || anyHtml(PUBLIC) || anyHtml(ROOT);
}
let INDEX = findIndex();

function loadFile(abs) {
  const st = fs.statSync(abs), buf = fs.readFileSync(abs);
  const ext = path.extname(abs).toLowerCase();
  const e = { buf, type: MIME[ext] || 'application/octet-stream', mtime: st.mtimeMs, checked: Date.now(), gz: null, br: null,
    etag: '"' + crypto.createHash('sha1').update(buf).digest('base64url').slice(0, 22) + '"', cache: /\.(mp3|ogg|wav|woff2?|png|jpe?g|webp|gif|ico)$/.test(ext) ? 'public, max-age=86400' : 'no-cache' };
  if (COMPRESSIBLE.test(ext) && buf.length > 1024) { // nén nền: trong lúc chờ vẫn phục vụ bản gốc
    zlib.gzip(buf, { level: 9 }, (err, out) => { if (!err && files.get(abs) === e) e.gz = out; });
    zlib.brotliCompress(buf, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 9, [zlib.constants.BROTLI_PARAM_SIZE_HINT]: buf.length } }, (err, out) => { if (!err && files.get(abs) === e) e.br = out; });
  }
  files.set(abs, e);
  return e;
}
function getFile(abs) {
  let e = files.get(abs);
  if (e && Date.now() - e.checked > 2000) { // cho phép thay file game mà không cần khởi động lại
    e.checked = Date.now();
    try { if (fs.statSync(abs).mtimeMs !== e.mtime) e = null; } catch (_) { files.delete(abs); return null; }
  }
  if (!e) { try { e = loadFile(abs); } catch (_) { return null; } }
  return e;
}
function resolveStatic(urlPath) {
  let p; try { p = decodeURIComponent(urlPath); } catch (_) { return null; }
  if (p.includes('\0')) return null;
  if (p === '/' || p === '/index.html') return INDEX || (INDEX = findIndex());
  const abs = path.normalize(path.join(PUBLIC, p));
  if (!abs.startsWith(PUBLIC + path.sep)) return null;                    // chặn ../
  if (abs.split(path.sep).some((s) => s.startsWith('.'))) return null;    // không phục vụ file ẩn
  try { if (fs.statSync(abs).isFile()) return abs; } catch (_) { /* thử tên file game ở thư mục gốc */ }
  return INDEX && path.basename(INDEX) === path.basename(p) ? INDEX : null;
}

const LAG_RES = 20, loopDelay = monitorEventLoopDelay({ resolution: LAG_RES }); loopDelay.enable();
const lagMs = (v) => +Math.max(0, v / 1e6 - LAG_RES).toFixed(1); // trừ chu kỳ lấy mẫu → độ trễ thật của event loop
function stats() {
  let inMatch = 0; for (const m of matches.values()) if (m.started && !m.over) inMatch++;
  return { ok: true, uptime: Math.round((Date.now() - START) / 1000), hub: hub.size, queue: queue.length, matches: matches.size, playing: inMatch, rooms: rooms.size,
    sockets: wss ? wss.clients.size : 0, lagP99ms: lagMs(loopDelay.percentile(99)), lagMaxMs: lagMs(loopDelay.max), rssMB: Math.round(process.memoryUsage().rss / 1048576) };
}

const server = http.createServer((req, res) => {
  const url = req.url || '/', q = url.indexOf('?'), pathname = q < 0 ? url : url.slice(0, q);
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('Referrer-Policy', 'no-referrer');
  if (pathname === '/healthz') {
    const body = JSON.stringify(stats());
    res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', 'Content-Length': Buffer.byteLength(body) });
    return res.end(req.method === 'HEAD' ? undefined : body);
  }
  if (req.method !== 'GET' && req.method !== 'HEAD') { res.writeHead(405, { Allow: 'GET, HEAD' }); return res.end(); }
  const abs = resolveStatic(pathname), e = abs && getFile(abs);
  if (!e) { res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' }); return res.end(INDEX ? 'Không tìm thấy.' : 'Chưa có file game. Hãy đặt index.html vào thư mục public/.'); }
  const h = { 'Content-Type': e.type, 'Cache-Control': e.cache, ETag: e.etag, Vary: 'Accept-Encoding' };
  if (req.headers['if-none-match'] === e.etag) { res.writeHead(304, h); return res.end(); }
  const ae = String(req.headers['accept-encoding'] || ''); let body = e.buf;
  if (e.br && /\bbr\b/.test(ae)) { body = e.br; h['Content-Encoding'] = 'br'; } else if (e.gz && /\bgzip\b/.test(ae)) { body = e.gz; h['Content-Encoding'] = 'gzip'; }
  h['Content-Length'] = body.length; res.writeHead(200, h); res.end(req.method === 'HEAD' ? undefined : body);
});
server.keepAliveTimeout = 65000; server.headersTimeout = 66000; // lớn hơn timeout rảnh của proxy Render → tránh 502 ngẫu nhiên

// ───────────────────────── WebSocket: hạ tầng chung ─────────────────────────
const wss = new WebSocketServer({ noServer: true, perMessageDeflate: false, maxPayload: CFG.maxPayload, clientTracking: true });
const ipCount = new Map();

function clientIp(req) {
  const h = req.headers, t = h['true-client-ip'] || h['cf-connecting-ip'];
  if (t) return String(t).trim();
  const x = h['x-forwarded-for']; if (x) return String(x).split(',')[0].trim();
  return req.socket.remoteAddress || '?';
}
function originOk(req) {
  if (!CFG.checkOrigin) return true;
  const o = req.headers.origin; if (!o) return true;           // client không phải trình duyệt (test, công cụ)
  let host; try { host = new URL(o).host.toLowerCase(); } catch (_) { return false; }
  return host === String(req.headers.host || '').toLowerCase() || CFG.allowedOrigins.includes(host) || CFG.allowedOrigins.includes(o.toLowerCase());
}
function reject(socket, code, text) { try { socket.write('HTTP/1.1 ' + code + ' ' + text + '\r\nConnection: close\r\nContent-Length: 0\r\n\r\n'); } catch (_) { /* ignore */ } socket.destroy(); }

server.on('upgrade', (req, socket, head) => {
  const u = req.url || '', pathname = u.split('?')[0];
  if (pathname !== '/ws') return reject(socket, 404, 'Not Found');
  if (!originOk(req)) return reject(socket, 403, 'Forbidden');
  const ip = clientIp(req), n = ipCount.get(ip) || 0;
  if (n >= CFG.maxConnPerIp) return reject(socket, 429, 'Too Many Requests');
  ipCount.set(ip, n + 1);
  socket.setNoDelay(true);
  socket.on('error', () => { /* đóng đột ngột: ws sẽ tự dọn */ });
  wss.handleUpgrade(req, socket, head, (ws) => { ws.ip = ip; wss.emit('connection', ws, req); });
});

const OPEN = 1;
const jstr = JSON.stringify;
function send(ws, obj) { if (ws && ws.readyState === OPEN) { try { ws.send(jstr(obj)); } catch (_) { /* ignore */ } } }
// Gói có thể bỏ (trạng thái, vị trí): nếu đường truyền đang nghẽn thì bỏ để không tích độ trễ.
function sendLossy(ws, str) { if (ws && ws.readyState === OPEN && ws.bufferedAmount <= CFG.dropBuffer) { try { ws.send(str); return true; } catch (_) { /* ignore */ } } return false; }
function sendRaw(ws, str) { if (ws && ws.readyState === OPEN) { try { ws.send(str); } catch (_) { /* ignore */ } } }
const clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
const fin = (v, d = 0) => { v = Number(v); return Number.isFinite(v) ? v : d; };
const selOf = (v) => clamp(Math.floor(fin(v, 0)), 0, 5);
const cleanName = (v) => String(v == null ? '' : v).replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 18) || 'EGO PLAYER';
const rid = (n) => crypto.randomBytes(n).toString('hex');

wss.on('connection', (ws) => {
  ws.alive = true; ws.kind = null; ws.tok = CFG.msgBurst; ws.tokAt = Date.now(); ws.drops = 0; ws.lastMsg = Date.now(); ws.opened = Date.now();
  ws.on('pong', () => { ws.alive = true; });
  ws.on('error', () => { /* xử lý ở close */ });
  ws.on('message', (data, isBinary) => {
    if (isBinary) return;
    ws.alive = true; ws.lastMsg = Date.now();
    const t = ws.lastMsg; ws.tok = Math.min(CFG.msgBurst, ws.tok + (t - ws.tokAt) * CFG.msgRate / 1000); ws.tokAt = t;
    if (ws.tok < 1) { if (++ws.drops > 600) ws.close(1008, 'rate limit'); return; }
    ws.tok--; if (ws.tok > CFG.msgBurst / 2) ws.drops = 0;
    let m; try { m = JSON.parse(data.toString()); } catch (_) { return; }
    if (!m || typeof m.t !== 'string') return;
    try { route(ws, m, data); } catch (err) { log('route lỗi', m.t, err && err.message); }
  });
  ws.on('close', () => {
    const n = (ipCount.get(ws.ip) || 1) - 1; if (n <= 0) ipCount.delete(ws.ip); else ipCount.set(ws.ip, n);
    onClose(ws);
  });
  ws.helloTimer = setTimeout(() => { if (!ws.kind) ws.close(4000, 'hello timeout'); }, CFG.helloTimeoutMs);
});

function route(ws, m, raw) {
  switch (m.t) {
    case 'hubJoin': return hubJoin(ws, m);
    case 'hubPose': return hubPose(ws, m);
    case 'hubBeat': return;                       // chỉ để giữ kết nối (đã tính ở ws.lastMsg)
    case 'hubLeave': return hubLeave(ws);
    case 'queueJoin': return queueJoin(ws);
    case 'queueCancel': return queueCancel(ws, true);
    case 'matchJoin': return matchJoin(ws, m);
    case 'matchInput': return ws.match && ws.match.sim.input(ws.slot, m);
    case 'matchAction': return ws.match && !ws.match.over && ws.match.sim.action(ws.slot, m);
    case 'matchLeave': return ws.match && leaveMatch(ws.match, ws.slot, true);
    case 'h': return roomOpen(ws, m, true);
    case 'g': return roomOpen(ws, m, false);
    default: if (ws.kind === 'room') return roomForward(ws, m, raw);
  }
}
function onClose(ws) {
  clearTimeout(ws.helloTimer);
  if (ws.kind === 'hub') hubRemove(ws.hub);
  else if (ws.kind === 'match') matchDetach(ws);
  else if (ws.kind === 'room') roomClose(ws);
}
function setKind(ws, kind) { if (ws.kind) return false; ws.kind = kind; clearTimeout(ws.helloTimer); return true; }

// ───────────────────────── SẢNH (Ego City) + HÀNG CHỜ ─────────────────────────
const hub = new Map();   // id → người chơi trong sảnh
const queue = [];        // người đang chờ ghép cặp (FIFO)
const hubDirty = new Set();
const pub = (p) => ({ id: p.id, name: p.name, sel: p.sel, x: p.x, z: p.z, a: p.a, moving: p.moving });

function hubJoin(ws, m) {
  if (ws.kind) return;
  if (hub.size >= CFG.hubMax) { ws.close(1013, 'hub full'); return; }
  if (!setKind(ws, 'hub')) return;
  const p = { id: 'p' + rid(4), name: cleanName(m.name), sel: selOf(m.sel), x: clamp(fin(m.x), -28, 28), z: clamp(fin(m.z, 19.2), -28, 28), a: clamp(fin(m.a), -10, 10), moving: false, ws, queued: false, qpos: 0 };
  ws.hub = p; hub.set(p.id, p);
  send(ws, { t: 'hubWelcome', id: p.id, count: hub.size, players: [...hub.values()].filter((o) => o !== p).map(pub) });
  const msg = jstr({ t: 'hubEnter', player: pub(p), count: hub.size });
  for (const o of hub.values()) if (o !== p) sendRaw(o.ws, msg);
}
function hubPose(ws, m) {
  const p = ws.hub; if (!p) return;
  const x = clamp(fin(m.x, p.x), -28, 28), z = clamp(fin(m.z, p.z), -28, 28), a = clamp(fin(m.a, p.a), -10, 10), moving = !!m.moving, sel = selOf(m.sel);
  if (Math.abs(x - p.x) > 0.02 || Math.abs(z - p.z) > 0.02 || Math.abs(a - p.a) > 0.02 || moving !== p.moving) hubDirty.add(p); // đứng yên → không phát lại
  p.x = x; p.z = z; p.a = a; p.moving = moving; p.sel = sel;
}
function hubFlush() {                              // gom vị trí đã đổi, mỗi người chỉ gửi 1 tin / lượt, stringify một lần
  if (hubDirty.size) {
    const list = [...hubDirty]; hubDirty.clear();
    for (const p of list) {
      if (!hub.has(p.id)) continue;
      const msg = jstr({ t: 'hubPose', player: { id: p.id, x: p.x, z: p.z, a: p.a, moving: p.moving } });
      for (const o of hub.values()) if (o !== p) sendLossy(o.ws, msg);
    }
  }
  setTimeout(hubFlush, hub.size <= 30 ? 100 : hub.size <= 60 ? 180 : 320);
}
function hubLeave(ws) { const p = ws.hub; if (p) { hubRemove(p); try { ws.close(1000, 'bye'); } catch (_) { /* ignore */ } } }
function hubRemove(p) {
  if (!p || !hub.delete(p.id)) return;
  hubDirty.delete(p); queueCancel(p.ws, false);
  const msg = jstr({ t: 'hubExit', id: p.id, count: hub.size });
  for (const o of hub.values()) sendRaw(o.ws, msg);
}
function queueJoin(ws) {
  const p = ws.hub; if (!p) return send(ws, { t: 'queueError', message: 'Hãy vào sảnh trước khi tìm trận.' });
  if (!p.queued) { p.queued = true; queue.push(p); }
  pairQueue(); queueNotify();
}
function queueCancel(ws, reply) {
  const p = ws && ws.hub; if (!p) return;
  const i = queue.indexOf(p);
  if (i >= 0) { queue.splice(i, 1); p.queued = false; p.qpos = 0; if (reply) send(ws, { t: 'queueCancelled' }); queueNotify(); }
  else if (reply) send(ws, { t: 'queueCancelled' });
}
function queueNotify() {                           // báo vị trí khi thay đổi
  queue.forEach((p, i) => { if (p.qpos !== i + 1) { p.qpos = i + 1; send(p.ws, { t: 'queueStatus', position: i + 1 }); } });
}
function pairQueue() {
  while (queue.length >= 2) {
    const a = queue.shift(), b = queue.shift();
    const okA = a.ws.readyState === OPEN, okB = b.ws.readyState === OPEN;
    if (!okA || !okB) { if (okA) queue.unshift(a); if (okB) queue.unshift(b); continue; }
    a.queued = b.queued = false; a.qpos = b.qpos = 0;
    if (!createMatch(a, b)) { for (const p of [a, b]) send(p.ws, { t: 'queueError', message: 'Máy chủ đang đầy trận. Hãy thử lại sau ít phút.' }); }
  }
}

// ───────────────────────── TRẬN 1v1 DO SERVER QUYẾT ĐỊNH ─────────────────────────
const matches = new Map();
function createMatch(a, b) {
  if (matches.size >= CFG.maxMatches) return false;
  const id = rid(6), tokens = [rid(12), rid(12)];
  const players = [{ sel: a.sel, name: a.name }, { sel: b.sel, name: b.name }];
  const m = { id, tokens, players, sim: new Match(players, { seconds: CFG.matchSeconds }), socks: [null, null], offlineAt: [0, 0], left: [false, false],
    started: false, over: false, endedAt: 0, createdAt: Date.now(), stateAcc: 0, endSends: 0, lastPhase: 'play', timer: null };
  matches.set(id, m);
  [a, b].forEach((p, slot) => send(p.ws, { t: 'queueFound', matchId: id, token: tokens[slot], slot, players }));
  m.timer = setTimeout(() => {
    if (m.started || !matches.has(id)) return;
    for (const s of m.socks) if (s) { send(s, { t: 'matchError', message: 'Đối thủ không kết nối được trận đấu. Hãy tìm trận lại.' }); try { s.close(1000, 'timeout'); } catch (_) { /* ignore */ } }
    destroyMatch(m);
  }, CFG.joinTimeoutMs);
  log('ghép trận', id, players[0].name, 'vs', players[1].name);
  return true;
}
function matchJoin(ws, msg) {
  if (ws.kind) return;
  const fail = (text) => { send(ws, { t: 'matchError', message: text }); try { ws.close(1000, 'no match'); } catch (_) { /* ignore */ } };
  const m = matches.get(String(msg.matchId || ''));
  if (!m || m.over && Date.now() - m.endedAt > CFG.endKeepMs) return fail('Trận đấu không tồn tại hoặc đã kết thúc.');
  const slot = m.tokens.indexOf(String(msg.token || ''));
  if (slot < 0) return fail('Mã vào trận không hợp lệ.');
  if (m.left[slot]) return fail('Bạn đã rời trận này.');
  if (!setKind(ws, 'match')) return;
  const old = m.socks[slot]; if (old && old !== ws) { old.match = null; try { old.close(4001, 'replaced'); } catch (_) { /* ignore */ } }
  ws.match = m; ws.slot = slot; m.socks[slot] = ws; m.offlineAt[slot] = 0;
  send(ws, { t: 'matchWelcome', slot });
  if (m.started) return send(ws, { t: 'matchStart', players: m.players, slot, state: m.sim.snapshot() }); // vào lại sau khi rớt mạng
  if (m.socks[0] && m.socks[1]) {
    m.started = true; clearTimeout(m.timer); m.stateAcc = 0;
    const state = m.sim.snapshot();
    m.socks.forEach((s, i) => send(s, { t: 'matchStart', players: m.players, slot: i, state }));
    log('vào trận', m.id);
  } else send(ws, { t: 'matchWaiting', message: 'Đang chờ đối thủ kết nối...' });
}
function matchDetach(ws) {
  const m = ws.match; if (!m || m.socks[ws.slot] !== ws) return;
  m.socks[ws.slot] = null;
  if (m.left[ws.slot]) return;
  if (!m.started) { for (const s of m.socks) if (s) { send(s, { t: 'matchError', message: 'Đối thủ đã thoát trước khi trận bắt đầu.' }); try { s.close(1000, 'opponent left'); } catch (_) { /* ignore */ } } return destroyMatch(m); }
  m.offlineAt[ws.slot] = Date.now();               // chờ vài giây cho người chơi vào lại; hết hạn → máy điều khiển thay
}
function leaveMatch(m, slot, closeSock) {
  if (m.left[slot]) return;
  m.left[slot] = true; m.offlineAt[slot] = 0; m.sim.removeHuman(slot);
  const s = m.socks[slot]; m.socks[slot] = null;
  if (s) { s.match = null; if (closeSock) { try { s.close(1000, 'left'); } catch (_) { /* ignore */ } } }
  const other = m.socks[slot ? 0 : 1];
  if (other) send(other, { t: 'matchOpponentLeft', message: 'Đối thủ đã rời trận. Máy sẽ điều khiển vị trí của họ.' });
  if (m.left[0] && m.left[1] || !m.started && !m.socks[0] && !m.socks[1]) destroyMatch(m);
}
function destroyMatch(m) {
  clearTimeout(m.timer); matches.delete(m.id); m.over = true;
  for (let i = 0; i < 2; i++) { const s = m.socks[i]; if (s) { s.match = null; try { s.close(1000, 'match closed'); } catch (_) { /* ignore */ } m.socks[i] = null; } }
}
function broadcastState(m, snap) {
  const str = jstr({ t: 'matchState', players: snap.players, ball: snap.ball, score: snap.score, time: snap.time, phase: snap.phase });
  for (const s of m.socks) if (s) sendLossy(s, str);
}
function stepMatches() {
  const now = Date.now();
  for (const m of matches.values()) {
    if (!m.started || m.over) continue;
    const sim = m.sim;
    try {
      if (sim.ph !== 'end') {
        sim.step(STEP); sim.drainEvents(); m.stateAcc += STEP * 1000;
        if (m.stateAcc >= STATE_MS - 0.5 || sim.ph !== m.lastPhase) { m.stateAcc = Math.max(0, m.stateAcc - STATE_MS); m.lastPhase = sim.ph; broadcastState(m, sim.snapshot()); }
        if (sim.ph === 'end') { m.endedAt = now; }
      }
    } catch (err) {
      log('trận lỗi', m.id, err && err.stack || err);
      for (const s of m.socks) if (s) send(s, { t: 'matchError', message: 'Máy chủ gặp lỗi trong trận. Hãy tìm trận lại.' });
      destroyMatch(m);
    }
  }
}
function sweepMatches() {                          // chạy mỗi giây
  const now = Date.now();
  for (const m of [...matches.values()]) {
    for (let s = 0; s < 2; s++) if (m.started && !m.left[s] && !m.socks[s] && m.offlineAt[s] && now - m.offlineAt[s] > CFG.rejoinGraceMs) leaveMatch(m, s, false);
    if (!matches.has(m.id)) continue;
    if (m.over) continue;
    if (m.sim.ph === 'end') {                      // gửi lại kết quả vài lần để chắc chắn tới nơi rồi giữ phòng một lúc
      if (m.endSends < 3) { m.endSends++; broadcastState(m, m.sim.snapshot()); }
      if (now - m.endedAt > CFG.endKeepMs) destroyMatch(m);
    }
  }
}

// ───────────────────────── PHÒNG MÃ PIN (relay) ─────────────────────────
const rooms = new Map();
const HOST_TO_GUEST = new Set(['go', 's', 'resetPose', 'end', 'bta', 'skno', 'pos', 'c']);
const GUEST_TO_HOST = new Set(['i', 'sl', 'sh', 'pa', 'sk', 'bt', 'pos', 'c']);
const LOSSY = new Set(['s', 'i', 'pos']);          // gói trạng thái/điều khiển liên tục: bỏ được khi nghẽn
const normPin = (v) => String(v == null ? '' : v).toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 12);

function roomOpen(ws, m, asHost) {
  if (ws.kind) return;
  const pin = normPin(m.pin);
  if (pin.length < 3) { send(ws, { t: 'err', m: 'Mã phòng cần ít nhất 3 ký tự.' }); return; }
  let r = rooms.get(pin);
  if (asHost) {
    if (r && r.host && r.host.readyState === OPEN) { send(ws, { t: 'err', m: 'Mã phòng này đang được dùng. Hãy chọn mã khác.' }); return; }
    if (rooms.size >= CFG.maxRooms) { send(ws, { t: 'err', m: 'Máy chủ đang có quá nhiều phòng. Hãy thử lại sau.' }); return; }
    if (!setKind(ws, 'room')) return;
    r = { pin, host: ws, guest: null, hostSel: selOf(m.sel) }; rooms.set(pin, r);
    ws.room = r; ws.slot = 0;
    send(ws, { t: 'ok', server: 1, slot: 0 });
  } else {
    if (!r || !r.host || r.host.readyState !== OPEN) { send(ws, { t: 'err', m: 'Không tìm thấy phòng ' + pin + '. Hãy kiểm tra mã hoặc nhờ chủ phòng tạo phòng trước.' }); return; }
    if (r.guest && r.guest.readyState === OPEN) { send(ws, { t: 'err', m: 'Phòng đã đủ 2 người.' }); return; }
    if (!setKind(ws, 'room')) return;
    r.guest = ws; ws.room = r; ws.slot = 1;
    send(ws, { t: 'ok', server: 1, slot: 1 });
    send(r.host, { t: 'j', sel: selOf(m.sel) });
  }
}
function roomForward(ws, m, raw) {
  const r = ws.room; if (!r) return;
  const host = ws.slot === 0, to = host ? r.guest : r.host;
  if (m.t === 'hb') return send(ws, { t: 'hp', s: m.s });          // đo ping: trả lại đúng dấu thời gian client gửi
  if (!(host ? HOST_TO_GUEST : GUEST_TO_HOST).has(m.t) || !to) return;
  if (m.t === 'pos') { m.p = ws.slot; const s = jstr(m); return sendLossy(to, s); }
  const str = typeof raw === 'string' ? raw : raw.toString();      // chuyển nguyên văn, không stringify lại
  if (LOSSY.has(m.t)) sendLossy(to, str); else sendRaw(to, str);
}
function roomClose(ws) {
  const r = ws.room; if (!r) return;
  if (ws.slot === 0) { // chủ phòng thoát → phòng đóng
    if (rooms.get(r.pin) === r) rooms.delete(r.pin);
    if (r.guest) { send(r.guest, { t: 'bye' }); try { r.guest.close(1000, 'host left'); } catch (_) { /* ignore */ } r.guest = null; }
  } else if (r.guest === ws) { r.guest = null; send(r.host, { t: 'bye' }); }
}

// ───────────────────────── vòng lặp mô phỏng (bù trôi thời gian) + dọn dẹp định kỳ ─────────────────────────
let last = performance.now(), acc = 0;
function simLoop() {
  const now = performance.now(); acc += now - last; last = now;
  if (acc > STEP_MS * 6) acc = STEP_MS * 6;        // CPU quá tải: bỏ bớt thay vì đuổi theo vô hạn (tránh "vòng xoáy chết")
  while (acc >= STEP_MS) { acc -= STEP_MS; stepMatches(); }
  setTimeout(simLoop, Math.max(1, Math.floor(STEP_MS - acc)));
}
setInterval(sweepMatches, 1000).unref();
setInterval(() => {                                // giữ kết nối + dọn kết nối chết
  const now = Date.now();
  for (const ws of wss.clients) {
    if (!ws.alive) { ws.terminate(); continue; }
    if (ws.kind === 'hub' && now - ws.lastMsg > CFG.hubIdleMs) { ws.close(4002, 'idle'); continue; }
    ws.alive = false; try { ws.ping(); } catch (_) { /* ignore */ }
  }
}, CFG.pingMs).unref();
setInterval(() => {                                // nhật ký tình trạng mỗi phút
  const s = stats(); if (s.hub || s.matches || s.rooms) log('stats', jstr(s));
  if (s.lagP99ms > 60) log('CẢNH BÁO event loop trễ p99=' + s.lagP99ms + 'ms — cân nhắc nâng cấu hình Render');
  loopDelay.reset();
}, 60000).unref();

// ───────────────────────── khởi động / tắt êm ─────────────────────────
function shutdown(sig) {
  log('nhận', sig, '— đóng máy chủ');
  server.close();
  for (const ws of wss.clients) { try { ws.close(1001, 'server restart'); } catch (_) { /* ignore */ } }
  setTimeout(() => process.exit(0), 800); // đủ để gửi khung đóng tới client; Render cho tối đa 30s
}
process.on('SIGTERM', () => shutdown('SIGTERM'));
process.on('SIGINT', () => shutdown('SIGINT'));
process.on('uncaughtException', (err) => log('uncaughtException', err && err.stack || err));
process.on('unhandledRejection', (err) => log('unhandledRejection', err && err.stack || err));

if (require.main === module) {
  if (INDEX) getFile(INDEX); // nạp + nén trước
  server.listen(CFG.port, '0.0.0.0', () => {
    log('Ego Futsal server · cổng', CFG.port, '· sim', CFG.simHz + 'Hz · state', CFG.stateHz + 'Hz · game:', INDEX ? path.relative(ROOT, INDEX) : '(chưa có file game trong public/)');
    simLoop(); hubFlush();
  });
}
module.exports = { server, wss, CFG, stats, matches, rooms, hub };
