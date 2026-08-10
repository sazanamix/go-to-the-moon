/*
 * Go to the Moon
 * 地球の自転で得られる接線速度＋ロケット固定Δvで射出方向(＝発射タイミング)だけを操作し、
 * 地球・月の重力で数値積分(RK4)されるロケットを月に届けるゲーム。
 *
 * 主要な物理定数は実測値。月の軌道はケプラー方程式を解いた本物の楕円軌道。
 * 詳細は index.html 内の「計算モデルについて」を参照。
 */
(() => {
  'use strict';

  // ---------- 物理定数 (SI単位: m, s, kg) ----------
  const GM_EARTH = 3.986004418e14;      // 地球の重力パラメータ
  const GM_MOON  = 4.9048695e12;        // 月の重力パラメータ
  const R_EARTH  = 6.371e6;             // 地球半径
  const R_MOON   = 1.7374e6;            // 月半径
  const MOON_A   = 3.844e8;             // 月軌道の半長径
  const MOON_E   = 0.0549;              // 月軌道の離心率
  const MOON_T   = 27.321661 * 86400;   // 月の公転周期(秒)
  const EARTH_T  = 86164.0905;          // 地球の自転周期(秒, 恒星日)

  const CAPTURE_RADIUS = 1.0e7;         // 「月に到達」判定半径(月重力圏に十分侵入したとみなす距離)
  const OUT_OF_BOUNDS  = 6.2e8;         // これより遠くへ離れたら「行方不明」
  const MAX_FLIGHT_TIME = 1.2e6;        // 打ち切りまでのシミュレーション内時間(秒)

  const ROCKET_DELTA_V = 10630;         // ロケット自身が生み出す固定の速度増分(m/s)
  const ACCEL = 9000;                   // 時間加速倍率 (1実時間秒 = ACCEL シミュレーション秒)
  const SUB_DT = 4;                     // RK4の内部固定ステップ幅(シミュレーション秒)

  // ---------- 状態 ----------
  const state = {
    tSim: MOON_T * 0.15,      // 開始時刻(月をやや近日点寄りの見やすい位置に置くための任意オフセット)
    launched: false,
    finished: false,
    rocket: null,             // {x,y,vx,vy, t0, closest}
    trail: [],
    dockOffset: null,         // 月到達後、ロケットを月に対して固定するための相対位置 {x,y}
    attempts: 0,
    successes: 0,
    resultMsg: null,
  };

  // ---------- ケプラー方程式 ----------
  // 平均近点角 M から離心近点角 E をニュートン法で求める
  function solveKepler(M, e) {
    let E = M;
    for (let i = 0; i < 8; i++) {
      E -= (E - e * Math.sin(E) - M) / (1 - e * Math.cos(E));
    }
    return E;
  }

  // 時刻 tSim における月の位置 {x,y}(地球中心, 近地点方向をx軸正方向に固定)
  function moonPosition(tSim) {
    const n = (2 * Math.PI) / MOON_T;
    const M = n * tSim;
    const E = solveKepler(M % (2 * Math.PI), MOON_E);
    const r = MOON_A * (1 - MOON_E * Math.cos(E));
    const trueAnom = 2 * Math.atan2(
      Math.sqrt(1 + MOON_E) * Math.sin(E / 2),
      Math.sqrt(1 - MOON_E) * Math.cos(E / 2)
    );
    return { x: r * Math.cos(trueAnom), y: r * Math.sin(trueAnom), r };
  }

  function earthRotationAngle(tSim) {
    return ((2 * Math.PI) / EARTH_T) * tSim;
  }

  // ---------- ロケットの運動方程式 (地球固定, 月は解析位置) ----------
  function acceleration(pos, tSim) {
    const moon = moonPosition(tSim);
    const dxE = pos.x, dyE = pos.y;
    const rE3 = Math.pow(dxE * dxE + dyE * dyE, 1.5);
    const dxM = pos.x - moon.x, dyM = pos.y - moon.y;
    const rM3 = Math.pow(dxM * dxM + dyM * dyM, 1.5);
    return {
      ax: -GM_EARTH * dxE / rE3 - GM_MOON * dxM / rM3,
      ay: -GM_EARTH * dyE / rE3 - GM_MOON * dyM / rM3,
    };
  }

  function rk4Step(r, dt, tSim) {
    function deriv(s, t) {
      const a = acceleration(s, t);
      return { dx: s.vx, dy: s.vy, dvx: a.ax, dvy: a.ay };
    }
    const k1 = deriv(r, tSim);
    const s2 = { x: r.x + k1.dx * dt / 2, y: r.y + k1.dy * dt / 2, vx: r.vx + k1.dvx * dt / 2, vy: r.vy + k1.dvy * dt / 2 };
    const k2 = deriv(s2, tSim + dt / 2);
    const s3 = { x: r.x + k2.dx * dt / 2, y: r.y + k2.dy * dt / 2, vx: r.vx + k2.dvx * dt / 2, vy: r.vy + k2.dvy * dt / 2 };
    const k3 = deriv(s3, tSim + dt / 2);
    const s4 = { x: r.x + k3.dx * dt, y: r.y + k3.dy * dt, vx: r.vx + k3.dvx * dt, vy: r.vy + k3.dvy * dt };
    const k4 = deriv(s4, tSim + dt);
    return {
      x: r.x + (dt / 6) * (k1.dx + 2 * k2.dx + 2 * k3.dx + k4.dx),
      y: r.y + (dt / 6) * (k1.dy + 2 * k2.dy + 2 * k3.dy + k4.dy),
      vx: r.vx + (dt / 6) * (k1.dvx + 2 * k2.dvx + 2 * k3.dvx + k4.dvx),
      vy: r.vy + (dt / 6) * (k1.dvy + 2 * k2.dvy + 2 * k3.dvy + k4.dvy),
    };
  }

  // ---------- Canvas ----------
  const canvas = document.getElementById('stage');
  const ctx = canvas.getContext('2d');
  let cssSize = 640;
  let SCALE = 1; // px per meter

  function resize() {
    const rect = canvas.parentElement.getBoundingClientRect();
    cssSize = Math.round(rect.width);
    const dpr = window.devicePixelRatio || 1;
    canvas.width = cssSize * dpr;
    canvas.height = cssSize * dpr;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    // 月の遠地点(約4.055e8m)が画面の40%程度に収まるスケール
    SCALE = (cssSize * 0.40) / (MOON_A * (1 + MOON_E));
  }
  window.addEventListener('resize', resize);

  function toPx(x, y) {
    return { x: cssSize / 2 + x * SCALE, y: cssSize / 2 + y * SCALE };
  }

  // 星の背景(固定パターン、視差なしの装飾)
  const stars = Array.from({ length: 140 }, () => ({
    x: Math.random(), y: Math.random(), r: Math.random() * 1.3 + 0.2, a: Math.random() * 0.6 + 0.25,
  }));

  // 月の軌道ガイド(静的な楕円ポリライン、初回のみ計算)
  const moonOrbitPath = (() => {
    const pts = [];
    for (let i = 0; i <= 240; i++) {
      const M = (i / 240) * 2 * Math.PI;
      const E = solveKepler(M, MOON_E);
      const r = MOON_A * (1 - MOON_E * Math.cos(E));
      const trueAnom = 2 * Math.atan2(
        Math.sqrt(1 + MOON_E) * Math.sin(E / 2),
        Math.sqrt(1 - MOON_E) * Math.cos(E / 2)
      );
      pts.push({ x: r * Math.cos(trueAnom), y: r * Math.sin(trueAnom) });
    }
    return pts;
  })();

  function draw() {
    ctx.clearRect(0, 0, cssSize, cssSize);

    // 背景の星
    ctx.save();
    for (const s of stars) {
      ctx.globalAlpha = s.a;
      ctx.fillStyle = '#cfe8ff';
      ctx.beginPath();
      ctx.arc(s.x * cssSize, s.y * cssSize, s.r, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.restore();

    // 月の軌道ガイド
    ctx.beginPath();
    moonOrbitPath.forEach((p, i) => {
      const px = toPx(p.x, p.y);
      if (i === 0) ctx.moveTo(px.x, px.y); else ctx.lineTo(px.x, px.y);
    });
    ctx.closePath();
    ctx.strokeStyle = 'rgba(127,224,196,0.16)';
    ctx.setLineDash([2, 4]);
    ctx.lineWidth = 1;
    ctx.stroke();
    ctx.setLineDash([]);

    const moon = moonPosition(state.tSim);
    const moonPx = toPx(moon.x, moon.y);
    const earthPx = toPx(0, 0);

    // 月の捕獲(到達判定)ゾーン
    ctx.beginPath();
    ctx.arc(moonPx.x, moonPx.y, CAPTURE_RADIUS * SCALE, 0, Math.PI * 2);
    ctx.strokeStyle = 'rgba(127,224,196,0.35)';
    ctx.setLineDash([3, 3]);
    ctx.stroke();
    ctx.setLineDash([]);

    // ロケットの軌跡
    if (state.trail.length > 1) {
      ctx.beginPath();
      state.trail.forEach((p, i) => {
        const px = toPx(p.x, p.y);
        if (i === 0) ctx.moveTo(px.x, px.y); else ctx.lineTo(px.x, px.y);
      });
      ctx.strokeStyle = 'rgba(255,255,255,0.55)';
      ctx.lineWidth = 1.2;
      ctx.stroke();
    }

    // 地球
    const earthR = Math.max(R_EARTH * SCALE, 6);
    ctx.beginPath();
    ctx.arc(earthPx.x, earthPx.y, earthR, 0, Math.PI * 2);
    const eg = ctx.createRadialGradient(earthPx.x - earthR * 0.3, earthPx.y - earthR * 0.3, earthR * 0.1, earthPx.x, earthPx.y, earthR);
    eg.addColorStop(0, '#7fc8e0');
    eg.addColorStop(1, '#2c5f78');
    ctx.fillStyle = eg;
    ctx.fill();

    // 地球の自転を示すマーカー(自転と共に回転する目印)
    const earthAngle = earthRotationAngle(state.tSim);
    const markerR = earthR * 0.9;
    ctx.beginPath();
    ctx.arc(earthPx.x + Math.cos(earthAngle) * markerR, earthPx.y + Math.sin(earthAngle) * markerR, Math.max(earthR * 0.16, 1.4), 0, Math.PI * 2);
    ctx.fillStyle = '#0b2b38';
    ctx.fill();

    // 発射前のロケット(地球表面を自転と共に周回)
    if (!state.launched) {
      const launchR = earthR;
      const rp = { x: earthPx.x + Math.cos(earthAngle) * launchR, y: earthPx.y + Math.sin(earthAngle) * launchR };
      ctx.beginPath();
      ctx.arc(rp.x, rp.y, 2.4, 0, Math.PI * 2);
      ctx.fillStyle = '#ffffff';
      ctx.shadowColor = '#7fe0c4';
      ctx.shadowBlur = 6;
      ctx.fill();
      ctx.shadowBlur = 0;
    }

    // 月
    const moonR = Math.max(R_MOON * SCALE, 3);
    ctx.beginPath();
    ctx.arc(moonPx.x, moonPx.y, moonR, 0, Math.PI * 2);
    ctx.fillStyle = '#c9c9c9';
    ctx.fill();
    // 常に地球側を向く模様(潮汐固定の再現)
    const faceAngle = Math.atan2(earthPx.y - moonPx.y, earthPx.x - moonPx.x);
    ctx.beginPath();
    ctx.arc(moonPx.x + Math.cos(faceAngle) * moonR * 0.4, moonPx.y + Math.sin(faceAngle) * moonR * 0.4, Math.max(moonR * 0.28, 1), 0, Math.PI * 2);
    ctx.fillStyle = '#9a9a9a';
    ctx.fill();

    // 飛行中のロケット(到達成功後は月に対する相対位置を保ったまま月と一緒に動く)
    if (state.launched && state.rocket) {
      const rocketPos = state.dockOffset
        ? { x: moon.x + state.dockOffset.x, y: moon.y + state.dockOffset.y }
        : state.rocket;
      const rp = toPx(rocketPos.x, rocketPos.y);
      ctx.beginPath();
      ctx.arc(rp.x, rp.y, 2.2, 0, Math.PI * 2);
      ctx.fillStyle = '#ffffff';
      ctx.shadowColor = '#ffffff';
      ctx.shadowBlur = 5;
      ctx.fill();
      ctx.shadowBlur = 0;
    }
  }

  // ---------- HUD ----------
  const hudStatus = document.getElementById('hudStatus');
  const hudTime = document.getElementById('hudTime');
  const hudDist = document.getElementById('hudDist');
  const hudSpeed = document.getElementById('hudSpeed');
  const hudClosest = document.getElementById('hudClosest');
  const banner = document.getElementById('banner');
  const launchBtn = document.getElementById('launchBtn');
  const retryBtn = document.getElementById('retryBtn');
  const attemptCountEl = document.getElementById('attemptCount');
  const successCountEl = document.getElementById('successCount');
  const giveUpBtn = document.getElementById('giveUpBtn');
  const rankList = document.getElementById('rankList');
  const rankClearBtn = document.getElementById('rankClearBtn');

  function fmtKm(m) { return (m / 1000).toLocaleString('ja-JP', { maximumFractionDigits: 0 }) + ' km'; }
  function fmtTime(tSim) {
    const days = Math.floor(tSim / 86400);
    const hours = Math.floor((tSim % 86400) / 3600);
    return `${days}日 ${hours}時間`;
  }

  function updateHud() {
    if (!state.launched) {
      hudStatus.textContent = '発射待機中';
      hudDist.textContent = '–';
      hudSpeed.textContent = '–';
      hudClosest.textContent = '–';
      hudTime.textContent = fmtTime(state.tSim);
    } else if (state.finished) {
      // 飛行終了後は結果を固定表示する(月・地球はその後も動き続けるが、飛行結果には無関係)
      const f = state.finalStats;
      hudStatus.textContent = '飛行終了';
      hudDist.textContent = fmtKm(f.dist);
      hudSpeed.textContent = (f.speed / 1000).toFixed(2) + ' km/s';
      hudClosest.textContent = fmtKm(f.closest);
      hudTime.textContent = fmtTime(f.elapsed);
    } else {
      const moon = moonPosition(state.tSim);
      const r = state.rocket;
      const dist = Math.hypot(r.x - moon.x, r.y - moon.y);
      const speed = Math.hypot(r.vx, r.vy);
      hudStatus.textContent = '飛行中';
      hudDist.textContent = fmtKm(dist);
      hudSpeed.textContent = (speed / 1000).toFixed(2) + ' km/s';
      hudClosest.textContent = fmtKm(r.closest);
      hudTime.textContent = fmtTime(state.tSim - r.t0);
    }
  }

  function showBanner(text, isFail) {
    banner.textContent = text;
    banner.classList.remove('hidden', 'fail');
    if (isFail) banner.classList.add('fail');
  }
  function hideBanner() {
    banner.classList.add('hidden');
  }

  // ---------- ランキング(この端末のlocalStorageのみに保存) ----------
  const RANK_KEY = 'gttm_ranking_v1';
  const RANK_MAX = 10;

  function loadRanking() {
    try {
      const raw = localStorage.getItem(RANK_KEY);
      const list = raw ? JSON.parse(raw) : [];
      return Array.isArray(list) ? list : [];
    } catch (e) {
      return [];
    }
  }
  function saveRanking(list) {
    try { localStorage.setItem(RANK_KEY, JSON.stringify(list)); } catch (e) { /* 保存できなくても続行 */ }
  }
  function fmtFlightTime(sec) {
    const days = Math.floor(sec / 86400);
    const hours = Math.floor((sec % 86400) / 3600);
    const mins = Math.floor((sec % 3600) / 60);
    if (days > 0) return `${days}日${hours}時間`;
    if (hours > 0) return `${hours}時間${mins}分`;
    return `${mins}分`;
  }
  function renderRanking(highlightIndex) {
    const list = loadRanking();
    rankList.innerHTML = '';
    if (list.length === 0) {
      rankList.innerHTML = '<li class="rank-empty">まだ月に到達した記録がありません</li>';
      return;
    }
    list.forEach((entry, i) => {
      const li = document.createElement('li');
      if (i === highlightIndex) li.classList.add('rank-new');
      const date = new Date(entry.date);
      const dateStr = `${date.getMonth() + 1}/${date.getDate()} ${String(date.getHours()).padStart(2, '0')}:${String(date.getMinutes()).padStart(2, '0')}`;
      li.innerHTML = `<span class="rank-no">${i + 1}</span><span class="rank-time">到達まで ${fmtFlightTime(entry.flightSec)}</span><span class="rank-meta">最接近 ${Math.round(entry.closestKm).toLocaleString('ja-JP')}km ・ ${dateStr}</span>`;
      rankList.appendChild(li);
    });
  }
  // 到達に成功した際の記録を登録し、TOP10入りしていればその順位(0始まり)を返す(なければ-1)
  function submitRanking(flightSec, closestKm) {
    const id = Date.now() + Math.random();
    const list = loadRanking();
    list.push({ id, flightSec, closestKm, date: Date.now() });
    list.sort((a, b) => a.flightSec - b.flightSec);
    const trimmed = list.slice(0, RANK_MAX);
    saveRanking(trimmed);
    return trimmed.findIndex((e) => e.id === id);
  }
  rankClearBtn.addEventListener('click', () => {
    if (!confirm('この端末に保存されたランキング記録を消去しますか？')) return;
    saveRanking([]);
    renderRanking(-1);
  });

  // ---------- 発射 ----------
  function launch() {
    if (state.launched) return;
    state.attempts++;
    attemptCountEl.textContent = state.attempts;

    const angle = earthRotationAngle(state.tSim);
    const pos = { x: Math.cos(angle) * R_EARTH, y: Math.sin(angle) * R_EARTH };
    const omega = (2 * Math.PI) / EARTH_T;
    const vSurface = R_EARTH * omega;
    const speed = vSurface + ROCKET_DELTA_V;
    const tangent = { x: -Math.sin(angle), y: Math.cos(angle) };

    state.rocket = {
      x: pos.x, y: pos.y,
      vx: tangent.x * speed, vy: tangent.y * speed,
      t0: state.tSim,
      closest: Infinity,
    };
    state.launched = true;
    state.finished = false;
    state.trail = [{ x: pos.x, y: pos.y }];
    launchBtn.disabled = true;
    giveUpBtn.classList.remove('hidden');
    hideBanner();
  }

  function finish(msg, isFail, tAtFinish, distMoonAtFinish) {
    state.finished = true;
    launchBtn.disabled = true;
    giveUpBtn.classList.add('hidden');
    retryBtn.classList.remove('hidden');

    // 飛行終了の瞬間の値でHUDを固定する(その後も月・地球は動き続けるが飛行結果には無関係)
    const r = state.rocket;
    const flightSec = tAtFinish - r.t0;
    state.finalStats = {
      elapsed: flightSec,
      dist: distMoonAtFinish,
      speed: Math.hypot(r.vx, r.vy),
      closest: r.closest,
    };

    if (!isFail) {
      state.successes++;
      successCountEl.textContent = state.successes;
      const rankIdx = submitRanking(flightSec, r.closest / 1000);
      renderRanking(rankIdx);
      if (rankIdx >= 0) {
        msg += ` (ランキング${rankIdx + 1}位にランクイン！)`;
      }
      // 到達成功後は宇宙空間に静止させず、月に対する相対位置を固定して月と一緒に動かす
      const moonAtFinish = moonPosition(tAtFinish);
      state.dockOffset = { x: r.x - moonAtFinish.x, y: r.y - moonAtFinish.y };
      // ロケットは月と一緒に移動するため、その場に残る飛行軌跡は表示しない
      state.trail = [];
    } else {
      state.dockOffset = null;
    }
    showBanner(msg, isFail);
  }

  function reset() {
    state.launched = false;
    state.finished = false;
    state.rocket = null;
    state.trail = [];
    state.dockOffset = null;
    launchBtn.disabled = false;
    giveUpBtn.classList.add('hidden');
    retryBtn.classList.add('hidden');
    hideBanner();
  }

  launchBtn.addEventListener('click', launch);
  retryBtn.addEventListener('click', reset);
  giveUpBtn.addEventListener('click', reset);

  // ---------- メインループ ----------
  let lastT = null;
  const TRAIL_MAX = 900;

  function frame(now) {
    if (lastT === null) lastT = now;
    let dtWall = (now - lastT) / 1000;
    lastT = now;
    dtWall = Math.min(dtWall, 0.05); // タブ非アクティブ復帰時の暴走を防止

    let dtSim = dtWall * ACCEL;
    state.tSim += dtSim;

    if (state.launched && !state.finished) {
      let remaining = dtSim;
      while (remaining > 0) {
        const step = Math.min(SUB_DT, remaining);
        const tBefore = state.tSim - remaining; // このサブステップ開始時のシミュレーション時刻
        const next = rk4Step(state.rocket, step, tBefore);
        state.rocket.x = next.x; state.rocket.y = next.y;
        state.rocket.vx = next.vx; state.rocket.vy = next.vy;
        remaining -= step;

        const tNow = tBefore + step;
        const moon = moonPosition(tNow);
        const distMoon = Math.hypot(state.rocket.x - moon.x, state.rocket.y - moon.y);
        const distEarth = Math.hypot(state.rocket.x, state.rocket.y);
        if (distMoon < state.rocket.closest) state.rocket.closest = distMoon;

        if (distMoon < CAPTURE_RADIUS) {
          finish('🌕 月へ到達しました！ 重力に捕獲されました。', false, tNow, distMoon);
          break;
        }
        if (distEarth < R_EARTH) {
          finish('💥 地球に落下しました。', true, tNow, distMoon);
          break;
        }
        if (distEarth > OUT_OF_BOUNDS) {
          finish('🛰️ ロケットは彼方へ飛び去り、行方不明になりました。', true, tNow, distMoon);
          break;
        }
        if (tNow - state.rocket.t0 > MAX_FLIGHT_TIME) {
          finish('⏱️ 燃料切れ想定 ― 月に届きませんでした。', true, tNow, distMoon);
          break;
        }
      }
      if (!state.finished) {
        state.trail.push({ x: state.rocket.x, y: state.rocket.y });
        if (state.trail.length > TRAIL_MAX) state.trail.shift();
      }
    }

    draw();
    updateHud();
    requestAnimationFrame(frame);
  }

  // ---------- 情報オーバーレイ ----------
  const infoOverlay = document.getElementById('infoOverlay');
  document.getElementById('infoBtn').addEventListener('click', () => infoOverlay.classList.remove('hidden'));
  document.getElementById('infoClose').addEventListener('click', () => infoOverlay.classList.add('hidden'));
  infoOverlay.addEventListener('click', (e) => { if (e.target === infoOverlay) infoOverlay.classList.add('hidden'); });

  // ---------- 起動 ----------
  resize();
  renderRanking(-1);
  requestAnimationFrame(frame);
})();
