// Compatibility-coloring and Bob-entropy refinements of causal response capacities.
// Independent re-implementation (shares no code with causal_response_check.js).
// Run: node causal_compat_check.js            (seed 870031)
//
// Capacities compared for an A-vertex v (log2 of a code size):
//   c_old  = min(|D(v)|, 2^|R(v)|)                       committed structural capacity
//   c_plus = min(|D(v)|, 2^|R(v)|, 2^mu(v))              new structural capacity
//   c_T    = log2 #{T_v(x)}   local response tables      (semantic, <= c_old)
//   c_G    = log2 #{G_v(x)}   y -> v(x,y)                 (semantic, <= min(|D*|, 2^mu))
//   c_chi  = log2 (greedy colours of the conflict graph)  (semantic, <= min(c_T, c_G))
// mu(v): minimum number of data-free vertices meeting every path from a varying Bob primary to v.
// Conflict: x ~ x' iff some allowed y gives equal actual reverse values on R(v) and v(x,y) != v(x',y).
"use strict";
let seed = 870031;
function rnd(n) { seed = (Math.imul(seed, 1103515245) + 12345) >>> 0; return (seed >>> 7) % n; }
function ok(c, m) { if (!c) throw Error("assertion failed: " + m); }
const EPS = 1e-9;
const lg = (x) => Math.log2(x);

function Circuit(n, side) {
  const E = [], S = side.slice();
  const AND = (a, b, s) => { E.push([a, b]); S.push(s); return 2 * (n + E.length - 1); };
  const OR = (a, b, s) => AND(a ^ 1, b ^ 1, s) ^ 1;
  const XOR = (a, b, s) => OR(AND(a, b ^ 1, s), AND(a ^ 1, b, s), s);
  const MUX = (q, a, b, s) => OR(AND(q, b, s), AND(q ^ 1, a, s), s); // q ? b : a
  return { n, E, S, AND, OR, XOR, MUX };
}
const nv = (C) => C.n + C.E.length;
function evalAll(C, inp) {
  const V = new Uint8Array(nv(C));
  for (let i = 0; i < C.n; i++) V[i] = inp[i];
  for (let j = 0; j < C.E.length; j++) {
    const [a, b] = C.E[j];
    V[C.n + j] = (V[a >> 1] ^ (a & 1)) & (V[b >> 1] ^ (b & 1));
  }
  return V;
}

// ---- structural sets ---------------------------------------------------------------------
function structure(C, U) {
  // U: array of data primary indices (all on A). Returns D, R (as Sets), Dstar, forward ports.
  const N = nv(C), D = [], R = [], Ds = [], F = new Set(), Rev = new Set();
  const Uset = new Set(U);
  for (let v = 0; v < N; v++) { D.push(new Set()); R.push(new Set()); Ds.push(new Set()); }
  for (const i of U) { D[i].add(i); Ds[i].add(i); }
  for (let j = 0; j < C.E.length; j++) {
    const v = C.n + j;
    for (const l of C.E[j]) {
      const u = l >> 1;
      for (const x of Ds[u]) Ds[v].add(x);
      if (C.S[u] !== C.S[v]) (C.S[u] === 0 ? F : Rev).add(u);
      if (C.S[v] === 0) {
        if (C.S[u] === 0) { for (const x of D[u]) D[v].add(x); for (const x of R[u]) R[v].add(x); }
        else R[v].add(u);
      }
    }
  }
  return { D, R, Ds, F: [...F].sort((a, b) => a - b), Rev: [...Rev].sort((a, b) => a - b), Uset };
}

// Generic max-flow (Edmonds-Karp, real capacities).
function MaxFlow(V) {
  const adj = Array.from({ length: V }, () => []);
  return {
    adj,
    edge(u, v, c) { adj[u].push({ v, c, r: adj[v].length }); adj[v].push({ v: u, c: 0, r: adj[u].length - 1 }); },
    run(s, t) {
      let flow = 0;
      for (;;) {
        const prev = new Array(V).fill(null); prev[s] = -1; const q = [s];
        for (let h = 0; h < q.length && prev[t] === null; h++) {
          const u = q[h];
          adj[u].forEach((e, i) => { if (e.c > EPS && prev[e.v] === null) { prev[e.v] = [u, i]; q.push(e.v); } });
        }
        if (prev[t] === null) return { flow, reach: prev.map((p) => p !== null) };
        let d = Infinity;
        for (let v = t; v !== s;) { const [u, i] = prev[v]; d = Math.min(d, adj[u][i].c); v = u; }
        for (let v = t; v !== s;) { const [u, i] = prev[v], e = adj[u][i]; e.c -= d; adj[v][e.r].c += d; v = u; }
        flow += d;
      }
    },
  };
}

// mu(v): min data-free vertex separator between varying Bob primaries Y and v (whole circuit).
function muOf(C, st, Y, v) {
  const N = nv(C), INF = 1e9, mf = MaxFlow(2 * N + 1), src = 2 * N;
  for (let u = 0; u < N; u++) mf.edge(2 * u, 2 * u + 1, st.Ds[u].size === 0 ? 1 : INF);
  for (let j = 0; j < C.E.length; j++) for (const l of C.E[j]) mf.edge(2 * (l >> 1) + 1, 2 * (C.n + j), INF);
  for (const y of Y) mf.edge(src, 2 * y, INF);
  if (st.Ds[v].size === 0) return null; // data-free vertex: not used (c = 0 anyway for D(v) empty)
  return Math.round(mf.run(src, 2 * v).flow);
}

// A-only vertex cut test: does K meet every A-only path from U to a forward port?
function isCut(C, st, K) {
  const N = nv(C), Ks = new Set(K), reach = new Uint8Array(N);
  for (const i of st.Uset) reach[i] = Ks.has(i) ? 0 : 1;
  for (let j = 0; j < C.E.length; j++) {
    const v = C.n + j;
    if (C.S[v] !== 0 || Ks.has(v)) continue;
    reach[v] = C.E[j].some((l) => C.S[l >> 1] === 0 && reach[l >> 1]) ? 1 : 0;
  }
  return st.F.every((p) => !reach[p]);
}

// Vertex-capacitated min cut on A from U to forward ports; returns {flow, cut, dist}.
function causalFlow(C, st, cap) {
  const N = nv(C), INF = 1e9, mf = MaxFlow(2 * N + 2), s = 2 * N, t = s + 1;
  for (let v = 0; v < N; v++) if (C.S[v] === 0) {
    mf.edge(2 * v, 2 * v + 1, cap[v]);
    if (st.Uset.has(v)) mf.edge(s, 2 * v, INF);
  }
  for (let j = 0; j < C.E.length; j++) {
    const v = C.n + j;
    if (C.S[v] === 0) for (const l of C.E[j]) if (C.S[l >> 1] === 0) mf.edge(2 * (l >> 1) + 1, 2 * v, INF);
  }
  for (const p of st.F) mf.edge(2 * p + 1, t, INF);
  const { flow, reach } = mf.run(s, t);
  const cut = [];
  for (let v = 0; v < N; v++) if (C.S[v] === 0 && reach[2 * v] && !reach[2 * v + 1]) cut.push(v);
  ok(isCut(C, st, cut), "min-cut is an A-only cut");
  ok(Math.abs(cut.reduce((a, v) => a + cap[v], 0) - flow) < 1e-6, "max-flow = min-cut");
  // inverse-capacity shortest path to a forward port (gates charged, primaries not)
  const dist = new Array(N).fill(Infinity);
  for (const p of st.F) if (cap[p] > EPS) dist[p] = 0;
  for (let v = N - 1; v >= C.n; v--) {
    if (C.S[v] !== 0 || !(cap[v] > EPS) || !Number.isFinite(dist[v])) continue;
    for (const l of C.E[v - C.n]) {
      const u = l >> 1;
      if (C.S[u] === 0 && cap[u] > EPS) dist[u] = Math.min(dist[u], dist[v] + 1 / cap[v]);
    }
  }
  return { flow, cut, dist };
}

// ---- full semantic analysis on a small instance -----------------------------------------
const stats = {
  instances: 0, vertices: 0, plus_below_old: 0, chi_below_minTG: 0, chi_below_plus: 0, G_below_T: 0, T_below_G: 0,
  cuts_tested: 0, decoder_evaluations: 0, joint_below_product: 0,
  mincut_plus_below_old: 0, mincut_chi_below_plus: 0, injective_instances: 0,
  charge_plus_above_old: 0, charge_chi_above_plus: 0, max_charge_old: 0, max_charge_plus: 0, max_charge_chi: 0,
  controls: [],
};

function analyze(C, out, U, fixedA, label) {
  ok(C.S[out >> 1] === 1, "output owned by B");
  const N = nv(C), st = structure(C, U);
  const Bprim = []; for (let i = 0; i < C.n; i++) if (C.S[i] === 1) Bprim.push(i);
  const nx = 1 << U.length, ny = 1 << Bprim.length;
  // full value table
  const full = [];
  for (let xi = 0; xi < nx; xi++) {
    const row = [];
    for (let yi = 0; yi < ny; yi++) {
      const inp = new Uint8Array(C.n);
      for (let i = 0; i < C.n; i++) if (C.S[i] === 0) inp[i] = fixedA[i] || 0;
      U.forEach((u, b) => { inp[u] = (xi >> b) & 1; });
      Bprim.forEach((u, b) => { inp[u] = (yi >> b) & 1; });
      row.push(evalAll(C, inp));
    }
    full.push(row);
  }
  const outv = (xi, yi) => full[xi][yi][out >> 1] ^ (out & 1);
  const resid = []; for (let xi = 0; xi < nx; xi++) { let s = ""; for (let yi = 0; yi < ny; yi++) s += outv(xi, yi); resid.push(s); }
  const Nres = new Set(resid).size, logN = lg(Nres);
  // local response tables with all reverse ports formal
  const rev = st.Rev, nz = 1 << rev.length, rix = new Map(rev.map((u, i) => [u, i]));
  const Tkey = Array.from({ length: N }, () => new Array(nx));
  for (let xi = 0; xi < nx; xi++) {
    const cols = Array.from({ length: N }, () => []);
    for (let z = 0; z < nz; z++) {
      const W = new Uint8Array(N);
      for (let i = 0; i < C.n; i++) if (C.S[i] === 0) W[i] = fixedA[i] || 0;
      U.forEach((u, b) => { W[u] = (xi >> b) & 1; });
      const lit = (l) => { const u = l >> 1; return (C.S[u] === 0 ? W[u] : (z >> rix.get(u)) & 1) ^ (l & 1); };
      for (let j = 0; j < C.E.length; j++) if (C.S[C.n + j] === 0) W[C.n + j] = lit(C.E[j][0]) & lit(C.E[j][1]);
      for (let v = 0; v < N; v++) if (C.S[v] === 0) cols[v].push(W[v]);
    }
    for (let v = 0; v < N; v++) if (C.S[v] === 0) Tkey[v][xi] = cols[v].join("");
  }
  const capOld = new Array(N).fill(0), capPlus = new Array(N).fill(0), capT = new Array(N).fill(0),
    capG = new Array(N).fill(0), capChi = new Array(N).fill(0), color = Array.from({ length: N }, () => null);
  for (let v = 0; v < N; v++) {
    if (C.S[v] !== 0) continue;
    const d = st.D[v].size, r = st.R[v].size;
    capOld[v] = Math.min(d, 2 ** r);
    const mu = muOf(C, st, Bprim, v);
    capPlus[v] = mu === null ? 0 : Math.min(d, 2 ** r, 2 ** mu);
    if (mu !== null) ok(mu <= Bprim.length, "mu <= |Y|");
    const nT = new Set(Tkey[v]).size;
    const Gk = []; for (let xi = 0; xi < nx; xi++) { let s = ""; for (let yi = 0; yi < ny; yi++) s += full[xi][yi][v]; Gk.push(s); }
    const nG = new Set(Gk).size;
    capT[v] = lg(nT); capG[v] = lg(nG);
    // conflict graph and greedy colouring
    const Rv = [...st.R[v]];
    const hist = (xi, yi) => Rv.map((u) => full[xi][yi][u]).join("");
    const adj = Array.from({ length: nx }, () => []);
    for (let a = 0; a < nx; a++) for (let b = a + 1; b < nx; b++) {
      for (let yi = 0; yi < ny; yi++) if (full[a][yi][v] !== full[b][yi][v] && hist(a, yi) === hist(b, yi)) { adj[a].push(b); adj[b].push(a); break; }
    }
    const order = [...Array(nx).keys()].sort((a, b) => adj[b].length - adj[a].length || a - b), col = new Array(nx).fill(-1);
    for (const a of order) { const used = new Set(adj[a].map((b) => col[b])); let c = 0; while (used.has(c)) c++; col[a] = c; }
    for (let a = 0; a < nx; a++) for (const b of adj[a]) ok(col[a] !== col[b], "proper colouring");
    // equal T or equal G never conflict (so chi <= min(#T, #G))
    for (let a = 0; a < nx; a++) for (const b of adj[a]) ok(Tkey[v][a] !== Tkey[v][b] && Gk[a] !== Gk[b], "T/G-equal pairs are compatible");
    const nChi = Math.max(...col) + 1;
    color[v] = col; capChi[v] = lg(nChi);
    // assertions on the capacity hierarchy
    ok(nT <= 2 ** capOld[v] + EPS, "#T <= 2^c_old");
    ok(capG[v] <= Math.min(st.Ds[v].size, mu === null ? 0 : 2 ** mu) + EPS, "c_G <= min(|D*|,2^mu)");
    ok(capPlus[v] + EPS >= Math.min(capT[v], capG[v]), "c_plus >= min(c_T,c_G)");
    ok(capPlus[v] <= capOld[v], "c_plus <= c_old");
    stats.vertices++;
    if (capPlus[v] < capOld[v]) stats.plus_below_old++;
    if (capG[v] < capT[v] - EPS) stats.G_below_T++;
    if (capT[v] < capG[v] - EPS) stats.T_below_G++;
    if (capChi[v] < Math.min(capT[v], capG[v]) - EPS) stats.chi_below_minTG++;
    if (capChi[v] < capPlus[v] - EPS) stats.chi_below_plus++;
  }
  // cut family
  const cuts = new Map();
  const addCut = (K) => { K = [...new Set(K)].sort((a, b) => a - b); if (isCut(C, st, K)) cuts.set(K.join(","), K); };
  addCut(st.F); addCut(U);
  let K = new Set(st.F);
  for (let step = 0; step < 10; step++) {
    const g = [...K].filter((v) => v >= C.n); if (!g.length) break;
    const v = g[rnd(g.length)]; K.delete(v);
    for (const l of C.E[v - C.n]) if (C.S[l >> 1] === 0) K.add(l >> 1);
    addCut([...K]);
  }
  const Avert = []; for (let v = 0; v < N; v++) if (C.S[v] === 0) Avert.push(v);
  for (let t = 0; t < 8; t++) addCut(Avert.filter(() => rnd(3) === 0));
  const fo = causalFlow(C, st, capOld), fp = causalFlow(C, st, capPlus), fc = causalFlow(C, st, capChi);
  addCut(fo.cut); addCut(fp.cut); addCut(fc.cut);
  ok(fo.flow + EPS >= logN && fp.flow + EPS >= logN && fc.flow + EPS >= logN, "flow >= log2 N (" + label + ")");
  if (fp.flow < fo.flow - EPS) stats.mincut_plus_below_old++;
  if (fc.flow < fp.flow - EPS) stats.mincut_chi_below_plus++;
  for (const K of cuts.values()) {
    stats.cuts_tested++;
    const sum = (cap) => K.reduce((a, v) => a + cap[v], 0);
    ok(logN <= sum(capChi) + EPS && sum(capChi) <= sum(capPlus) + EPS && sum(capPlus) <= sum(capOld), "cut capacities (" + label + ")");
    // joint colour vectors
    const joint = new Set(); for (let xi = 0; xi < nx; xi++) joint.add(K.map((v) => color[v][xi]).join(","));
    ok(lg(joint.size) + EPS >= logN, "joint code count >= N");
    if (lg(joint.size) < sum(capChi) - EPS) stats.joint_below_product++;
    // colour decoder: knows only colours at K, y, and values it has itself simulated
    const codeToResid = new Map();
    for (let xi = 0; xi < nx; xi++) {
      const code = K.map((v) => color[v][xi]).join(",");
      let sig = "";
      for (let yi = 0; yi < ny; yi++) {
        const V = new Uint8Array(N), Ks = new Set(K);
        for (let i = 0; i < C.n; i++) V[i] = C.S[i] === 1 ? (yi >> Bprim.indexOf(i)) & 1 : (st.Uset.has(i) ? 0 : (fixedA[i] || 0));
        const decide = (v) => {
          const Rv = [...st.R[v]], h = Rv.map((u) => V[u]).join("");
          // any assignment of the same colour realising (y, h)
          let rep = -1;
          for (let x2 = 0; x2 < nx && rep < 0; x2++) if (color[v][x2] === color[v][xi] && Rv.map((u) => full[x2][yi][u]).join("") === h) rep = x2;
          ok(rep >= 0, "decoder representative exists");
          V[v] = full[rep][yi][v];
        };
        for (let i = 0; i < C.n; i++) if (Ks.has(i)) decide(i);
        for (let j = 0; j < C.E.length; j++) {
          const v = C.n + j, [a, b] = C.E[j];
          V[v] = (V[a >> 1] ^ (a & 1)) & (V[b >> 1] ^ (b & 1));
          if (Ks.has(v)) decide(v);
        }
        const got = V[out >> 1] ^ (out & 1);
        ok(got === outv(xi, yi), "colour decoder reconstructs output (" + label + ")");
        sig += got; stats.decoder_evaluations++;
      }
      if (codeToResid.has(code)) ok(codeToResid.get(code) === sig, "equal colour vectors give equal residuals");
      codeToResid.set(code, sig);
    }
  }
  // additive charge under injectivity
  const sA = C.E.filter((_, j) => C.S[C.n + j] === 0).length;
  let charges = null;
  if (Nres === nx) {
    stats.injective_instances++;
    const ch = (f) => U.reduce((a, i) => a + f.dist[i], 0);
    const co = ch(fo), cp = ch(fp), cc = ch(fc);
    ok(Number.isFinite(cc) && co <= cp + EPS && cp <= cc + EPS && cc <= sA + EPS, "weighted charges <= s_A (" + label + ")");
    if (cp > co + EPS) stats.charge_plus_above_old++;
    if (cc > cp + EPS) stats.charge_chi_above_plus++;
    stats.max_charge_old = Math.max(stats.max_charge_old, co);
    stats.max_charge_plus = Math.max(stats.max_charge_plus, cp);
    stats.max_charge_chi = Math.max(stats.max_charge_chi, cc);
    charges = { old: +co.toFixed(3), plus: +cp.toFixed(3), chi: +cc.toFixed(3) };
  }
  stats.instances++;
  return { label, data: U.length, bob: Bprim.length, gatesA: sA, gates: C.E.length, log2N: +logN.toFixed(3),
    mincut: { old: +fo.flow.toFixed(3), plus: +fp.flow.toFixed(3), chi: +fc.flow.toFixed(3) },
    portCap: { old: st.F.reduce((a, v) => a + capOld[v], 0), plus: st.F.reduce((a, v) => a + capPlus[v], 0), chi: +st.F.reduce((a, v) => a + capChi[v], 0).toFixed(3) },
    charges };
}

// Structural-only analysis for larger topologies (no truth tables).
function structural(C, U, label, need) {
  const st = structure(C, U), N = nv(C);
  const Bprim = []; for (let i = 0; i < C.n; i++) if (C.S[i] === 1) Bprim.push(i);
  const capOld = new Array(N).fill(0), capPlus = new Array(N).fill(0);
  for (let v = 0; v < N; v++) if (C.S[v] === 0) {
    const d = st.D[v].size, r = st.R[v].size, mu = muOf(C, st, Bprim, v);
    capOld[v] = Math.min(d, 2 ** r); capPlus[v] = mu === null ? 0 : Math.min(d, 2 ** r, 2 ** mu);
  }
  const fo = causalFlow(C, st, capOld), fp = causalFlow(C, st, capPlus);
  const r = { label, data: U.length, gates: C.E.length, ports: st.F.length, reverse: st.Rev.length, need,
    portCap: { old: st.F.reduce((a, v) => a + capOld[v], 0), plus: st.F.reduce((a, v) => a + capPlus[v], 0) },
    mincut: { old: fo.flow, plus: fp.flow } };
  r.rejects = { old: fo.flow < need, plus: fp.flow < need };
  return r;
}

// ---- 1. random signed AIGs ----------------------------------------------------------------
let randomDone = 0;
for (let t = 0; t < 400 && randomDone < 160; t++) {
  const n = 3 + rnd(4), side = Array.from({ length: n }, () => rnd(2));
  if (!side.includes(0) || !side.includes(1)) continue;
  const C = Circuit(n, side), g = 3 + rnd(9);
  let out;
  for (let j = 0; j < g; j++) out = C.AND(2 * rnd(n + j) + rnd(2), 2 * rnd(n + j) + rnd(2), j === g - 1 ? 1 : rnd(2));
  const A = [...Array(n).keys()].filter((i) => side[i] === 0);
  const U = A.filter((i, k) => k === 0 || rnd(4) > 0), fixedA = {};
  for (const i of A) if (!U.includes(i)) fixedA[i] = rnd(2);
  const st = structure(C, U);
  if (st.Rev.length > 8) continue;
  analyze(C, out, U, fixedA, "random");
  randomDone++;
}
stats.random_instances = randomDone;

// ---- 2. data-dependent feedback carrying few Bob bits (Bob-entropy detection) -------------
// Data x in A is forwarded; B returns many data-dependent reverse wires that carry only one
// query bit through a single data-free vertex b. c_old counts 2^|R|; c_plus counts 2^mu = 2.
function echo(k, g, wantSemantics) {
  const M = k * g, n = M + k, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= M)));
  const data = (i, j) => 2 * (i * g + j), q = (i) => 2 * (M + i);
  const z = []; for (let i = 0; i < k; i++) { let p = data(i, 0); for (let j = 1; j < g; j++) p = C.XOR(p, data(i, j), 0); z.push(p); }
  let b = q(0); for (let i = 1; i < k; i++) b = C.AND(b, q(i), 1);           // data-free, in B
  const e = z.map((zi) => C.AND(zi, b, 1));                                   // data-dependent reverse wires
  const w = [];
  for (let i = 0; i < k; i++) {
    let acc = null;
    for (let j = 0; j < g; j++) { const u = C.XOR(data(i, j), e[j % k], 0); acc = acc === null ? u : C.XOR(acc, u, 0); }
    w.push(acc);
  }
  const out = w.reduce((a, c) => C.AND(a, c, 1));
  const U = [...Array(M).keys()];
  const r = structural(C, U, "echo k=" + k + " g=" + g, M);
  if (wantSemantics) {
    // exact residual count (data 2^M x Bob 2^k), checked against both min cuts
    const res = new Set();
    for (let x = 0; x < 1 << M; x++) {
      let s = "";
      for (let y = 0; y < 1 << k; y++) {
        const inp = new Uint8Array(n);
        for (let i = 0; i < M; i++) inp[i] = (x >> i) & 1;
        for (let i = 0; i < k; i++) inp[M + i] = (y >> i) & 1;
        const V = evalAll(C, inp); s += V[out >> 1] ^ (out & 1);
      }
      res.add(s);
    }
    r.log2N = lg(res.size);
    ok(r.log2N <= r.mincut.plus + EPS, "echo: actual residuals obey c_plus");
  }
  return r;
}
for (const [k, g] of [[2, 2], [3, 2], [4, 4], [5, 7], [6, 11], [7, 19]]) stats.controls.push(echo(k, g, k <= 3));
for (const r of stats.controls.filter((r) => r.label.startsWith("echo") && r.data >= 16)) ok(!r.rejects.old && r.rejects.plus, "echo: old passes, plus rejects INDEX demand");

// ---- 3. committed strict topologies (local and all-feedback) ------------------------------
for (let k = 4; k <= 7; k++) for (const all of [false, true]) {
  const M = 2 ** k, n = M + k, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= M)));
  const groups = Array.from({ length: k }, () => []);
  for (let i = 0; i < M; i++) groups[i % k].push(2 * i);
  const z = groups.map((G) => G.reduce((a, b) => C.XOR(a, b, 0)));
  const gq = all ? Array.from({ length: k }, (_, i) => 2 * (M + i)).reduce((a, b) => C.XOR(a, b, 0)) : 0;
  const out = z.map((v, i) => C.XOR(v, all ? gq : 2 * (M + i), 0)).reduce((a, b) => C.AND(a, b, 1));
  const r = structural(C, [...Array(M).keys()], (all ? "all-feedback" : "local-feedback") + " k=" + k, M);
  ok(r.rejects.old && r.rejects.plus, "strict topology rejected");
  if (all) ok(r.portCap.old === M && r.portCap.plus === 2 * k, "all-feedback: c_plus already rejects at ports");
  stats.controls.push(r);
}

// ---- 4. early feedback: INDEX mux trees (queries reach data first) and late feedback ------
function muxTree(k, sideOf) {
  const M = 2 ** k, n = M + k, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= M)));
  let V = Array.from({ length: M }, (_, i) => 2 * i);
  for (let j = 0; j < k; j++) { const W = []; for (let i = 0; i < V.length; i += 2) W.push(C.MUX(2 * (M + j), V[i], V[i + 1], sideOf(j))); V = W; }
  return { C, out: C.AND(V[0], V[0], 1), M };
}
for (let k = 1; k <= 3; k++) {
  const { C, out, M } = muxTree(k, () => 0);
  stats.controls.push(analyze(C, out, [...Array(M).keys()], {}, "INDEX mux tree in A, k=" + k));
  const h = muxTree(k, (j) => +(j >= 1));
  stats.controls.push(analyze(h.C, h.out, [...Array(h.M).keys()], {}, "INDEX mux, level>=1 in B, k=" + k));
}
for (let k = 4; k <= 7; k++) { const { C, M } = muxTree(k, () => 0); stats.controls.push(structural(C, [...Array(M).keys()], "INDEX mux tree in A (structural), k=" + k, M)); }

// ---- 5. programmable permutation network (data in A, switch controls on B) ---------------
function benes(m, sideSwitch) {
  // butterfly-of-butterflies on m = 4 wires with controls as Bob primaries; output reads wire 0
  const n = m + 6, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= m)));
  let W = Array.from({ length: m }, (_, i) => 2 * i), c = m;
  const sw = (a, b) => { const s = 2 * c++; return [C.MUX(s, W[a], W[b], sideSwitch), C.MUX(s, W[b], W[a], sideSwitch)]; };
  for (const [a, b] of [[0, 1], [2, 3], [0, 2], [1, 3], [0, 1], [2, 3]]) [W[a], W[b]] = sw(a, b);
  return { C, out: C.AND(W[0], W[0], 1) };
}
{ const { C, out } = benes(4, 0); stats.controls.push(analyze(C, out, [0, 1, 2, 3], {}, "programmable 4-wire network, switches in A")); }

// ---- 6. enabled lookup (fixed pi): r groups, AND_j (NOT E_j OR table_j[q_j]) --------------
{
  const r = 2, k = 1, M = 2, n = r * M + r * k + r, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= r * M)));
  const terms = [];
  for (let j = 0; j < r; j++) {
    const v = C.MUX(2 * (r * M + j), 2 * (j * M), 2 * (j * M + 1), 0);
    terms.push(C.OR(2 * (r * M + r * k + j) ^ 1, v, 1));
  }
  const out = terms.reduce((a, b) => C.AND(a, b, 1));
  stats.controls.push(analyze(C, out, [...Array(r * M).keys()], {}, "enabled lookup r=2 M=2 (fixed pi)"));
}

// ---- 7. tautology padding: inflates syntactic capacities, not semantic ones ---------------
{
  const k = 2, M = 4, n = M + k, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= M)));
  const taut = (j) => C.AND(2 * (M + j), 2 * (M + j) ^ 1, 1) ^ 1;        // constant 1, data-free, in B
  let V = Array.from({ length: M }, (_, i) => C.AND(C.AND(2 * i, taut(0), 0), taut(1), 0));
  for (let j = 0; j < k; j++) { const W = []; for (let i = 0; i < V.length; i += 2) W.push(C.MUX(2 * (M + j), V[i], V[i + 1], 0)); V = W; }
  const out = C.AND(V[0], V[0], 1);
  stats.controls.push(analyze(C, out, [0, 1, 2, 3], {}, "INDEX k=2 with tautology padding"));
}

// ---- 8. tautological Bob dependence fools BOTH structural capacities ----------------------
// Local-feedback compress-then-query topology on 8 data bits (groups 3,3,2), with every
// parity tree leaf ANDed with t_j = NOT(q_j AND NOT q_j) (constant 1, data-free, in B).
// Structurally R and mu grow to 3, so c_old = c_plus = |D| on the parity roots and the INDEX
// demand of 8 passes; the semantic colouring capacity sees constants and rejects.
{
  const k = 3, M = 8, n = M + k, C = Circuit(n, Array.from({ length: n }, (_, i) => +(i >= M)));
  const t = Array.from({ length: k }, (_, j) => C.AND(2 * (M + j), 2 * (M + j) ^ 1, 1) ^ 1);
  const groups = [[0, 3, 6], [1, 4, 7], [2, 5]];
  const z = groups.map((G) => G.map((i, a) => C.AND(2 * i, t[a % k], 0)).reduce((a, b) => C.XOR(a, b, 0)));
  const z2 = z.map((v, i) => C.AND(v, t[(i + 1) % k], 0));
  const out = z2.map((v, i) => C.XOR(v, 2 * (M + i), 0)).reduce((a, b) => C.AND(a, b, 1));
  const r = analyze(C, out, [...Array(M).keys()], {}, "tautology-inflated local feedback, 8 data");
  ok(r.mincut.old >= M && r.mincut.plus >= M && r.mincut.chi < M, "structural fooled, semantic rejects INDEX demand");
  r.need = M; stats.controls.push(r);
}

// ---- 9. falsification sweep: c_plus min cut vs exact residual count ----------------------
// Larger random circuits with heavy B->A->B->A interleaving; only the structural c_plus cut is
// tested against the exact number of residual functions (no colouring).
stats.sweep = { circuits: 0, plus_tight: 0, plus_below_old: 0, max_gates: 0 };
for (let t = 0; stats.sweep.circuits < 1500 && t < 20000; t++) {
  const n = 4 + rnd(5), side = Array.from({ length: n }, () => rnd(2));
  if (!side.includes(0) || !side.includes(1)) continue;
  const C = Circuit(n, side), g = 6 + rnd(20);
  let out;
  for (let j = 0; j < g; j++) out = C.AND(2 * rnd(n + j) + rnd(2), 2 * rnd(n + j) + rnd(2), j === g - 1 ? 1 : rnd(2));
  const U = [...Array(n).keys()].filter((i) => side[i] === 0);
  const r = structural(C, U, "sweep", U.length);
  const Bp = [...Array(n).keys()].filter((i) => side[i] === 1), res = new Set();
  for (let x = 0; x < 1 << U.length; x++) {
    let s = "";
    for (let y = 0; y < 1 << Bp.length; y++) {
      const inp = new Uint8Array(n);
      U.forEach((u, b) => { inp[u] = (x >> b) & 1; }); Bp.forEach((u, b) => { inp[u] = (y >> b) & 1; });
      const V = evalAll(C, inp); s += V[out >> 1] ^ (out & 1);
    }
    res.add(s);
  }
  ok(lg(res.size) <= r.mincut.plus + EPS && r.mincut.plus <= r.mincut.old + EPS, "sweep: log2 N <= mincut_plus <= mincut_old");
  stats.sweep.circuits++;
  if (Math.abs(lg(res.size) - r.mincut.plus) < EPS) stats.sweep.plus_tight++;
  if (r.mincut.plus < r.mincut.old - EPS) stats.sweep.plus_below_old++;
  stats.sweep.max_gates = Math.max(stats.sweep.max_gates, C.E.length);
}

console.log(JSON.stringify(stats, null, 1));
console.log("all assertions passed");
