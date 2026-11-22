// Push-optimal Sokoban solver for make.fun's room-and-hallway levels.
// Boxes never leave their room (a box pushed into the hallway is lost), so each room is solved on its own by an
// exhaustive breadth-first search over pushes (state: sorted boxes + the player's reachable area), which is
// push-optimal and deterministic. The rooms' pushes are then replayed on the whole level with walking moves between.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

function solve(text: string): string {
  const rows = text.replace(/\r/g, '').split('\n');
  while (rows.length && rows[rows.length - 1].trim() === '') rows.pop();
  const H = rows.length, W = Math.max(...rows.map((r) => r.length)) + 2; // padded so +-1 never wraps onto floor
  const N = H * W, wall = new Uint8Array(N).fill(1), goal = new Uint8Array(N), box = new Uint8Array(N);
  let pl = -1;
  rows.forEach((row, r) => [...row].forEach((ch, c) => {
    const i = r * W + c + 1;
    if (ch === '#') return;
    wall[i] = 0;
    if ('.*+'.includes(ch)) goal[i] = 1;
    if ('$*'.includes(ch)) box[i] = 1;
    if ('@+'.includes(ch)) pl = i;
  }));
  const D = [-W, W, -1, 1], L = 'udlr';
  const hr = Math.floor(pl / W);
  // Rooms: connected floor components off the hallway row.
  const comp = new Int32Array(N).fill(-1), rooms: number[][] = [];
  for (let s = 0; s < N; s++) {
    if (wall[s] || comp[s] >= 0 || Math.floor(s / W) === hr) continue;
    const id = rooms.length, cells = [s];
    comp[s] = id;
    for (let k = 0; k < cells.length; k++) for (const d of D) {
      const t = cells[k] + d;
      if (t >= 0 && t < N && !wall[t] && comp[t] < 0 && Math.floor(t / W) !== hr) { comp[t] = id; cells.push(t); }
    }
    rooms.push(cells);
  }
  const pushes: [number, number][] = [];
  for (const cells of rooms) {
    const bx = cells.filter((c) => box[c]);
    if (!bx.length) continue;
    // Local graph: the room's cells plus the hallway cells touching it (player-only).
    const loc = [...cells];
    for (const c of cells) for (const d of [-W, W]) if (Math.floor((c + d) / W) === hr && !wall[c + d] && !loc.includes(c + d)) loc.push(c + d);
    const M = loc.length, idx = new Map(loc.map((c, i) => [c, i])), nb: number[][] = [];
    for (let i = 0; i < M; i++) nb.push(D.map((d) => idx.get(loc[i] + d) ?? -1));
    const R = cells.length, room = (i: number) => i >= 0 && i < R;
    const gi = new Int32Array(N).fill(-1); loc.forEach((c, i) => { gi[c] = i; });
    // hd[i]: pushes a lone box at i needs to reach a goal (-1: never, a dead square). Admissible and consistent.
    const hd = new Int32Array(M).fill(-1), q: number[] = [];
    for (let i = 0; i < R; i++) if (goal[loc[i]]) { hd[i] = 0; q.push(i); }
    for (let k = 0; k < q.length; k++) for (let d = 0; d < 4; d++) {
      const x = nb[q[k]][d ^ 1], p = x >= 0 ? nb[x][d ^ 1] : -1; // box came from x, pushed from p
      if (room(x) && p >= 0 && hd[x] < 0) { hd[x] = hd[q[k]] + 1; q.push(x); }
    }
    const K = bx.length, B = M + 1;
    const enc = (b: number[], p: number) => b.reduce((a, v) => a * B + v, 0) * B + p;
    // reach() marks the player's area with a fresh stamp (no clearing) and returns its smallest cell.
    const occ = new Uint8Array(M), seen = new Int32Array(M), vis = new Int32Array(M), stk = new Int32Array(M);
    let stamp = 0;
    const reach = (p: number, sn: Int32Array) => {
      const g = ++stamp; let n = 0, m = p; stk[n++] = p; sn[p] = g;
      while (n) {
        const u = stk[--n], a = nb[u]; if (u < m) m = u;
        for (let e = 0; e < 4; e++) { const v = a[e]; if (v >= 0 && sn[v] !== g && !occ[v]) { sn[v] = g; stk[n++] = v; } }
      }
      return m;
    };
    const start = bx.map((c) => idx.get(c)!).sort((a, b) => a - b);
    const p0 = idx.get(loc.find((c) => Math.floor(c / W) === hr)!)!;
    if (start.every((v) => goal[loc[v]])) continue;
    for (const v of start) occ[v] = 1;
    const k0 = enc(start, reach(p0, seen));
    for (const v of start) occ[v] = 0;
    // A* over pushes with a bucket queue by f = g + h, FIFO within a bucket (deterministic).
    type Node = [number[], number, number, number, number]; // boxes, player, key, g, h
    const best = new Map<number, number>([[k0, 0]]), par = new Map<number, [number, number, number]>([[k0, [-1, 0, 0]]]);
    const h0 = start.reduce((a, v) => a + hd[v], 0), bk: Node[][] = [];
    (bk[h0] = []).push([start, p0, k0, 0, h0]);
    let end = -1;
    search: for (let f = h0; f < bk.length; f++) {
      const bucket = bk[f];
      if (!bucket) continue;
      for (let qi = 0; qi < bucket.length; qi++) {
        const [b, p, key, g, h] = bucket[qi];
        if (best.get(key) !== g) continue;
        if (h === 0) { end = key; break search; } // h is 0 only with every box on a goal
        for (const v of b) occ[v] = 1;
        reach(p, vis);
        const vg = stamp;
        for (let j = 0; j < K; j++) for (let d = 0; d < 4; d++) {
          const fr = nb[b[j]][d ^ 1], t = nb[b[j]][d];
          if (fr < 0 || vis[fr] !== vg || !room(t) || occ[t] || hd[t] < 0) continue;
          occ[b[j]] = 0; occ[t] = 1;
          // freeze check: the moved box stuck in a 2x2 block of walls and boxes, one box off its goal
          let dead = false;
          for (let a = 0; a < 2 && !dead; a++) for (let c = 2; c < 4 && !dead; c++) {
            const g0 = loc[t], g1 = g0 + D[a], g2 = g0 + D[c], g3 = g1 + D[c];
            let all = true, off = false;
            for (let z = 0; z < 4; z++) {
              const s2 = z === 0 ? g0 : z === 1 ? g1 : z === 2 ? g2 : g3, i = gi[s2], isB = i >= 0 && i < R && occ[i] === 1;
              if (!wall[s2] && !isB) { all = false; break; }
              if (isB && !goal[s2]) off = true;
            }
            dead = all && off;
          }
          let nb2: number[] = [], nk = -1;
          if (!dead) { nb2 = b.slice(); nb2[j] = t; nb2.sort((x, y) => x - y); nk = enc(nb2, reach(b[j], seen)); }
          occ[t] = 0; occ[b[j]] = 1;
          if (dead) continue;
          const old = best.get(nk);
          if (old !== undefined && old <= g + 1) continue;
          best.set(nk, g + 1); par.set(nk, [key, b[j], d]);
          const nh = h - hd[b[j]] + hd[t];
          (bk[g + 1 + nh] ??= []).push([nb2, b[j], nk, g + 1, nh]);
        }
        for (const v of b) occ[v] = 0;
      }
    }
    if (end < 0) continue; // unsolvable room: leave it (never seen)
    const seq: [number, number][] = [];
    for (let k = end; par.get(k)![0] >= 0; k = par.get(k)![0]) { const [, b, d] = par.get(k)!; seq.push([loc[b], d]); }
    pushes.push(...seq.reverse());
  }
  // Replay on the whole level: walk to each push's square, then push.
  let out = '';
  for (const [b, d] of pushes) {
    const tgt = b - D[d], prev = new Int32Array(N).fill(-1), q = [pl];
    prev[pl] = pl;
    for (let k = 0; k < q.length && prev[tgt] < 0; k++) for (let e = 0; e < 4; e++) {
      const v = q[k] + D[e];
      if (v >= 0 && v < N && !wall[v] && !box[v] && prev[v] < 0) { prev[v] = q[k]; q.push(v); }
    }
    let walk = '';
    for (let v = tgt; v !== pl; v = prev[v]) walk = L[D.indexOf(v - prev[v])] + walk;
    out += walk + L[d].toUpperCase();
    box[b] = 0; box[b + D[d]] = 1; pl = b;
  }
  return out;
}

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
