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
    const room = (i: number) => i >= 0 && i < cells.length;
    // Live squares: a lone box there can still be pushed onto a goal.
    const live = new Uint8Array(M), q: number[] = [];
    for (let i = 0; i < cells.length; i++) if (goal[loc[i]]) { live[i] = 1; q.push(i); }
    for (let k = 0; k < q.length; k++) for (let d = 0; d < 4; d++) {
      const x = nb[q[k]][d ^ 1], p = x >= 0 ? nb[x][d ^ 1] : -1; // box came from x, pushed from p
      if (room(x) && p >= 0 && !live[x]) { live[x] = 1; q.push(x); }
    }
    const K = bx.length, B = M + 1;
    const enc = (b: number[], p: number) => b.reduce((a, v) => a * B + v, 0) * B + p;
    const occ = new Uint8Array(M), seen = new Uint8Array(M), stk: number[] = [];
    const reach = (p: number) => { // fills seen[], returns min reachable cell
      seen.fill(0); stk.length = 0; stk.push(p); seen[p] = 1; let m = p;
      while (stk.length) { const u = stk.pop()!; if (u < m) m = u; for (const v of nb[u]) if (v >= 0 && !seen[v] && !occ[v]) { seen[v] = 1; stk.push(v); } }
      return m;
    };
    const start = bx.map((c) => idx.get(c)!).sort((a, b) => a - b);
    let p0 = idx.get(loc.find((c) => Math.floor(c / W) === hr)!)!;
    for (const b of start) occ[b] = 1;
    const k0 = enc(start, reach(p0));
    for (const b of start) occ[b] = 0;
    const par = new Map<number, [number, number, number]>([[k0, [-1, 0, 0]]]);
    let fr: [number[], number, number][] = [[start, p0, k0]], end = -1;
    const done = (b: number[]) => b.every((v) => goal[loc[v]]);
    if (done(start)) continue;
    search: while (fr.length) {
      const nx: [number[], number, number][] = [];
      for (const [b, p, key] of fr) {
        for (const v of b) occ[v] = 1;
        reach(p);
        const vis = Uint8Array.from(seen);
        for (let j = 0; j < K; j++) for (let d = 0; d < 4; d++) {
          const f = nb[b[j]][d ^ 1], t = nb[b[j]][d];
          if (f < 0 || !vis[f] || !room(t) || occ[t] || !live[t]) continue;
          const nb2 = b.slice(); nb2[j] = t; nb2.sort((x, y) => x - y);
          occ[b[j]] = 0; occ[t] = 1;
          // freeze check: the moved box stuck in a 2x2 block with a box off its goal
          let dead = false;
          for (const [a, c] of [[0, 2], [0, 3], [1, 2], [1, 3]]) {
            const g = [loc[t], loc[t] + D[a], loc[t] + D[c], loc[t] + D[a] + D[c]];
            const bx2 = (s: number) => { const i = idx.get(s); return i !== undefined && room(i) && occ[i] === 1; };
            if (g.every((s) => wall[s] || bx2(s)) && g.some((s) => bx2(s) && !goal[s])) { dead = true; break; }
          }
          let nk = -1;
          if (!dead) { nk = enc(nb2, reach(b[j])); }
          occ[t] = 0; occ[b[j]] = 1;
          if (dead || par.has(nk)) continue;
          par.set(nk, [key, b[j], d]);
          if (done(nb2)) { end = nk; for (const v of b) occ[v] = 0; break search; }
          nx.push([nb2, b[j], nk]);
        }
        for (const v of b) occ[v] = 0;
      }
      fr = nx;
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
