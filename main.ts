// Tiny stack VM for make.fun's tiny stack ISA (kit generator/subject/ISA.md).
// node main.ts: runs every /input/<id>/ program on its input, writes
// /output/<id>/stdout.bin and /output/<id>/exit.txt. Follows the reference VM
// (generator/subject/vm.mjs): same trap order and codes, wrapping 32-bit math,
// exact DIV/MOD/DIVU/MODU/SHRU edges, 1M-step and 64K-output limits.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// [immediate bytes, pops, pushes] per opcode; an opcode not listed is trap 5.
const T = new Map<number, [number, number, number]>([
  [0, [0, 0, 0]], [1, [1, 0, 1]], [2, [4, 0, 1]], [3, [0, 1, 0]], [4, [0, 1, 2]],
  [5, [0, 2, 2]], [6, [0, 2, 3]], [7, [0, 3, 3]], [16, [0, 2, 1]], [17, [0, 2, 1]],
  [18, [0, 2, 1]], [19, [0, 2, 1]], [20, [0, 2, 1]], [21, [0, 2, 1]], [22, [0, 2, 1]],
  [23, [0, 1, 1]], [24, [0, 2, 1]], [25, [0, 2, 1]], [26, [0, 2, 1]], [27, [0, 1, 1]],
  [28, [0, 2, 1]], [29, [0, 2, 1]], [30, [0, 2, 1]], [32, [0, 2, 1]], [33, [0, 2, 1]],
  [34, [0, 2, 1]], [48, [2, 0, 0]], [49, [2, 1, 0]], [50, [2, 1, 0]], [51, [2, 0, 0]],
  [52, [0, 0, 0]], [64, [0, 1, 1]], [65, [0, 2, 0]], [80, [0, 1, 0]], [81, [0, 1, 0]],
  [82, [0, 0, 1]], [83, [0, 1, 0]],
]);
const IM = new Int8Array(256), PO = new Int8Array(256), PU = new Int8Array(256), OK = new Uint8Array(256);
for (const [o, [i, a, b]] of T) { IM[o] = i; PO[o] = a; PU[o] = b; OK[o] = 1; }
const enc = new TextEncoder();
function run(p: Buffer, q: Buffer): { out: Uint8Array; code: number } {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, st = 0, ip = 0, ol = 0;
  const done = (code: number) => ({ out: out.subarray(0, ol), code });
  for (;;) {
    if (st === 1000000) return done(10);
    if (pc < 0 || pc >= p.length) return done(9);
    const op = p[pc];
    if (!OK[op]) return done(5);
    const im = IM[op], pp = PO[op], pu = PU[op];
    if (pc + im >= p.length) return done(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < pp) return done(2);
    if (sp - pp + pu > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0: return done(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24: case 25:
      case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r = 0;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19: if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 20: if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; break;
          case 21: if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 22: if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          case 34: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2; D[sp++] = r; break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return done(7);
        C[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 52:
        if (cp === 0) return done(8);
        pc = C[--cp]; break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return done(6);
        D[sp - 1] = M[a]; break;
      }
      case 65: {
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return done(6);
        sp -= 2; M[a] = v; break;
      }
      case 80: {
        const s = enc.encode(String(D[sp - 1]));
        if (ol + s.length > 65536) return done(11);
        sp--; out.set(s, ol); ol += s.length; break;
      }
      case 81:
        if (ol + 1 > 65536) return done(11);
        out[ol++] = D[--sp] & 255; break;
      case 82: D[sp++] = ip < q.length ? q[ip++] : -1; break;
      case 83: return done(D[--sp] & 255);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let p: Buffer, q: Buffer;
  try { p = readFileSync(join(I, id, 'program.bin')); } catch { p = Buffer.alloc(0); }
  try { q = readFileSync(join(I, id, 'input.bin')); } catch { q = Buffer.alloc(0); }
  const r = run(p, q);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
