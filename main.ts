// Tiny stack VM (Node 22, built-ins only): answers every instance of a set
// in one run. Deterministic: no clock, no environment reads, no randomness.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Decode table: one byte per opcode, imm << 4 | pops << 2 | pushes; 255 is
// an unknown opcode. Built once, shared by every instance.
const T = new Uint8Array(256).fill(255);
const put = (a: number, b: number, v: number): void => { for (let i = a; i <= b; i++) T[i] = v; };
put(0x10, 0x16, 9); put(0x18, 0x1a, 9); put(0x1c, 0x1e, 9); put(0x20, 0x22, 9);
T[0x00] = 0; T[0x01] = 17; T[0x02] = 65; T[0x03] = 4; T[0x04] = 6; T[0x05] = 10;
T[0x06] = 11; T[0x07] = 15; T[0x17] = 5; T[0x1b] = 5; T[0x30] = 32; T[0x31] = 36;
T[0x32] = 36; T[0x33] = 32; T[0x34] = 0; T[0x40] = 5; T[0x41] = 8; T[0x50] = 4;
T[0x51] = 4; T[0x52] = 1; T[0x53] = 4;

// Runs one program on its input: [bytes written, exit code]. A trap ends the
// program at once with the trap's code, keeping the output written so far.
// Check order: step limit, pc bounds, known opcode, immediate fits, step
// counted, stack underflow, stack overflow, then the instruction's own
// traps and effect.
function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const n = p.length;
  const done = (code: number): [Uint8Array, number] => [out.subarray(0, olen), code];
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    const d = T[op];
    if (d === 255) return done(5);
    const imm = d >> 4;
    if (pc + imm >= n) return done(9);
    steps++;
    const pops = (d >> 2) & 3;
    if (sp < pops) return done(2);
    if (sp - pops + (d & 3) > 256) return done(3);
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return done(4); r = (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op === 0x30) pc = nx + rel;
        else if ((op === 0x31) === (D[--sp] === 0)) pc = nx + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return done(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return done(D[--sp] & 255);
    }
  }
}

for (const id of readdirSync(I).sort()) {
  let out: Uint8Array = new Uint8Array(0);
  let code = 0;
  try {
    [out, code] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  } catch {
    out = new Uint8Array(0);
    code = 0;
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
