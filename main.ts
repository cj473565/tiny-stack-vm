// A tiny stack virtual machine, built for make.fun's tiny-stack-vm bounty.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// A trap aborts a program at once: its code becomes the exit code, and the
// output written before the trap is kept.
class Trap {
  code: number;
  constructor(code: number) { this.code = code; }
}

// How many values each opcode pops and pushes, as two digit strings indexed
// by the opcode byte: the pre-execution stack checks read them from here.
const POPS = '000112230000000022222221222122202220000000000000011000000000000012000000000000001101';
const PUSHES = '011022330000000011111111111111101110000000000000000000000000000010000000000000000010';

function isOpcode(op: number): boolean {
  return op <= 0x07 || (op >= 0x10 && op <= 0x22) || (op >= 0x30 && op <= 0x34)
    || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
}

function runVm(code: Buffer, data: Buffer): { out: Buffer; exit: number } {
  const stack: number[] = [];
  const calls: number[] = [];
  const mem = new Int32Array(256);
  const chunks: Buffer[] = [];
  let outLen = 0;
  let pc = 0;
  let steps = 0;
  let readAt = 0;
  const emit = (bytes: Buffer): void => {
    if (outLen + bytes.length > 65_536) throw new Trap(11);
    chunks.push(bytes);
    outLen += bytes.length;
  };
  const fold = (f: (a: number, b: number) => number): void => {
    const b = stack.pop() as number;
    const a = stack.pop() as number;
    stack.push(f(a, b));
  };
  const nz = (b: number): number => { // a zero divisor traps, code 4
    if (b === 0) throw new Trap(4);
    return b;
  };
  const cell = (v: number): number => { // a memory address outside 0..255 traps, code 6
    if (v < 0 || v > 255) throw new Trap(6);
    return v;
  };
  try {
    for (;;) {
      if (steps === 1_000_000) throw new Trap(10);
      if (pc < 0 || pc >= code.length) throw new Trap(9);
      const op = code[pc];
      if (!isOpcode(op)) throw new Trap(5);
      const imm = op === 0x01 ? 1 : op === 0x02 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
      if (pc + imm >= code.length) throw new Trap(9);
      steps += 1;
      const pops = POPS.charCodeAt(op) - 48;
      if (stack.length < pops) throw new Trap(2);
      if (stack.length - pops + (PUSHES.charCodeAt(op) - 48) > 256) throw new Trap(3);
      const next = pc + 1 + imm;
      pc = next;
      switch (op) {
        case 0x00: return { out: Buffer.concat(chunks), exit: 0 }; // HALT
        case 0x01: stack.push((code[next - 1] << 24) >> 24); break; // PUSH8, sign-extended
        case 0x02: // PUSH32, little-endian
          stack.push(code[next - 4] | (code[next - 3] << 8) | (code[next - 2] << 16) | (code[next - 1] << 24));
          break;
        case 0x03: stack.pop(); break; // POP
        case 0x04: stack.push(stack[stack.length - 1]); break; // DUP
        case 0x05: { // SWAP
          const t = stack[stack.length - 1];
          stack[stack.length - 1] = stack[stack.length - 2];
          stack[stack.length - 2] = t;
          break;
        }
        case 0x06: stack.push(stack[stack.length - 2]); break; // OVER
        case 0x07: { // ROT: ( a b c -- b c a )
          const a = stack[stack.length - 3];
          stack[stack.length - 3] = stack[stack.length - 2];
          stack[stack.length - 2] = stack[stack.length - 1];
          stack[stack.length - 1] = a;
          break;
        }
        case 0x10: fold((a, b) => (a + b) | 0); break;
        case 0x11: fold((a, b) => (a - b) | 0); break;
        case 0x12: fold((a, b) => Math.imul(a, b)); break;
        // DIV truncates toward zero, MOD takes the dividend's sign, the U
        // forms are unsigned; x / -1 wraps and x % -1 is 0.
        case 0x13: fold((a, b) => (a === -2147483648 && b === -1 ? a : (a / nz(b)) | 0)); break;
        case 0x14: fold((a, b) => (b === -1 ? 0 : (a % nz(b)) | 0)); break;
        case 0x15: fold((a, b) => Math.floor((a >>> 0) / (nz(b) >>> 0)) | 0); break;
        case 0x16: fold((a, b) => ((a >>> 0) % (nz(b) >>> 0)) | 0); break;
        case 0x17: stack[stack.length - 1] = -stack[stack.length - 1] | 0; break; // NEG
        case 0x18: fold((a, b) => a & b); break;
        case 0x19: fold((a, b) => a | b); break;
        case 0x1a: fold((a, b) => a ^ b); break;
        case 0x1b: stack[stack.length - 1] = ~stack[stack.length - 1]; break; // NOT
        case 0x1c: fold((a, b) => a << (b & 31)); break;
        case 0x1d: fold((a, b) => a >> (b & 31)); break;
        case 0x1e: fold((a, b) => (a >>> (b & 31)) | 0); break;
        case 0x20: fold((a, b) => (a === b ? 1 : 0)); break;
        case 0x21: fold((a, b) => (a < b ? 1 : 0)); break;
        case 0x22: fold((a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0)); break;
        case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: signed offset from next
          const rel = ((code[next - 2] | (code[next - 1] << 8)) << 16) >> 16;
          let go = true;
          if (op !== 0x30) {
            const v = stack.pop() as number;
            go = op === 0x31 ? v === 0 : v !== 0;
          }
          if (go) pc = next + rel;
          break;
        }
        case 0x33: // CALL: unsigned absolute address, at most 64 deep
          if (calls.length === 64) throw new Trap(7);
          calls.push(next);
          pc = code[next - 2] | (code[next - 1] << 8);
          break;
        case 0x34: // RET
          if (calls.length === 0) throw new Trap(8);
          pc = calls.pop() as number;
          break;
        case 0x40: // LOAD
          stack[stack.length - 1] = mem[cell(stack[stack.length - 1])];
          break;
        case 0x41: { // STORE: the address sits on top of the value
          const addr = cell(stack.pop() as number);
          mem[addr] = stack.pop() as number;
          break;
        }
        case 0x50: emit(Buffer.from(String(stack.pop() as number))); break; // PRINT
        case 0x51: emit(Buffer.from([(stack.pop() as number) & 255])); break; // PUTC
        case 0x52: stack.push(readAt < data.length ? data[readAt++] : -1); break; // IN
        case 0x53: return { out: Buffer.concat(chunks), exit: (stack.pop() as number) & 255 }; // EXIT
      }
    }
  } catch (e) {
    if (e instanceof Trap) return { out: Buffer.concat(chunks), exit: e.code };
    throw e;
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const { out, exit } = runVm(
    readFileSync(join(IN_DIR, id, 'program.bin')),
    readFileSync(join(IN_DIR, id, 'input.bin')),
  );
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${exit}\n`);
}
