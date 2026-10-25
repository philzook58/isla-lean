#!/usr/bin/env python3
"""Native RISC-V oracle (qemu-user) against the lifted Lean models, mirroring pcode-lean's
tests/check.py, check_bignum.py and check_writes.py.

Every case runs the exact example bytes natively and runs the generated Lean `execute` on the
same inputs. Both print a0, a1, a2 and a 96-byte buffer, which must agree; write cases are also
checked against a Python byte reference. Requires riscv64-linux-gnu-gcc, qemu-riscv64 and Lake.
"""

from __future__ import annotations

import pathlib
import random
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
MASK = (1 << 64) - 1
BUF, SP, RA = 0xC0006000, 0xC0008000, 0x4000  # model addresses, inside the platform's RAM
MODULES = {"inc64": "Increment", "umax64": "Maximum", "count64": "Count", "scan64": "Scan",
           "add128": "Add128", "addmem": "AddMem", "fill64": "Fill", "stack32": "Stack32",
           "reserve256": "Reserve256", "alias64": "Alias", "stack64": "Stack",
           "shift64": "Shift", "probe_stack32": "Stack32"}


def run(args, data=None, cwd=ROOT, cap=False):
    """Run a command; `cap` puts it in a memory-capped systemd scope when available."""
    if cap and shutil.which("systemd-run"):
        args = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=3G",
                "-p", "MemorySwapMax=0", *args]
    result = subprocess.run(list(map(str, args)), cwd=cwd, input=data, text=True,
                            capture_output=True, timeout=600)
    if result.returncode:
        raise RuntimeError(f"{args}: exit {result.returncode}\n{result.stdout}{result.stderr}")
    return result.stdout


def pattern(seed=None):
    mem = bytearray((i * 37 + 11) & 255 for i in range(96))
    limbs = [None, (0, 0, 0, 0), (MASK, 0, 1, 0), (MASK, MASK, 1, 0)][seed or 0]
    if limbs is not None:
        for offset, value in zip([0, 8, 32, 40], limbs):
            mem[offset:offset + 8] = value.to_bytes(8, "little")
    return mem


def cases():
    rng = random.Random(0xC0DE)
    edge = [0, 1, 15, 16, 127, 128, 255, 256, (1 << 63) - 1, 1 << 63, MASK]
    pairs = [(a, b) for a in edge for b in [0, 1, MASK]]
    pairs += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(32)]
    zero = bytes(96)
    out = []
    for routine in ["inc64", "umax64", "alias64", "stack64", "shift64"]:
        out += [(routine, [a, b, 0, 0], zero) for a, b in pairs]
    out += [("shift64", [0x123456789ABCDEF0, n, 0, 0], zero) for n in [31, 32, 63, 64, 65, 255]]
    out += [("count64", [n, 0, 0, 0], zero) for n in [*range(25), 63, 127, 255, 511]]
    edge128 = [0, 1, (1 << 63) - 1, 1 << 63, MASK - 1, MASK]
    adds = [[a, b, c, d] for a in edge128 for b in [0, MASK] for c in [0, 1, MASK] for d in [0, MASK]]
    adds += [[rng.getrandbits(64) for _ in range(4)] for _ in range(64)]
    out += [("add128", row, zero) for row in adds]
    scans = [[], [0], [MASK], [0, 0, 0], [0, 1, 0], [MASK, MASK]]
    scans += [[rng.getrandbits(64) for _ in range(n)] for n in range(2, 13)]
    for words in scans:
        buf = b"".join(w.to_bytes(8, "little") for w in words).ljust(96, b"\0")
        out.append(("scan64", [len(words), "p0", 0, 0], buf))
    out += [("addmem", [f"p{off}", "p0", "p32", 0], bytes(pattern(seed)))
            for off in [0, 32, 64, 1, 31, 40] for seed in range(4)]
    out += [("fill64", ["p16", n, v, 0], bytes(pattern())) for n in range(9) for v in [0, 1, MASK]]
    out += [("probe_stack32", [v, 0, 0, 0], zero) for v in [0, 1, 1 << 63, MASK, 0x123456789ABCDEF0]]
    out += [("reserve256", [0, 0, 0, 0], zero)]
    return out


def reference(routine, args, buf):
    """Byte reference for the write routines (same formula as pcode-lean's check_writes)."""
    mem = bytearray(buf)
    if routine == "fill64":
        n, value = args[1], args[2]
        mem[16:16 + 8 * n] = value.to_bytes(8, "little") * n
        return mem
    if routine == "addmem":
        a = int(args[0][1:])
        low = int.from_bytes(mem[0:8], "little") + int.from_bytes(mem[32:40], "little")
        mem[a:a + 8] = (low & MASK).to_bytes(8, "little")
        high = (int.from_bytes(mem[8:16], "little") + int.from_bytes(mem[40:48], "little")
                + (low >> 64))
        mem[a + 8:a + 16] = (high & MASK).to_bytes(8, "little")
        return mem
    return None


def line(routine, args, buf):
    return " ".join([routine, *map(str, args), *map(str, buf)])


def lean_program(rows, fuel=2000, segments=()):
    """`segments`: (address, bytes) images loaded into the model's memory (e.g. `.rodata`)."""
    imports = sorted(set(MODULES.values()))
    out = [*(f"import Examples.Generated.{m}" for m in imports), "open IslaLean", ""]
    image = "165"
    for index, (address, data) in enumerate(segments):
        out.append(f"def segment{index} : Array Nat := #[" + ",".join(map(str, data)) + "]")
        image = (f"if (p - {address}).toNat < {len(data)} then "
                 f"segment{index}[(p - {address}).toNat]! else {image}")
    out += [
           "def value (v : BitVec 64) : String :=",
           f"  if (v - {BUF}).toNat ≤ 1024 then s!\"p{{(v - {BUF}).toNat}}\" else s!\"{{v.toNat}}\"",
           "",
           "def report (s : RVState) (a0 : BitVec 64) : IO Unit := do",
           "  IO.print s!\"{value a0} {value s.x11} {value s.x12}\"",
           "  for i in List.range 96 do",
           f"    IO.print s!\" {{(s.mem ({BUF} + BitVec.ofNat 64 i)).toNat}}\"",
           "  IO.println \"\"", "",
           "def check (name : String) (out : Option Exit) : IO (Option RVState) := do",
           "  match out with",
           "  | some (.stuck _) => IO.println \"STUCK\"; pure none",
           "  | some (.ret s) =>",
           f"    if s.pc != {RA} || s.x2 != {SP} then throw (IO.userError s!\"{{name}}: return state\")",
           "    pure (some s)",
           "  | none => throw (IO.userError s!\"{name}: fuel exhausted\")", ""]
    # One definition per case: a single huge `do` block exceeds Lean's recursion depth.
    for index, (routine, args, buf) in enumerate(rows):
        regs = [BUF + int(a[1:]) if isinstance(a, str) else a for a in args]
        bytes_ = "#[" + ",".join(map(str, buf)) + "]"
        module = MODULES[routine]
        out += [f"def case{index} : IO Unit := do",
                f"    let bytes : Array Nat := {bytes_}",
                f"    let mem : Memory := fun p ↦ BitVec.ofNat 8 (bytes[(p - {BUF}).toNat]?.getD"
                f" ({image}))",
                f"    let s : RVState := {{ x1 := {RA}, x2 := {SP}, x10 := {regs[0]}, "
                f"x11 := {regs[1]}, x12 := {regs[2]}, x13 := {regs[3]}, mem := mem }}",
                f"    let some out ← check \"{routine}\" ({module}.execute {fuel} s) | pure ()"]
        out.append(f"    report out (readLE out.mem ({SP} - 32) 8)" if routine == "probe_stack32"
                   else "    report out out.x10")
    batches = [range(i, min(i + 50, len(rows))) for i in range(0, len(rows), 50)]
    for b, batch in enumerate(batches):
        out += [f"def batch{b} : IO Unit := do", *(f"  case{index}" for index in batch)]
    out += ["def main : IO Unit := do", *(f"  batch{b}" for b in range(len(batches)))]
    return "\n".join(out) + "\n"


def main():
    rows = cases()
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        run(["riscv64-linux-gnu-gcc", "-static", "-O2", "-march=rv64gc", "tests/native/native.c",
             "examples/routines.S", "tests/native/stack_probe.S", "-o", tmp / "native"])
        data = "".join(line(*row) + "\n" for row in rows)
        native = run(["qemu-riscv64", tmp / "native"], data=data).splitlines()
        program = ROOT / "lean" / "build" / "NativeCases.lean"
        program.parent.mkdir(exist_ok=True)
        program.write_text(lean_program(rows))
        model = run(["lake", "env", "lean", "--run", program.relative_to(ROOT / "lean")],
                    cwd=ROOT / "lean", cap=True).splitlines()
    assert len(native) == len(model) == len(rows), (len(native), len(model), len(rows))
    failures, stuck = 0, 0
    for row, n, m in zip(rows, native, model):
        if m == "STUCK":
            # The model cuts misaligned accesses (see the generated headers); nothing else may stick.
            if row[0] == "addmem" and int(row[1][0][1:]) % 8:
                stuck += 1
                continue
            failures += 1
            print("UNEXPECTED STUCK", row[0], row[1])
            continue
        ref = reference(*row)
        bad = n != m or (ref is not None and n.split()[3:] != list(map(str, ref)))
        if bad:
            failures += 1
            if failures <= 10:
                print("MISMATCH", row[0], row[1], "\n  native", n[:120], "\n  model ", m[:120])
    kinds = sorted({r[0] for r in rows})
    print(f"{len(rows) - failures - stuck}/{len(rows)} native/model comparisons agree "
          f"({', '.join(kinds)}).")
    print(f"{stuck} misaligned cases run natively but are outside the model (stuck), as expected.")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
