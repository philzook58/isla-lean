#!/usr/bin/env python3
"""Lift compiler output: the C corpus in examples/c/challenges.c at -O0 and -O2.

The corpus is linked into the native driver, so every function's bytes are the final, relocated
instructions at their real link address. Each function is lifted with isla-lean (failures are
recorded, not hidden), and every lifted model is compared against qemu-riscv64 on the same inputs.
Requires riscv64-linux-gnu-gcc, qemu-riscv64, isla-footprint (or a trace cache) and Lake.
"""

from __future__ import annotations

import os
import pathlib
import random
import re
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_native import BUF, MODULES, RA, SP, lean_program, run  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEVELS = ["O0", "O2"]
FUNCTIONS = ["inc_u32", "max_u32", "mix_u32", "sum_u32", "find_u32", "copy_bytes", "isort_u32",
             "gcd_u64", "crc32_bytes", "popcount_u64", "strlen_bytes", "classify"]
GENERATED = ROOT / "lean" / "Examples" / "Generated"
CFLAGS = ["-march=rv64imfd", "-mabi=lp64d", "-mcmodel=medany", "-ffunction-sections",
          "-fdata-sections", "-fno-tree-vectorize", "-fno-builtin", "-fno-pic"]
# The Sail platform serves loads from RAM only at [0x80000000, 0x100000000), so the corpus's
# static data is moved there (as `.corpusdata`); `medany` code reaches it PC-relatively. glibc's
# static start files are `medlow`, so the program image itself stays at the default address.
DATA_BASE = 0x80000000
MASK32, MASK64 = (1 << 32) - 1, (1 << 64) - 1


def lean_name(function: str, level: str) -> str:
    return "".join(part.capitalize() for part in function.split("_")) + level


def words32(values):
    return b"".join(v.to_bytes(4, "little") for v in values).ljust(96, b"\0")


def cases(function: str):
    """Inputs per C function: (args, 96-byte buffer). Pointer args are "p<offset>"."""
    rng = random.Random(hash(function) & 0xFFFF)
    zero = bytes(96)
    edge32 = [0, 1, 31, 32, 0x7FFFFFFF, 0x80000000, MASK32]
    edge64 = [0, 1, 2, 3, 12, 255, 1 << 32, (1 << 63) - 1, 1 << 63, MASK64]
    if function in ("inc_u32", "max_u32", "mix_u32"):
        pairs = [(a, b) for a in edge32 for b in edge32]
        pairs += [(rng.getrandbits(32), rng.getrandbits(32)) for _ in range(20)]
        return [([a, b, 0, 0], zero) for a, b in pairs]
    if function == "sum_u32":
        return [(["p0", n, 0, 0], words32([rng.getrandbits(32) for _ in range(24)])) for n in range(25)]
    if function == "find_u32":
        out = []
        for n in [0, 1, 5, 24]:
            data = [rng.getrandbits(8) for _ in range(24)]
            out += [(["p0", n, key, 0], words32(data)) for key in [data[0], data[min(n, 23)], 999]]
        return out
    if function == "copy_bytes":
        buf = bytes(rng.getrandbits(8) for _ in range(96))
        return ([(["p48", "p0", n, 0], buf) for n in [0, 1, 7, 8, 40, 48]] +
                [(["p4", "p0", n, 0], buf) for n in [0, 5, 20]] +       # forward overlap
                [(["p0", "p4", n, 0], buf) for n in [5, 20]])
    if function == "isort_u32":
        out = []
        for n in [0, 1, 2, 5, 12, 24]:
            out.append((["p0", n, 0, 0], words32([rng.getrandbits(32) for _ in range(24)])))
            out.append((["p0", n, 0, 0], words32(list(range(24, 0, -1)))))
        return out
    if function == "gcd_u64":
        pairs = [(a, b) for a in edge64 for b in edge64]
        pairs += [(rng.getrandbits(64), rng.getrandbits(20)) for _ in range(10)]
        return [([a, b, 0, 0], zero) for a, b in pairs]
    if function == "crc32_bytes":
        buf = bytes(rng.getrandbits(8) for _ in range(96))
        return [(["p0", n, 0, 0], buf) for n in [0, 1, 4, 9, 32, 96]]
    if function == "popcount_u64":
        return [([x, 0, 0, 0], zero) for x in edge64 + [rng.getrandbits(64) for _ in range(10)]]
    if function == "strlen_bytes":
        return [(["p0", 0, 0, 0], bytes([65] * k + [0] * (96 - k))) for k in [0, 1, 7, 8, 9, 60]]
    if function == "classify":
        return [([x, 0, 0, 0], zero) for x in [*range(10), MASK32, 1 << 31]]
    raise KeyError(function)


def build(tmp: pathlib.Path) -> pathlib.Path:
    objects = []
    for level in LEVELS:
        obj = tmp / f"c_{level}.o"
        run(["riscv64-linux-gnu-gcc", "-c", f"-{level}", f"-DLEVEL={level}", *CFLAGS,
             "examples/c/challenges.c", "-o", obj])
        names = [line.split()[1] for line in run(["riscv64-linux-gnu-objdump", "-h", obj]).splitlines()
                 if re.match(r"\s*\d+\s+\.s?rodata", line)]
        run(["riscv64-linux-gnu-objcopy",
             *[a for n in names for a in ("--rename-section", f"{n}=.corpusdata,alloc,load,readonly,data")],
             obj])
        objects.append(obj)
    header = tmp / "routines.h"
    header.write_text("#define ROUTINES " + " ".join(
        f"X({f}_{level})" for level in LEVELS for f in FUNCTIONS) + "\n")
    binary = tmp / "native_c"
    run(["riscv64-linux-gnu-gcc", "-static", "-O2", "-march=rv64gc", "-include", header,
         f"-Wl,--section-start=.corpusdata={DATA_BASE:#x}",
         "tests/native/native.c", *objects, "-o", binary])
    return binary


def corpus_data(binary: pathlib.Path, tmp: pathlib.Path) -> list[tuple[int, bytes]]:
    """The corpus's static data as loaded, i.e. what an ELF loader would put in memory."""
    m = re.search(r"\s\.corpusdata\s+([0-9a-f]+)\s+([0-9a-f]+)",
                  run(["riscv64-linux-gnu-objdump", "-h", binary]))
    if not m:
        return []
    dump = tmp / "corpusdata.bin"
    run(["riscv64-linux-gnu-objcopy", "-O", "binary", "-j", ".corpusdata", binary, dump])
    return [(int(m.group(2), 16), dump.read_bytes())]


def function_bytes(binary: pathlib.Path, tmp: pathlib.Path) -> dict[str, tuple[int, bytes]]:
    """Address and final bytes of each corpus function in the linked binary."""
    symbols = {}
    for line in run(["riscv64-linux-gnu-nm", "-S", "--defined-only", binary]).splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[2] in "tT":
            symbols[parts[3]] = (int(parts[0], 16), int(parts[1], 16))
    vma = next(int(m.group(1), 16) for m in re.finditer(
        r"\.text\s+\S+\s+([0-9a-f]+)", run(["riscv64-linux-gnu-objdump", "-h", binary])))
    text = tmp / "text.bin"
    run(["riscv64-linux-gnu-objcopy", "-O", "binary", "-j", ".text", binary, text])
    data = text.read_bytes()
    return {name: (addr, data[addr - vma: addr - vma + size])
            for name, (addr, size) in symbols.items()
            if any(name == f"{f}_{level}" for f in FUNCTIONS for level in LEVELS)}


def lift_all(functions, cache: str | None):
    GENERATED.mkdir(parents=True, exist_ok=True)
    results = {}
    for level in LEVELS:
        for f in FUNCTIONS:
            addr, code = functions[f"{f}_{level}"]
            name = lean_name(f, level)
            with tempfile.NamedTemporaryFile(suffix=".bin") as tmpbin:
                tmpbin.write(code)
                tmpbin.flush()
                args = ["uv", "run", "isla-lean", "lift", "--binary", tmpbin.name, "--name", name,
                        "--base", hex(addr), "-o", GENERATED / f"{name}.lean"]
                args += ["--cache", cache]
                start = time.time()
                r = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=3600)
                elapsed = time.time() - start
            path = GENERATED / f"{name}.lean"
            if r.returncode:
                path.unlink(missing_ok=True)
                results[(f, level)] = ("rejected", r.stderr.strip().splitlines()[-1], len(code), elapsed)
            else:
                text = path.read_text()
                cuts = sum(int(n) for n in re.findall(r"(\d+) at ", text.split("import IslaLean")[0]))
                results[(f, level)] = ("lifted", f"{text.count(chr(10))} lines, {cuts} cut paths",
                                       len(code), elapsed)
    return results


def main():
    cache = os.environ.get("ISLA_LEAN_C_CACHE", str(ROOT / ".trace-cache"))
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        binary = build(tmp)
        functions = function_bytes(binary, tmp)
        segments = corpus_data(binary, tmp)
        print("static data loaded into the model:", [(hex(a), len(d)) for a, d in segments])
        results = lift_all(functions, cache)
        print(f"{'function':14} {'lvl':3} {'bytes':>5} {'insns':>5} {'time':>6}  result")
        for (f, level), (status, detail, size, elapsed) in results.items():
            print(f"{f:14} {level:3} {size:5} {size // 4:5} {elapsed:5.1f}s  {status}: {detail}")
        lifted = [(f, level) for (f, level), r in results.items() if r[0] == "lifted"]
        rows = [(f"{f}_{level}", args, buf) for f, level in lifted for args, buf in cases(f)]
        for f, level in lifted:
            MODULES[f"{f}_{level}"] = lean_name(f, level)
        data = "".join(" ".join([r, *map(str, a), *map(str, b)]) + "\n" for r, a, b in rows)
        native = run(["qemu-riscv64", binary], data=data).splitlines()
    for f, level in lifted:
        start = time.time()
        run(["lake", "build", f"Examples.Generated.{lean_name(f, level)}"], cwd=ROOT / "lean", cap=True)
        print(f"  built {lean_name(f, level):18} {time.time() - start:5.1f}s")
    program = ROOT / "lean" / "build" / "CCases.lean"
    program.parent.mkdir(exist_ok=True)
    program.write_text(lean_program(rows, fuel=200000, segments=segments))
    model = run(["lake", "env", "lean", "--run", "build/CCases.lean"], cwd=ROOT / "lean",
                cap=True).splitlines()
    assert len(native) == len(model) == len(rows), (len(native), len(model), len(rows))
    bad = {}
    for (routine, args, _), n, m in zip(rows, native, model):
        if n != m:
            bad.setdefault(routine, []).append((args, n[:80], m[:80]))
    for routine in sorted({r for r, _, _ in rows}):
        count = sum(1 for r, _, _ in rows if r == routine)
        status = "agree" if routine not in bad else f"{len(bad[routine])} DIFFER"
        print(f"  {routine:22} {count:4} cases  {status}")
        for args, n, m in bad.get(routine, [])[:2]:
            print("     ", args, "\n       native", n, "\n       model ", m)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
