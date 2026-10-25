# isla-lean

Lift RISC-V machine code through [Isla](https://github.com/rems-project/isla) footprints of the
[Sail](https://github.com/rems-project/sail) RISC-V model into ordinary executable Lean, then prove
contracts about it with Lean's `vcgen`.

```text
RV64 bytes ─ isla-footprint -t (Sail IR) ─▶ trace tree per instruction ─ isla-lean ─▶ Lean step function ─▶ vcgen proofs
```

The generated Lean has the same shape as [pcode-lean](../pcode-lean)'s: one `step` alternative per
instruction, a finite `PC` type, and `run`/`execute` over a small `RVState` record. pcode-lean's
proof infrastructure is vendored as `lean/IslaLean/Run.lean`, so pcode-lean-style invariant proofs
carry over unchanged. The semantics come from the Sail model, as in Islaris, not from SLEIGH.

## Setup

Requirements:
- `uv`.
- `isla-footprint`, for live lifting only.
- `riscv64-linux-gnu-gcc` and `qemu-riscv64`, for the native oracle only.
- A Sail RISC-V IR snapshot matching the packaged config, for live lifting only. The pinned
  `rv64d.ir` from `sail_graham/isla-snapshots` (sha256 `de8bee837b6a3b88…`) works.
- Lean/Lake 4.35.0, for the proofs.
- The RISC-V binutils (`riscv64-linux-gnu-as`, `objcopy`), for the examples.

```sh
uv sync
uv run --group dev pytest                      # no Isla or IR needed: replays checked-in traces
export ISLA_LEAN_ARCH=/path/to/rv64d.ir
scripts/examples.sh                            # assemble, lift live, build and check proofs
scripts/examples.sh --traces tests/fixtures/traces   # same, replaying the checked-in traces
python3 -I tests/check_native.py               # qemu-riscv64 oracle against the Lean models
python3 -I tests/check_c.py                    # compile, lift and natively check the C corpus
```

## Use

```sh
uv run isla-lean lift --hex 1305150067800000 --name Increment --base 0x1000 -o Increment.lean
uv run isla-lean lift --binary routine.bin --name Routine --arch rv64d.ir
uv run isla-lean lift ... -o Routine.lean --check     # fail if the file is stale
```

- **Input:** bytes come from `--binary` (raw) or `--hex`, modelled at `--base`; the entry point is
  the first byte. There is no ELF loader yet, so extract the region with `objcopy` first. Assemble
  without compressed instructions (`-march=rv64i`, or `.option norvc`).
- **Model profile:** the IR's file name selects a packaged profile: its config, the Sail functions
  where paths are cut (`--kill`), and the Isla errors known to end one class of path. Only
  `rv64d.ir` has a profile; see "Why rv64d.ir" below.
- **Caching:** traces are cached under `~/.cache/isla-lean/<model>-<config>-<cuts>-v<format>/`, with
  a `PROVENANCE` file. A cache directory can be replayed later with `--traces DIR`, without Isla.
- **Memory:** each Isla process runs under an address-space limit (`--memory-limit`, default 4G).
- **Python API:** `isla_lean.lift(name, code, base, source)`, where `source` is an `IslaRunner` or
  a `TraceDirectory`.

## What the translation does

| Isla trace | Lean |
| --- | --- |
| `declare-const` / `define-const` | typed `let` |
| `read-reg`/`write-reg` of `x1`..`x31` | `RVState` fields |
| plain explicit `read-mem` / `write-mem` of 1, 2, 4 or 8 bytes | `readLE` / `writeLE` on `RVState.mem` |
| `cases` whose branches start with `assert c` / `assert (not c)` | `if c then … else …` |
| `cases` with one branch (its sibling was cut) | `if !c then return .inr (.stuck s)`, then the branch |
| any other `assert c` | `if !c then return .inr (.stuck s)` |
| no `nextPC` write | fall through to `pc + 4` |
| concrete `nextPC` | jump to that instruction, which must be in the region |
| symbolic `nextPC` | `.inr (.ret s)`: the routine returns |
| read of `PC` / `nextPC` | must equal pc / pc+4 (Isla is run with both pinned) |
| concrete read of another register (`cur_privilege`, `misa`, PMP, platform map, …) | listed in the header as an environment assumption |

Anything else is rejected with an error, never dropped. That includes:
- CSR reads and writes, and exclusive or atomic accesses;
- abstract primitives such as `fence`;
- case splits with other shapes;
- branches out of the region;
- unknown SMT operators.

SMT division and remainder use Lean's SMT-LIB-faithful `smtUDiv`/`smtSDiv`/`srem`/`smod`/`umod`;
Lean's `/` differs on division by zero.

**`stuck` is the escape hatch, and contracts must exclude it.** A path cut at a trap, at an MMIO
device access, or at a misaligned access leaves its guard behind, so reaching it ends in `stuck`.
That makes every contract a statement about the modelled domain only: each contract's postcondition
is `False` on `stuck`, so its premises must rule those paths out. Each generated header lists, per
instruction, how many paths were cut and why.

Isla also runs a second pass per instruction (`--trace-all`). An instruction whose `execute`
performs no events at all is rejected, because in this snapshot that is how an unimplemented
instruction looks (F/D, for example). The simplified trace can't tell it apart from a no-op.

One deliberate rewrite: `bvadd x c`, where the top bit of `c` is set (a negative immediate), is
emitted as `x - (-c)`. That's the same bit vector, but Lean's kernel checks definitional equalities
involving literals near 2^64 extremely slowly. Leaving them in once exhausted memory in an otherwise
trivial proof.

## Why `rv64d.ir`, and what the cuts mean

- **Traps.** The older `riscv_model_rv64d.ir` snapshot handles symbolic loads, but its illegal and
  unimplemented instructions (`ecall`, `fld`, opcode 0) execute nothing, indistinguishable from a
  no-op, so it is not offered. In `rv64d.ir`, `execute` *returns* a trap, built by `trap`, and the
  footprint never runs the handler. Without a cut, a trap would also look like a no-op, so paths
  reaching `trap` are cut.
- **Memory.** A symbolic load or store walks the platform memory map: an alignment check, then ROM
  (0x1000), CLINT, a device window at 0x0c000000, and RAM at `[0x80000000, 0x100000000)`. Paths
  into MMIO devices are cut at `mmio_read`/`mmio_write`.
- **Misalignment.** A misaligned access is split by `count_trailing_zeros` of the address. Isla
  cannot size that split symbolically, and its error ends exactly that path, so it is recorded as
  "misaligned access". qemu (and real hardware that allows misalignment) performs such accesses;
  the model excludes them. The native oracle confirms this is the only gap.
- **PMP.** PMP registers are pinned off in the config; otherwise every access branches over 64
  symbolic entries.

## The pcode-lean corpus, ported

`examples/routines.S` holds RV64I ports of every routine in pcode-lean's `examples/routines.S` and
`tests/probes.S`, except `afgap64`: RISC-V has no flags, so it has no auxiliary-carry analogue.
All 12 lift. The table lists the proved contracts (`lean/Examples/`):

| routine | theorem | contract | extra premise vs pcode-lean |
| --- | --- | --- | --- |
| `inc64` | `IncrementProof.correct`, `terminates` | returns `a0 + 1` | — |
| `umax64` | `MaximumProof.correct`, `terminates` | unsigned max of `a0`, `a1` | — |
| `count64` | `CountProof.correct`, `terminates` | returns `a0`, every count, within `3n+4` steps | — |
| `scan64` | `ScanProof.correct`, `terminates` | ORs `a0` limbs at `a1`, within `5n+5` steps | limbs aligned and in RAM |
| `add128` | `Add128Proof.correct` | `(a2:a1:a0) = (a1:a0) + (a3:a2)` as 129-bit numbers | — |
| `addmem` | `WriteProof.add_correct` | exact memory effect (machine order) and carry | three buffers aligned and in RAM |
| `fill64` | `FillProof.correct`, `terminates` | exact memory effect, within `4n+2` steps | limbs aligned and in RAM |
| `stack32` | `WriteProof.stack_correct`, `stack32` | exact spill; `sp` within 32 bytes at every boundary | spill slot aligned and in RAM |
| `reserve256` | `reserve_correct`, `reserve_depth`, `reserve256_exceeds32` | exit frame holds, yet it breaks a 32-byte bound | — |

Every contract also gives the return to `ra &&& ~~~1` and preservation of `ra` and `sp`. All 16
theorems use only `propext`, `Classical.choice` and `Quot.sound`. `bv_decide` is avoided, because
it adds a native-evaluation axiom.

A from-scratch Lean build takes about 22 s and peaks at about 0.8 GB. `addmem` is the slowest
file, at about 20 s.

**Native oracle.** `tests/check_native.py` mirrors pcode-lean's `check.py`, `check_bignum.py` and
`check_writes.py`:
- it runs the exact example bytes under qemu-riscv64 and the lifted Lean `execute` on the same
  inputs: edge values, random values, buffers and the stack-spill probe;
- every byte of a 96-byte buffer is compared, and write routines are also checked against a Python
  byte reference;
- **562/570 agree.** The other 8 are the misaligned `addmem` cases, where the model is `stuck` by
  design.

**Proof technique.** The proofs follow pcode-lean's shape: a PC-indexed invariant, `vcgen` per
block, and `run_spec`. Two additions handle memory:
- `IslaLean/Memory.lean` holds simp lemmas that turn the model's 128-bit `sle`/`slt`/`srem` guards
  into `Nat` comparisons, after which `omega` refutes every non-RAM or misaligned branch under a
  `RamRegion` premise.
- `IslaLean/Rank.lean` derives termination from a second Hoare triple stating that a rank decreases,
  so `vcgen` handles the guard trees there too.

**Not ported:** pcode-lean's register/flag frame library (`Frame.lean`, `Contracts.lean`,
`FrameChecks.lean`), caller helpers (`Callers.lean`, `CallerChecks.lean`) and tutorial. They are
built around x86 registers and flags, and the RISC-V versions would need a new `Footprint`
definition. The probes (`alias64`, `stack64`, `shift64`) are lifted and natively checked; as in
pcode-lean, they have no theorems.

## Compiled C

`examples/c/challenges.c` holds lean-pcode's C challenge corpus (`inc_u32`, `max_u32`, `mix_u32`,
`sum_u32`, `find_u32`, `copy_bytes`) plus larger functions:
- `isort_u32`: nested loops with loads and stores;
- `gcd_u64`: a `remu` loop;
- `crc32_bytes`: a bitwise CRC with a nested loop;
- `popcount_u64`;
- `strlen_bytes`;
- `classify`: a dense `switch`.

`tests/check_c.py` does the following:
1. builds the corpus at `-O0` and `-O2` (`rv64imfd`, no compressed instructions) and links it into
   the native driver;
2. lifts each function's *linked* bytes at its link address;
3. compiles every module;
4. compares every function against qemu-riscv64.

| | `-O0` | `-O2` |
| --- | --- | --- |
| functions lifted | 12/12 | 12/12 |
| instructions | 454 | 127 |
| generated Lean | 16,200 lines | 2,200 lines |
| cut paths (trap/MMIO/misaligned guards) | 1,459 | 82 |
| lift time (4 parallel Isla jobs) | about 13 min | about 2.3 min |
| native comparison | all agree | all agree |

`isort_u32`, for example, is 72 instructions at `-O0`: 2737 lines of Lean with 249 cuts, because
every local variable lives on the stack and every stack access walks the platform memory map. At
`-O2` it is 20 instructions and 437 lines.

Proved against the C semantics, for every input (`lean/Examples/`):

| function | theorem | contract |
| --- | --- | --- |
| `sum_u32` `-O2` | `SumU32Proof.correct` | `a0` = (Σ `a[i]` mod 2^32) sign-extended, for every `n` |
| `copy_bytes` `-O2` | `CopyBytesProof.correct` | memory = the C loop's byte-by-byte copy, overlapping buffers included; returns `n` |
| `find_u32` `-O2` | `FindU32Proof.correct` (cut points) | the first `i < n` with `a[i] = key`, or `n` |

These proofs check in 3, 5 and 10 s respectively.

What compiled code adds, compared with hand-written assembly:
- **Relocations.** RISC-V objects keep even intra-function branches relocatable (linker
  relaxation). Lifting must use the linked binary: `nm -S` for address and size, then `objcopy`
  for the bytes.
- **The C ABI becomes a premise.** GCC's `sum_u32` tests `n = 0` on all 64 bits of `a1` but
  computes the end pointer from the low 32. A non-canonical `a1` would loop about 2^62 times. The
  theorem therefore needs `Canonical32 a1`: the psABI passes a `uint32_t` sign-extended. Results
  are stated sign-extended for the same reason.
- **Static data needs loading.** At `-O2`, `classify` is a table lookup in `.rodata`, not a jump
  table. The Sail platform serves loads only from ROM and RAM, so the corpus's read-only data is
  placed in RAM (`.corpusdata` at 0x80000000, compiled `-mcmodel=medany`), and the harness loads
  it into the model's memory as an ELF loader would. Before that, the model was `stuck` exactly on
  the eight table cases.
- **Indirect jumps.** A computed `nextPC` is accepted as a return only for the exact `ret`
  encoding; jump tables and calls through pointers are rejected. GCC used neither here.
- **Speed.** Each instruction costs two Isla runs (about 5 s, 10–15 s for memory accesses), and the
  model reloads each time. `--jobs` parallelizes across instructions. Linking at a new address
  re-lifts everything, because traces are keyed by `opcode@pc`.

## Writing proofs

There are two styles. Both use `vcgen` on the generated `step`.
- **Per-instruction invariants** (`run_spec`, as in pcode-lean): one clause per PC. All of the
  pcode-lean ports use this style.
- **Cut points** (`IslaLean/Cut.lean`, used by `FindU32Proof`):
  - state the invariant only at entry and loop heads, and prove the run with `run_cuts`;
  - `walk step, cut` executes everything between cut points;
  - `walk … using tac` also tries `tac` on each new goal, so a load's non-RAM branches are closed
    as they appear instead of being walked.

  A cut-style `count64` needs a two-clause invariant and a six-line proof:
  ```lean
  apply run_cuts _ cut (I s) _ _ _ (by simp [I, Count.initial])
  intro ⟨pc, state⟩ h; refine ⟨10, ?_⟩
  cases pc <;> simp only [I] at h
  all_goals walk Count.step, cut
  all_goals simp_all [I, Returns]
  all_goals bv_omega
  ```

Termination is proved with `IslaLean/Rank.lean`: a second triple per block says a rank decreases.

`IslaLean/Memory.lean` collects the shared lemmas:
- the platform-guard normalizers (128-bit `sle`/`slt`/`srem` → `Nat`);
- `RamWords` and `RamRegion`;
- `ret_aligned`;
- the ABI helpers: `Canonical32`, `canonical_signExtend`, `canonical_ofNat`, `signExtend_inj`;
- `cursor_eq`;
- literal-form variants such as `sub1_add1`.

Pitfalls that cost the most time:
- **Literal spellings.** Generated code writes `4#64`, while specs write `4`. `rw` treats them as
  different; `simp`/`simpa` normalise them.
- **Self-referential facts loop `simp_all`.** For example `x = signExtend (low x)`, or
  `canonical_ofNat`. Orient them so the right-hand side is smaller, or introduce them only after
  walking.
- **Hypothesis names.** `simp_all` may split a named hypothesis into anonymous ones. Destructure
  the cut-point hypothesis *before* `walk`, and fetch branch conditions by their exact type.
- **32-bit C types.** Indexes and keys live sign-extended in 64-bit registers. `Canonical32`
  premises and the ABI helpers turn those comparisons into `Nat` facts for `omega`.

## Trust base and limits

- **Trusted:**
  - the Sail model and Isla's symbolic execution and simplifier;
  - the Isla config's environment (header assumptions);
  - the profile's cut list, where cutting the wrong thing makes theorems vacuous on that path,
    never wrong;
  - this translator.

  A deep embedding, with traces stored as Lean data and given a meaning once inside Lean, would
  shrink the translator's share. It is not done yet.
- **Not modelled:**
  - traps, MMIO and misaligned accesses (all `stuck`);
  - CSRs, atomics, F/D, compressed instructions;
  - calls out of the region and indirect jumps other than `ret`;
  - ELF loading (the C harness loads the corpus's `.rodata` itself);
  - self-modifying code: code is fixed separately from data memory, as in pcode-lean.
- **RV64 only.**

`src/isla_lean/configs/riscv64.toml` is derived from `sail_graham`'s config, with PMP pinned off. It
must match the IR snapshot.

## Status and next steps (October 2026)

**Status.** Everything described above works and is tested:
- the hand-written pcode-lean corpus and the C corpus at `-O0`/`-O2` all lift and agree with qemu;
- 19 contracts check with standard axioms only;
- CI (`.github/workflows/ci.yml`) runs pytest, the Lean build and the qemu native check on GitHub.

How this compares with pcode-lean and with Sail's own `--lean` output (x86 experiments, the AF
bug, why proofs through the whole-ISA interpreter don't scale) is recorded in
`../sail-lean-compare/README.md`.

**Open threads, roughly in order of value:**
1. **SLEIGH versus Sail on the same RISC-V code.** Lift the C corpus through both and compare per
   instruction (sail_graham already does per-instruction comparisons). This answers "is p-code
   good enough" directly, on code both front ends handle.
2. **More proofs in cut style:** `isort_u32` (nested loop with stores) and an `-O0` function
   (stack-resident locals). These test whether `walk` scales.
3. **Lift speed:** link isla-lib (Rust) or keep one Isla process alive, instead of two model
   reloads per instruction; drop the `opcode@pc` cache key's PC dependence where the trace allows.
4. **x86:** build an Isla `x86.ir` with the isla-sail plugin for a head-to-head with pcode-lean's
   x86 corpus.
5. **Trust:** a deep embedding (traces as Lean data with one semantics), so `emit.py`-style
   translation drops out of the trusted base.

**Known gaps:**
- traps, MMIO and misaligned accesses are `stuck`, not modelled;
- there is no ELF loader (`check_c.py` loads `.rodata` itself);
- `-O0` traces (30 MB) are not checked in.

# AI Disclosure
An agent was heavily involved in producing this
