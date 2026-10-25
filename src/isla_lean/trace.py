"""Translate one instruction's Isla trace tree into the body of a Lean `step` alternative.

- `declare-const`/`define-const` become typed `let`s; integer register reads and writes become
  `RVState` fields.
- `read-mem`/`write-mem` of plain explicit accesses become `readLE`/`writeLE` on `RVState.mem`.
- `cases` whose branches begin with complementary assertions becomes `if`. A `cases` with one
  branch (its sibling was cut, e.g. an access fault or MMIO access) and any other assertion become
  `stuck` exits when false: behavior outside the model, which contracts must prove unreachable.
- A trace that writes no `nextPC` falls through to `pc + 4` (the Sail RISC-V model's default);
  a concrete `nextPC` must be an instruction in the region; a symbolic one is the routine's return.
- Concrete reads of registers outside `RVState` are the Isla configuration's environment
  assumptions and are collected for the generated header, not checked.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .errors import Unsupported
from .sexpr import SExpr, render
from .smt import Terms, lean_type, literal_value, sort_of

RET = (0x00008067).to_bytes(4, "little")
GPRS = frozenset(f"x{i}" for i in range(1, 32))
IGNORED = frozenset({"cycle", "branch", "branch-address", "mark-reg", "assume-reg", "define-enum",
                     "define-struct", "define-union", "instr"})


@dataclass
class Region:
    """Instruction addresses of the lifted region and their PC constructor names."""

    labels: dict[int, str]
    assumptions: set[str] = field(default_factory=set)


class Block:
    def __init__(self, pc: int, region: Region, word: bytes = b""):
        self.pc, self.region, self.word = pc, region, word
        self.terms = Terms()

    def translate(self, events: list[SExpr], indent: int = 2) -> list[str]:
        return self._events(events, indent, None)

    def _events(self, events: list[SExpr], indent: int, next_pc: SExpr | None) -> list[str]:
        pad = "  " * indent
        out: list[str] = []
        for ev in events:
            if not isinstance(ev, list) or not ev or not isinstance(ev[0], str):
                raise Unsupported(f"malformed event {ev}")
            kind = ev[0]
            if kind == "declare-const":
                self.terms.sorts[ev[1]] = sort_of(ev[2])
            elif kind in IGNORED:
                pass
            elif kind == "read-reg":
                out += self._read(ev[1], ev[3], pad)
            elif kind == "define-const":
                term, sort = self.terms.term(ev[2])
                self.terms.sorts[ev[1]] = sort
                out.append(f"{pad}let {ev[1]} : {lean_type(sort)} := {term}")
            elif kind == "write-reg":
                reg, value = ev[1], ev[3]
                if reg == "nextPC":
                    self.terms.term(value)  # reject untranslatable targets early
                    next_pc = value
                elif reg in GPRS:
                    term, _ = self.terms.term(value)
                    out.append(f"{pad}let s := {{ s with {reg} := {term} }}")
                else:
                    raise Unsupported(f"write of {reg}")
            elif kind == "assert":
                cond, _ = self.terms.term(ev[1])
                out.append(f"{pad}if !{cond} then return .inr (.stuck s)")
            elif kind == "cases":
                branches = ev[2:]
                if len(branches) == 1:
                    # The surviving branch continues the instruction at the same indentation.
                    guard, rest = self._one_sided(branches[0])
                    return out + [f"{pad}if !{guard} then return .inr (.stuck s)",
                                  *self._events(rest, indent, next_pc)]
                return out + self._cases(branches, indent, next_pc)
            elif kind == "read-mem":
                value, request, address, size = ev[1:5]
                n = self._access(request, size)
                addr, _ = self.terms.term(address)
                self.terms.sorts[value] = ("bv", 8 * n)
                out.append(f"{pad}let {value} : BitVec {8 * n} := readLE s.mem {addr} {n}")
            elif kind == "write-mem":
                success, request, address, data, size = ev[1:6]
                n = self._access(request, size)
                (addr, _), (val, _) = self.terms.term(address), self.terms.term(data)
                out.append(f"{pad}let s := {{ s with mem := writeLE s.mem {addr} {n} {val} }}")
                self.terms.sorts[success] = ("bool",)
                out.append(f"{pad}let {success} : Bool := true")
            elif kind in ("write-mem-value", "address-announce", "write-mem-tag", "read-mem-tag"):
                raise Unsupported(f"memory event {kind}")
            else:
                raise Unsupported(f"event {kind}")
        return out + self._finish(indent, next_pc)

    def _read(self, reg: str, value: SExpr, pad: str) -> list[str]:
        if isinstance(value, str) and value in self.terms.sorts:
            if reg not in GPRS:
                raise Unsupported(f"symbolic read of {reg}")
            return [f"{pad}let {value} : BitVec 64 := s.{reg}"]
        if reg in ("PC", "nextPC"):
            expected = self.pc if reg == "PC" else (self.pc + 4) % (1 << 64)
            if not isinstance(value, str) or literal_value(value) != expected:
                raise Unsupported(f"{reg} read {render(value)} at {self.pc:#x}, expected {expected:#x}")
            return []
        if reg in GPRS:
            raise Unsupported(f"concrete read of {reg}")
        self.region.assumptions.add(f"{reg} = {_summary(value)}")
        return []

    def _access(self, request: SExpr, size: SExpr) -> int:
        """Accept plain explicit accesses of 1, 2, 4 or 8 bytes without tags or translation."""
        fields = _fields(request)
        kind = fields.get("access_kind")
        if not (isinstance(kind, list) and kind[:1] == ["AK_explicit"] and len(kind) == 2
                and _fields(kind[1]) == {"variety": "AV_plain", "strength": "AS_normal"}):
            raise Unsupported(f"memory access kind {render(fields.get('access_kind', request))}")
        if fields.get("translation") != ["_", "unit"] or fields.get("tag") not in ("false", ["None", ["_", "unit"]]):
            raise Unsupported("translated or tagged memory access")
        if not isinstance(size, str) or size not in ("1", "2", "4", "8"):
            raise Unsupported(f"memory access of {render(size)} bytes")
        return int(size)

    def _one_sided(self, branch: SExpr) -> tuple[str, list[SExpr]]:
        if branch[:1] != ["trace"] or len(branch) < 2 or branch[1][:1] != ["assert"]:
            raise Unsupported("one-sided case split without a guarding assertion")
        cond, _ = self.terms.term(branch[1][1])
        return cond, branch[2:]

    def _cases(self, branches: list[SExpr], indent: int, next_pc: SExpr | None) -> list[str]:
        pad = "  " * indent
        if len(branches) != 2 or any(b[:1] != ["trace"] or len(b) < 2 for b in branches):
            raise Unsupported(f"{len(branches)}-way case split")
        (t_head, *t_rest), (f_head, *f_rest) = (b[1:] for b in branches)
        if t_head[:1] != ["assert"] or f_head != ["assert", ["not", t_head[1]]]:
            raise Unsupported("case split without complementary assertions")
        cond, _ = self.terms.term(t_head[1])
        saved = dict(self.terms.sorts)
        then = self._events(t_rest, indent + 1, next_pc)
        self.terms.sorts = saved
        other = self._events(f_rest, indent + 1, next_pc)
        return [f"{pad}if {cond} then", *then, f"{pad}else", *other]

    def _finish(self, indent: int, next_pc: SExpr | None) -> list[str]:
        pad = "  " * indent
        if next_pc is None:
            target = self.pc + 4
        elif isinstance(next_pc, str) and (value := literal_value(next_pc)) is not None:
            target = value
        else:
            # Only `ret` (jalr x0, 0(ra)) leaves the region as a return. Any other computed target
            # (a jump table, a call through a pointer) would otherwise pass for a return.
            if self.word != RET:
                raise Unsupported(f"indirect jump at {self.pc:#x} is not a return")
            term, _ = self.terms.term(next_pc)
            return [f"{pad}return .inr (.ret {{ s with pc := {term} }})"]
        if target not in self.region.labels:
            raise Unsupported(f"branch from {self.pc:#x} to {target:#x} leaves the region")
        label = self.region.labels[target]
        return [f"{pad}return .inl (.{label}, {{ s with pc := 0x{target:x} }})"]


def _summary(value: SExpr) -> str:
    """Render a concrete value, writing a vector of identical entries as `(_ vec item × n)`."""
    if isinstance(value, list) and value[:2] == ["_", "vec"] and len(value) > 3 \
            and all(item == value[2] for item in value[3:]):
        return f"(_ vec {render(value[2])} × {len(value) - 2})"
    return render(value)


def _fields(value: SExpr) -> dict:
    """Fields of an Isla `(_ struct (name value) ...)`, whose field order varies."""
    if isinstance(value, list) and value[:2] == ["_", "struct"]:
        return {f[0]: f[1] for f in value[2:]}
    return {}
