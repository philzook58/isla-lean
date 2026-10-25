"""Translate Isla's SMT-LIB bit-vector terms into Lean `BitVec`/`Bool` expressions."""

from __future__ import annotations

from .errors import Unsupported
from .sexpr import SExpr

# A sort is ("bool",) or ("bv", width).
Sort = tuple

BINARY = {"bvadd": "+", "bvsub": "-", "bvmul": "*", "bvand": "&&&", "bvor": "|||", "bvxor": "^^^"}
COMPARE = {"bvult": "ult", "bvslt": "slt", "bvule": "ule", "bvsle": "sle"}
FLIPPED = {"bvugt": "ult", "bvsgt": "slt", "bvuge": "ule", "bvsge": "sle"}
SHIFTS = {"bvshl": "<<<", "bvlshr": ">>>"}
# Lean's `/` and `%` return 0 on division by zero; these follow SMT-LIB exactly.
DIVISION = {"bvudiv": "BitVec.smtUDiv", "bvsdiv": "BitVec.smtSDiv", "bvurem": "BitVec.umod",
            "bvsrem": "BitVec.srem", "bvsmod": "BitVec.smod"}


def literal(tok: str) -> tuple[str, Sort] | None:
    """Literals use `#` notation, the form `simp` normalizes to."""
    if tok.startswith("#x"):
        n = 4 * (len(tok) - 2)
        return f"0x{tok[2:]}#{n}", ("bv", n)
    if tok.startswith("#b"):
        n = len(tok) - 2
        return f"0b{tok[2:]}#{n}", ("bv", n)
    if tok in ("true", "false"):
        return tok, ("bool",)
    return None


def literal_value(tok: str) -> int | None:
    if tok.startswith("#x"):
        return int(tok[2:], 16)
    if tok.startswith("#b"):
        return int(tok[2:], 2)
    return None


def sort_of(s: SExpr) -> Sort:
    if s == "Bool":
        return ("bool",)
    if isinstance(s, list) and s[:2] == ["_", "BitVec"]:
        return ("bv", int(s[2]))
    raise Unsupported(f"sort {s}")


def lean_type(sort: Sort) -> str:
    return "Bool" if sort == ("bool",) else f"BitVec {sort[1]}"


def receiver(x: str) -> str:
    """Parenthesize a literal used before `.method`, which Lean would read as a decimal point."""
    return x if x.startswith("(") or x[0].isalpha() or x[0] == "_" else f"({x})"


class Terms:
    """Translator with the sorts of the trace's declared and defined variables."""

    def __init__(self) -> None:
        self.sorts: dict[str, Sort] = {}

    def term(self, e: SExpr) -> tuple[str, Sort]:
        if isinstance(e, str):
            if (lit := literal(e)) is not None:
                return lit
            if e in self.sorts:
                return e, self.sorts[e]
            raise Unsupported(f"unknown symbol {e}")
        head, *args = e
        if isinstance(head, list) and head[:1] == ["_"]:
            return self._indexed(head, args)
        if head == "bvadd" and len(args) == 2 and (c := self._negative(args[1])) is not None:
            # A negative immediate arrives as `bvadd x #xffff...`. Lean's kernel checks
            # definitional equalities involving such near-2^n literals extremely slowly, so emit
            # the identical `x - k` with the small two's-complement negation instead.
            x, sort = self.term(args[0])
            return f"({x} - 0x{c:x}#{sort[1]})", sort
        if head in BINARY:
            terms = [self.term(a) for a in args]
            return "(" + f" {BINARY[head]} ".join(t for t, _ in terms) + ")", terms[0][1]
        if head in DIVISION:
            (x, sx), (y, _) = self.term(args[0]), self.term(args[1])
            return f"({DIVISION[head]} {x} {y})", sx
        if head in SHIFTS or head == "bvashr":
            (x, sx), (y, _) = self.term(args[0]), self.term(args[1])
            if head == "bvashr":
                return f"({receiver(x)}.sshiftRight' {y})", sx
            return f"({x} {SHIFTS[head]} {y})", sx
        if head == "bvnot":
            x, sx = self.term(args[0])
            return f"(~~~{x})", sx
        if head == "bvneg":
            x, sx = self.term(args[0])
            return f"(-{x})", sx
        if head in COMPARE or head in FLIPPED:
            (x, _), (y, _) = self.term(args[0]), self.term(args[1])
            if head in FLIPPED:
                x, y = y, x
            return f"({receiver(x)}.{COMPARE.get(head) or FLIPPED[head]} {y})", ("bool",)
        if head == "=":
            (x, _), (y, _) = self.term(args[0]), self.term(args[1])
            return f"({x} == {y})", ("bool",)
        if head == "not":
            x, _ = self.term(args[0])
            return f"(!{x})", ("bool",)
        if head in ("and", "or"):
            op = " && " if head == "and" else " || "
            return "(" + op.join(self.term(a)[0] for a in args) + ")", ("bool",)
        if head == "ite":
            (c, _), (t, st), (f, _) = (self.term(a) for a in args)
            return f"(if {c} then {t} else {f})", st
        if head == "concat":
            (x, (_, n)), (y, (_, m)) = self.term(args[0]), self.term(args[1])
            return f"({x} ++ {y})", ("bv", n + m)
        raise Unsupported(f"operator {head}")

    def _indexed(self, head: list, args: list) -> tuple[str, Sort]:
        (inner,) = args
        x, sort = self.term(inner)
        if sort == ("bool",):
            raise Unsupported(f"indexed operator on Bool: {head}")
        n = sort[1]
        op = head[1]
        if op == "extract":
            hi, lo = int(head[2]), int(head[3])
            return f"(BitVec.extractLsb {hi} {lo} {x})", ("bv", hi - lo + 1)
        if op in ("zero_extend", "sign_extend"):
            k = int(head[2])
            method = "zeroExtend" if op == "zero_extend" else "signExtend"
            return f"({receiver(x)}.{method} {n + k})", ("bv", n + k)
        raise Unsupported(f"indexed operator {op}")

    def _negative(self, tok: SExpr) -> int | None:
        """The two's-complement negation of a literal whose top bit is set."""
        if not isinstance(tok, str) or not tok.startswith("#x"):
            return None
        n, value = 4 * (len(tok) - 2), int(tok[2:], 16)
        return (-value) % (1 << n) if value >> (n - 1) else None
