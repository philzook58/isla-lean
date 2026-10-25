"""Tests that need neither Isla nor the Sail IR: checked-in traces replay to the checked-in Lean."""

import pathlib
import re

import pytest

from isla_lean import TraceDirectory, Unsupported, lift
from isla_lean.cli import main
from isla_lean.sexpr import parse
from isla_lean.smt import Terms
from isla_lean.trace import Block, Region

ROOT = pathlib.Path(__file__).resolve().parent.parent
TRACES = ROOT / "tests" / "fixtures" / "traces"
def region_bytes(path: pathlib.Path) -> tuple[int, bytes]:
    base, code = re.search(r"^-- Bytes at (0x[0-9a-f]+): ([0-9a-f]+)$", path.read_text(), re.M).groups()
    return int(base, 16), bytes.fromhex(code)


def replayable(path: pathlib.Path) -> bool:
    base, code = region_bytes(path)
    return all((TRACES / f"{code[i:i + 4].hex()}@{base + i:x}.trace").is_file()
               for i in range(0, len(code), 4))


# The -O0 C modules' traces (about 30 MB) are not checked in; tests/check_c.py regenerates them.
GENERATED = sorted(p for p in (ROOT / "lean" / "Examples" / "Generated").glob("*.lean")
                   if replayable(p))


def test_golden_coverage():
    names = {p.stem for p in GENERATED}
    assert {"Increment", "Scan", "AddMem", "Fill", "Stack32", "SumU32O2", "CopyBytesO2",
            "IsortU32O2", "Crc32BytesO2", "ClassifyO2"} <= names


@pytest.mark.parametrize("path", GENERATED, ids=lambda p: p.stem)
def test_fixture_traces_reproduce_generated_lean(path):
    base, code = region_bytes(path)
    assert lift(path.stem, code, base, TraceDirectory(TRACES)) == path.read_text()


def test_cli_check_accepts_current_output(tmp_path):
    path = ROOT / "lean" / "Examples" / "Generated" / "Increment.lean"
    _, code = region_bytes(path)
    main(["lift", "--hex", code.hex(), "--name", "Increment", "--traces", str(TRACES),
          "-o", str(path), "--check"])
    stale = tmp_path / "Increment.lean"
    stale.write_text("stale\n")
    with pytest.raises(SystemExit, match="stale"):
        main(["lift", "--hex", code.hex(), "--name", "Increment", "--traces", str(TRACES),
              "-o", str(stale), "--check"])


def test_parse_restores_parenthesis_inside_comment():
    (trace,) = parse('(trace\n  (assert (not v1)) ; 0:0 - 0:0)\n')
    assert trace == ["trace", ["assert", ["not", "v1"]]]


def test_parse_strips_symbol_bars_and_rejects_unbalanced():
    assert parse("(read-reg |x10| nil v1)") == [["read-reg", "x10", "nil", "v1"]]
    with pytest.raises(Unsupported):
        parse("(trace (cycle)")


def terms(**sorts):
    t = Terms()
    t.sorts.update({k: ("bv", v) for k, v in sorts.items()})
    return t


def test_negative_immediate_becomes_subtraction():
    assert terms(v=64).term(["bvadd", "v", "#xffffffffffffffff"]) == ("(v - 0x1#64)", ("bv", 64))
    assert terms(v=64).term(["bvadd", "v", "#x0000000000000001"])[0] == "(v + 0x0000000000000001#64)"


def test_flipped_comparison_and_widths():
    t = terms(a=64, b=64)
    assert t.term(["bvuge", "a", "b"]) == ("(b.ule a)", ("bool",))
    assert t.term([["_", "zero_extend", "64"], "a"]) == ("(a.zeroExtend 128)", ("bv", 128))
    assert t.term([["_", "extract", "7", "0"], "a"]) == ("(BitVec.extractLsb 7 0 a)", ("bv", 8))


def test_unknown_operator_is_rejected():
    with pytest.raises(Unsupported, match="operator bvcomp"):
        terms(a=64).term(["bvcomp", "a", "a"])


def test_division_uses_smt_lib_semantics():
    # Lean's `/` returns 0 on division by zero; SMT-LIB's bvudiv returns all ones.
    assert terms(a=64).term(["bvudiv", "a", "a"])[0] == "(BitVec.smtUDiv a a)"
    assert terms(a=64).term(["bvsrem", "a", "a"])[0] == "(BitVec.srem a a)"


def block(pc=0x1000, labels=(0x1000, 0x1004)):
    return Block(pc, Region({p: f"p{i}" for i, p in enumerate(labels)}))


def test_fallthrough_and_assumptions():
    region_block = block()
    lines = region_block.translate([["read-reg", "misa", "nil", "#x1"],
                                    ["declare-const", "v", ["_", "BitVec", "64"]],
                                    ["read-reg", "x11", "nil", "v"],
                                    ["write-reg", "x10", "nil", "v"]])
    assert lines[-1] == "    return .inl (.p1, { s with pc := 0x1004 })"
    assert region_block.region.assumptions == {"misa = #x1"}


PLAIN = ["_", "struct", ["access_kind", ["AK_explicit", ["_", "struct", ["strength", "AS_normal"],
                                                                ["variety", "AV_plain"]]]],
         ["translation", ["_", "unit"]], ["tag", "false"]]


def test_plain_load_becomes_readLE_and_region_exits_are_rejected():
    lines = block().translate([["declare-const", "a", ["_", "BitVec", "64"]],
                               ["read-reg", "x11", "nil", "a"],
                               ["read-mem", "v", PLAIN, "a", "8"],
                               ["write-reg", "x10", "nil", "v"]])
    assert "    let v : BitVec 64 := readLE s.mem a 8" in lines
    with pytest.raises(Unsupported, match="leaves the region"):
        block().translate([["write-reg", "nextPC", "nil", "#x0000000000002000"]])


def test_exclusive_access_is_rejected():
    exclusive = [PLAIN[0], PLAIN[1], ["access_kind", ["AK_explicit", ["_", "struct",
                 ["variety", "AV_exclusive"], ["strength", "AS_normal"]]]], *PLAIN[3:]]
    with pytest.raises(Unsupported, match="access kind"):
        block().translate([["declare-const", "a", ["_", "BitVec", "64"]],
                           ["read-mem", "v", exclusive, "a", "8"]])


def test_one_sided_case_split_becomes_stuck_guard():
    lines = block().translate([["declare-const", "c", "Bool"],
                               ["cases", "loc", ["trace", ["assert", "c"],
                                                 ["write-reg", "x10", "nil", "#x0000000000000001"]]]])
    assert lines[0] == "    if !c then return .inr (.stuck s)"
    assert lines[-1] == "    return .inl (.p1, { s with pc := 0x1004 })"


def test_next_pc_reads_must_see_pc_plus_4():
    block().translate([["read-reg", "nextPC", "nil", "#x0000000000001004"]])
    with pytest.raises(Unsupported, match="nextPC read"):
        block().translate([["read-reg", "nextPC", "nil", "#x0000000000000000"]])


def test_record_stops_accepts_only_requested_cuts():
    from isla_lean.footprint import _record_stops
    stderr = ("No primop foo\n\x1b[0;31merror\x1b[0m: Execution stopped at trap\n"
              "\x1b[0;31merror\x1b[0m: Symbolic (bit)vector length in zeros\n")
    note = _record_stops(stderr, ("trap",), (("Symbolic (bit)vector length in zeros", "misaligned"),))
    assert note == "; isla-lean stopped: 1 at misaligned, 1 at trap\n"
    with pytest.raises(Unsupported, match="isla-footprint error"):
        _record_stops(stderr, ("trap",))


def test_instruction_with_empty_execute_is_rejected():
    class Source(TraceDirectory):
        def footprint(self, word, pc):
            return "; isla-lean execute events: [0]\n(trace (cycle))\n"
    with pytest.raises(Unsupported, match="execute performs no events"):
        lift("Fld", bytes.fromhex("07300500"), 0x1000, Source(TRACES))


def test_case_split_needs_complementary_assertions():
    t = ["declare-const", "c", "Bool"]
    with pytest.raises(Unsupported, match="complementary"):
        block().translate([t, ["cases", "loc", ["trace", ["assert", "c"]], ["trace", ["assert", "c"]]]])


def test_compressed_instructions_are_rejected():
    with pytest.raises(Unsupported, match="compressed"):
        lift("Tiny", bytes.fromhex("05058280"), 0x1000, TraceDirectory(TRACES))


def test_computed_jump_other_than_ret_is_rejected():
    jump = [["declare-const", "t", ["_", "BitVec", "64"]], ["read-reg", "x5", "nil", "t"],
            ["write-reg", "nextPC", "nil", "t"]]
    with pytest.raises(Unsupported, match="indirect jump"):
        Block(0x1000, Region({0x1000: "p0"}), bytes.fromhex("67800200")).translate(jump)
    lines = Block(0x1000, Region({0x1000: "p0"}), bytes.fromhex("67800000")).translate(jump)
    assert lines[-1] == "    return .inr (.ret { s with pc := t })"
