"""Command line: `isla-lean lift (--binary FILE | --hex HEX) --name Name [options]`."""

from __future__ import annotations

import argparse
import os
import pathlib
import sys

from .errors import Unsupported
from .footprint import IslaRunner, TraceDirectory
from .lift import lift


def _size(text: str) -> int:
    units = {"K": 1 << 10, "M": 1 << 20, "G": 1 << 30}
    if text[-1:].upper() in units:
        return int(float(text[:-1]) * units[text[-1].upper()])
    return int(text)


def _parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(prog="isla-lean", description=__doc__)
    sub = ap.add_subparsers(dest="command", required=True)
    p = sub.add_parser("lift", help="lift a raw code region into a Lean module")
    code = p.add_mutually_exclusive_group(required=True)
    code.add_argument("--binary", type=pathlib.Path, help="raw little-endian instruction bytes")
    code.add_argument("--hex", help="instruction bytes as hex, in memory order")
    p.add_argument("--name", required=True, help="Lean namespace for the module")
    p.add_argument("--base", type=lambda x: int(x, 0), default=0x1000,
                   help="address of the first byte (default 0x1000)")
    p.add_argument("--arch", type=pathlib.Path, default=os.environ.get("ISLA_LEAN_ARCH"),
                   help="Sail IR snapshot, e.g. rv64d.ir (or $ISLA_LEAN_ARCH)")
    p.add_argument("--config", type=pathlib.Path,
                   help="Isla config (default: the packaged profile for the IR file name)")
    p.add_argument("--kill", action="append",
                   help="cut executions reaching this Sail function (repeatable; default: profile)")
    p.add_argument("--traces", type=pathlib.Path,
                   help="replay traces from this directory instead of running Isla")
    p.add_argument("--cache", type=pathlib.Path,
                   default=pathlib.Path(os.environ.get("XDG_CACHE_HOME", pathlib.Path.home() / ".cache"))
                   / "isla-lean", help="trace cache root (default ~/.cache/isla-lean)")
    p.add_argument("--no-cache", action="store_true")
    p.add_argument("--isla", default="isla-footprint", help="isla-footprint executable")
    p.add_argument("--timeout", type=int, default=20, help="Isla timeout per instruction, seconds")
    p.add_argument("--jobs", type=int, default=4, help="Isla processes to run in parallel (default 4)")
    p.add_argument("--memory-limit", type=_size, default=_size("4G"),
                   help="address-space limit for each Isla process (default 4G)")
    p.add_argument("-o", "--output", type=pathlib.Path, help="write here instead of stdout")
    p.add_argument("--check", action="store_true",
                   help="fail if --output differs from the generated module instead of writing it")
    return ap


def main(argv: list[str] | None = None) -> None:
    args = _parser().parse_args(argv)
    code = args.binary.read_bytes() if args.binary else bytes.fromhex(args.hex)
    try:
        if args.traces:
            source = TraceDirectory(args.traces)
        else:
            if args.arch is None:
                sys.exit("isla-lean: pass --arch or set ISLA_LEAN_ARCH (or replay with --traces)")
            source = IslaRunner(args.arch, args.config, kills=tuple(args.kill) if args.kill else None,
                                executable=args.isla, timeout=args.timeout,
                                memory_limit=args.memory_limit,
                                cache=None if args.no_cache else args.cache)
        text = lift(args.name, code, args.base, source, jobs=args.jobs)
    except (Unsupported, FileNotFoundError, ValueError) as error:
        sys.exit(f"isla-lean: {error}")
    if args.check:
        if args.output is None:
            sys.exit("isla-lean: --check needs --output")
        if not args.output.is_file() or args.output.read_text() != text:
            sys.exit(f"isla-lean: {args.output} is stale")
    elif args.output:
        args.output.write_text(text)
    else:
        sys.stdout.write(text)
