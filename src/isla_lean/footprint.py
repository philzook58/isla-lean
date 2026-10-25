"""Sources of per-instruction Isla trace text: a live `isla-footprint`, or a trace directory.

A cache directory written by `IslaRunner` is itself a valid `TraceDirectory`, so lifting can be
replayed offline (and in tests) without Isla or the large Sail IR file.
"""

from __future__ import annotations

import hashlib
import os
import pathlib
import re
import resource
import shutil
import subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from importlib import resources
from typing import Protocol

from .errors import Unsupported

PROVENANCE = "PROVENANCE"


def packaged_config(name: str) -> pathlib.Path:
    return pathlib.Path(str(resources.files("isla_lean").joinpath("configs", name)))


@dataclass(frozen=True)
class Profile:
    """How to run one Sail IR snapshot: its Isla config, the functions whose paths are cut, and
    Isla errors that are known to end exactly one class of path (recorded under a label).

    A cut path never reaches the emitted Lean as behavior. Its sibling branch keeps the guarding
    assertion, which becomes a `stuck` exit, so contracts must prove it unreachable. If a cut
    leaves an instruction with no path at all, lifting fails.
    """

    config: str
    kills: tuple[str, ...] = ()
    known_errors: tuple[tuple[str, str], ...] = ()


# Keyed by IR file name. In `rv64d.ir`, `execute` returns traps as values (built by `trap`) and
# the footprint never runs the trap handler, so a trap would otherwise look like a no-op: trap
# paths are cut at `trap`. MMIO device accesses are cut at the platform's MMIO entry points.
# A misaligned access splits by `count_trailing_zeros` of the address, which Isla cannot size
# symbolically; that error ends exactly the misaligned path.
#
# The older `riscv_model_rv64d.ir` snapshot is deliberately absent: its illegal and unimplemented
# instructions (ecall, fld, opcode 0, ...) execute nothing, indistinguishable from a no-op.
PROFILES = {
    "rv64d.ir": Profile(
        "riscv64.toml",
        ("trap", "mmio_read", "mmio_write"),
        (("Symbolic (bit)vector length in zeros", "misaligned access"),
         ("Symbolic (bit)vector length in subrange_internal", "misaligned access"))),
}

ANSI = re.compile(r"\x1b\[[0-9;]*m")
STOPPED = re.compile(r"^error: Execution stopped at (\S+)$")
STOP_NOTE = "; isla-lean stopped:"
EXECUTE_NOTE = "; isla-lean execute events:"
# Bump when the Isla command line changes, so cached traces from older runners are not reused.
RUNNER_FORMAT = 4


def _digest(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def trace_name(word: bytes, pc: int) -> str:
    return f"{word.hex()}@{pc:x}.trace"


class TraceSource(Protocol):
    def footprint(self, word: bytes, pc: int) -> str: ...
    def provenance(self) -> list[str]: ...


class TraceDirectory:
    """Read `<word>@<pc>.trace` files, failing on a missing trace rather than guessing."""

    def __init__(self, directory: pathlib.Path):
        self.directory = pathlib.Path(directory)

    def footprint(self, word: bytes, pc: int) -> str:
        path = self.directory / trace_name(word, pc)
        if not path.is_file():
            raise Unsupported(f"no cached trace {path}")
        return path.read_text()

    def provenance(self) -> list[str]:
        path = self.directory / PROVENANCE
        return path.read_text().splitlines() if path.is_file() else ["trace directory (unknown model)"]


class IslaRunner:
    """Run `isla-footprint -t` per instruction under an address-space limit, with caching."""

    def __init__(self, arch: pathlib.Path, config: pathlib.Path | None = None, *,
                 kills: tuple[str, ...] | None = None, executable: str = "isla-footprint",
                 timeout: int = 20, memory_limit: int = 4 << 30, cache: pathlib.Path | None = None):
        self.arch = pathlib.Path(arch)
        profile = PROFILES.get(self.arch.name)
        if config is None and profile is None:
            raise FileNotFoundError(f"no packaged profile for {self.arch.name}; pass a config")
        self.config = pathlib.Path(config) if config else packaged_config(profile.config)
        self.kills = tuple(kills) if kills is not None else (profile.kills if profile else ())
        self.known_errors = profile.known_errors if profile else ()
        for path in (self.arch, self.config):
            if not path.is_file():
                raise FileNotFoundError(path)
        resolved = shutil.which(executable)
        if resolved is None:
            raise FileNotFoundError(f"{executable} not found on PATH")
        self.executable, self.timeout, self.memory_limit = resolved, timeout, memory_limit
        self._provenance: list[str] | None = None
        self._memo: dict[tuple[bytes, int], str] = {}
        self.cache = None
        if cache is not None:
            kills = hashlib.sha256(",".join(self.kills).encode()).hexdigest()[:8]
            key = f"{self._arch_digest()[:12]}-{_digest(self.config)[:12]}-{kills}-v{RUNNER_FORMAT}"
            self.cache = pathlib.Path(cache) / key
            self.cache.mkdir(parents=True, exist_ok=True)
            (self.cache / PROVENANCE).write_text("\n".join(self.provenance()) + "\n")

    def _arch_digest(self) -> str:
        if not hasattr(self, "_arch_sha"):
            self._arch_sha = _digest(self.arch)
        return self._arch_sha

    def _limit(self) -> None:
        resource.setrlimit(resource.RLIMIT_AS, (self.memory_limit, self.memory_limit))

    def _run(self, args: list[str]) -> subprocess.CompletedProcess[str]:
        result = subprocess.run([self.executable, *args], capture_output=True, text=True,
                                timeout=self.timeout + 30, preexec_fn=self._limit)
        if result.returncode != 0:
            raise Unsupported(f"isla-footprint failed ({result.returncode}): {result.stderr[-500:]}")
        return result

    def version(self) -> str:
        # `--version` still demands an instruction argument, and prints to stderr.
        result = self._run(["--version", "-i", "0"])
        return (result.stdout.strip() or result.stderr.strip()).splitlines()[-1]

    def provenance(self) -> list[str]:
        if self._provenance is None:
            self._provenance = [
                f"isla-footprint {self.version()}",
                f"model {self.arch.name} sha256 {self._arch_digest()[:16]}",
                f"config {self.config.name} sha256 {_digest(self.config)[:16]}",
                "paths cut at: " + (", ".join(self.kills) or "(none)"),
                *(f"paths ending in Isla error {e!r} are cut as: {label}"
                  for e, label in self.known_errors),
            ]
        return self._provenance

    def prefetch(self, instructions: list[tuple[bytes, int]], jobs: int) -> None:
        """Trace independent instructions concurrently (each Isla process keeps its own memory
        limit); results land in the cache, or are kept in memory without one."""
        if jobs <= 1:
            return
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for (word, pc), text in zip(instructions,
                                        pool.map(lambda i: self.footprint(*i), instructions)):
                self._memo[(word, pc)] = text

    def footprint(self, word: bytes, pc: int) -> str:
        if (word, pc) in self._memo:
            return self._memo[(word, pc)]
        if self.cache is not None and (path := self.cache / trace_name(word, pc)).is_file():
            return path.read_text()
        cut = [arg for name in self.kills for arg in ("-k", name)]
        common = [
            "-A", os.fspath(self.arch), "-C", os.fspath(self.config), "-i", word.hex(), "-x",
            "-e", "little", "--executable", "-T", "1",
            "--timeout", str(self.timeout), "-R", f"PC=0x{pc:016x}",
            # Sail's fetch sets nextPC = PC + 4 before execute; the footprint function does not.
            "-R", f"nextPC=0x{(pc + 4) % (1 << 64):016x}",
            *cut, *(["-c"] if cut or self.known_errors else []),
        ]
        result = self._run([*common, "-s", "-t"])
        stops = _record_stops(result.stderr, self.kills, self.known_errors)
        # A second, unsimplified pass with every call traced: an instruction the snapshot does
        # not implement reaches `execute` and returns without a single event, which the
        # simplified trace cannot distinguish from a no-op.
        probe = self._run([*common, "--trace-all"]).stdout
        counts = [len(re.findall(r"\n\s*\((?!assume-reg|define-enum)", body)) for body in
                  re.findall(r"\(call \|execute\|\)(.*?)\(return \|execute\|\)", probe, re.S)]
        text = stops + f"{EXECUTE_NOTE} {counts}\n" + result.stdout
        if self.cache is not None:
            (self.cache / trace_name(word, pc)).write_text(text)
        return text


def _record_stops(stderr: str, kills: tuple[str, ...],
                  known_errors: tuple[tuple[str, str], ...] = ()) -> str:
    """With `-c`, Isla reports killed executions as errors; accept only the requested cuts.

    Any other error would silently drop a path, so it is fatal. The cut counts are kept as a
    trace comment and copied into the generated header.
    """
    lines = [ANSI.sub("", line).strip() for line in stderr.splitlines()]
    errors = [line for line in lines if re.search(r"\berror\b", line, re.I)]
    stops = Counter()
    for line in errors:
        m = STOPPED.search(line)
        if m is not None and m.group(1) in kills:
            stops[m.group(1)] += 1
            continue
        label = next((label for e, label in known_errors if line == f"error: {e}"), None)
        if label is None:
            raise Unsupported(f"isla-footprint error: {line}")
        stops[label] += 1
    if not stops:
        return ""
    return STOP_NOTE + " " + ", ".join(f"{n} at {name}" for name, n in sorted(stops.items())) + "\n"
