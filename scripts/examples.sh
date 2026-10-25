#!/bin/sh
# Assemble the example routines, lift them through Isla, and check the Lean proofs.
#   ISLA_LEAN_ARCH=/path/to/rv64d.ir scripts/examples.sh          # live Isla (sail_graham isla-snapshots/rv64d.ir)
#   scripts/examples.sh --traces tests/fixtures/traces           # replay checked-in traces
# Lean runs in a memory-capped systemd scope (MEMORY_MAX, default 3G) when systemd-run exists
# and $CI is unset (CI runners have no user systemd session).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
cap() {
  if command -v systemd-run >/dev/null && [ -z "$CI" ]; then
    systemd-run --user --scope -q -p MemoryMax="${MEMORY_MAX:-3G}" -p MemorySwapMax=0 "$@"
  else
    "$@"
  fi
}
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT
riscv64-linux-gnu-as -march=rv64i -o "$BUILD/routines.o" examples/routines.S
for pair in inc64:Increment umax64:Maximum count64:Count scan64:Scan add128:Add128 addmem:AddMem \
    fill64:Fill stack32:Stack32 reserve256:Reserve256 alias64:Alias stack64:Stack shift64:Shift; do
  routine=${pair%%:*}; name=${pair##*:}
  riscv64-linux-gnu-objcopy -O binary --only-section=".text.$routine" "$BUILD/routines.o" "$BUILD/$routine.bin"
  uv run isla-lean lift --binary "$BUILD/$routine.bin" --name "$name" \
    -o "lean/Examples/Generated/$name.lean" "$@"
done
cd lean && cap lake build
