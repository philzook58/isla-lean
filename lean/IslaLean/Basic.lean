import IslaLean.Run

/-! Machine state for Lean emitted by `isla-lean`: the integer registers, `pc`, and flat
little-endian byte memory. The traces' other register reads are environment assumptions listed in
each generated header. Code is fixed separately from data memory, so self-modifying code is
excluded, as in pcode-lean. -/
namespace IslaLean

abbrev Memory := BitVec 64 → BitVec 8

/-- `readLE`/`writeLE` are pcode-lean's definitions, so its memory lemmas and proofs carry over. -/
def readLE (mem : Memory) (address : BitVec 64) : (bytes : Nat) → BitVec (bytes * 8)
  | 0 => 0
  | n + 1 => ((readLE mem (address + 1) n).setWidth ((n + 1) * 8) <<< 8) |||
      (mem address).setWidth ((n + 1) * 8)

def writeLE (mem : Memory) (address : BitVec 64) (bytes : Nat)
    (value : BitVec (bytes * 8)) : Memory :=
  fun p ↦ if (p - address).toNat < bytes
    then (value >>> ((p - address).toNat * 8)).setWidth 8 else mem p

structure RVState where
  x1 : BitVec 64 := 0
  x2 : BitVec 64 := 0
  x3 : BitVec 64 := 0
  x4 : BitVec 64 := 0
  x5 : BitVec 64 := 0
  x6 : BitVec 64 := 0
  x7 : BitVec 64 := 0
  x8 : BitVec 64 := 0
  x9 : BitVec 64 := 0
  x10 : BitVec 64 := 0
  x11 : BitVec 64 := 0
  x12 : BitVec 64 := 0
  x13 : BitVec 64 := 0
  x14 : BitVec 64 := 0
  x15 : BitVec 64 := 0
  x16 : BitVec 64 := 0
  x17 : BitVec 64 := 0
  x18 : BitVec 64 := 0
  x19 : BitVec 64 := 0
  x20 : BitVec 64 := 0
  x21 : BitVec 64 := 0
  x22 : BitVec 64 := 0
  x23 : BitVec 64 := 0
  x24 : BitVec 64 := 0
  x25 : BitVec 64 := 0
  x26 : BitVec 64 := 0
  x27 : BitVec 64 := 0
  x28 : BitVec 64 := 0
  x29 : BitVec 64 := 0
  x30 : BitVec 64 := 0
  x31 : BitVec 64 := 0
  pc : BitVec 64 := 0
  mem : Memory := fun _ ↦ 0

/-- A routine returns through a symbolic `nextPC`, or gets `stuck`: a trace assertion failed, or
execution reached a path cut from the model (an access fault, trap, or MMIO device access).
Contracts prove `stuck` unreachable, so they say nothing about those behaviors. -/
inductive Exit where
  | ret (s : RVState)
  | stuck (s : RVState)

end IslaLean
