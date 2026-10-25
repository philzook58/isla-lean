import Examples.Generated.AddMem
import Examples.Generated.Stack32
import Examples.Generated.Reserve256
import IslaLean.Memory
import IslaLean.Trace

/-! Memory-writing examples, mirroring `pcode-lean/Examples/WriteProofs.lean`.
RISC-V keeps the return address in `ra`, so no return-cell separation premise is needed. Every
accessed limb must be aligned and in RAM; otherwise the Sail model's access is `stuck`. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.WriteProof

private theorem ret_aligned (x : BitVec 64) :
    BitVec.extractLsb 0 0 (x &&& 0xfffffffffffffffe#64) = 0#1 := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp

/-! ## `addmem`: two-limb add of buffers `a1` and `a2` into `a0`, returning the carry. -/

def carryBit (b : Bool) : BitVec 64 := if b then 1 else 0

/-- The machine's order: the high limbs are loaded after the low limb is stored, so an
overlapping output changes the high inputs, exactly as in the native byte reference. -/
structure AddResult where
  lo : BitVec 64
  c0 : BitVec 64
  mem1 : Memory
  sum1 : BitVec 64
  c1 : BitVec 64
  hi : BitVec 64
  c2 : BitVec 64
  mem2 : Memory

def addResult (s : RVState) : AddResult :=
  let x0 := readLE s.mem s.x11 8
  let lo := x0 + readLE s.mem s.x12 8
  let c0 := carryBit (decide (lo.toNat < x0.toNat))
  let mem1 := writeLE s.mem s.x10 8 lo
  let x1 := readLE mem1 (s.x11 + 8) 8
  let sum1 := x1 + readLE mem1 (s.x12 + 8) 8
  let c1 := carryBit (decide (sum1.toNat < x1.toNat))
  let hi := sum1 + c0
  let c2 := carryBit (decide (hi.toNat < c0.toNat))
  ⟨lo, c0, mem1, sum1, c1, hi, c2, writeLE mem1 (s.x10 + 8) 8 hi⟩

def AddPost (s : RVState) : Exit → Prop
  | .ret out => let r := addResult s
      out.mem = r.mem2 ∧ out.x10 = (r.c1 ||| r.c2) ∧ out.pc = s.x1 &&& ~~~1 ∧
      out.x1 = s.x1 ∧ out.x2 = s.x2
  | .stuck _ => False

def AddPre (s : RVState) : Prop := RamRegion s.x10 2 ∧ RamRegion s.x11 2 ∧ RamRegion s.x12 2

private def addInv (s : RVState) (f : AddMem.Frame) : Prop :=
  let r := addResult s
  f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧ AddPre s ∧
  (f.1 ≠ .p14 → f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.x12 = s.x12) ∧
  match f.1 with
  | .p0 => f.2.mem = s.mem
  | .p1 => f.2.mem = s.mem ∧ f.2.x5 = readLE s.mem s.x11 8
  | .p2 => f.2.mem = s.mem ∧ f.2.x5 = readLE s.mem s.x11 8 ∧ f.2.x6 = readLE s.mem s.x12 8
  | .p3 => f.2.mem = s.mem ∧ f.2.x5 = readLE s.mem s.x11 8 ∧ f.2.x7 = r.lo
  | .p4 => f.2.mem = s.mem ∧ f.2.x7 = r.lo ∧ f.2.x28 = r.c0
  | .p5 => f.2.mem = r.mem1 ∧ f.2.x28 = r.c0
  | .p6 => f.2.mem = r.mem1 ∧ f.2.x28 = r.c0 ∧ f.2.x5 = readLE r.mem1 (s.x11 + 8) 8
  | .p7 => f.2.mem = r.mem1 ∧ f.2.x28 = r.c0 ∧ f.2.x5 = readLE r.mem1 (s.x11 + 8) 8 ∧
      f.2.x6 = readLE r.mem1 (s.x12 + 8) 8
  | .p8 => f.2.mem = r.mem1 ∧ f.2.x28 = r.c0 ∧ f.2.x5 = readLE r.mem1 (s.x11 + 8) 8 ∧
      f.2.x7 = r.sum1
  | .p9 => f.2.mem = r.mem1 ∧ f.2.x28 = r.c0 ∧ f.2.x7 = r.sum1 ∧ f.2.x29 = r.c1
  | .p10 => f.2.mem = r.mem1 ∧ f.2.x28 = r.c0 ∧ f.2.x7 = r.hi ∧ f.2.x29 = r.c1
  | .p11 => f.2.mem = r.mem1 ∧ f.2.x7 = r.hi ∧ f.2.x29 = r.c1 ∧ f.2.x30 = r.c2
  | .p12 => f.2.mem = r.mem1 ∧ f.2.x7 = r.hi ∧ f.2.x29 = (r.c1 ||| r.c2)
  | .p13 => f.2.mem = r.mem2 ∧ f.2.x29 = (r.c1 ||| r.c2)
  | .p14 => f.2.mem = r.mem2 ∧ f.2.x10 = (r.c1 ||| r.c2)

/-- Close a memory instruction's VCs: unfold the premises to `Nat` facts, normalize the
platform guards, and let `omega` refute every non-RAM or misaligned branch. -/
macro "mem_vcs" : tactic => `(tactic| (
  all_goals simp only [addInv, AddPre, RamRegion, Sum.elim, AddPost, addResult, carryBit] at *
  all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
  all_goals omega))

set_option maxHeartbeats 1000000 in
private theorem add_block (s : RVState) (f : AddMem.Frame) :
    ⦃addInv s f⦄ AddMem.step f ⦃Sum.elim (addInv s) (AddPost s)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc
  case p0 => vcgen [AddMem.step]; mem_vcs
  case p1 => vcgen [AddMem.step]; mem_vcs
  case p4 => vcgen [AddMem.step]; mem_vcs
  case p5 => vcgen [AddMem.step]; mem_vcs
  case p6 => vcgen [AddMem.step]; mem_vcs
  case p12 => vcgen [AddMem.step]; mem_vcs
  all_goals vcgen [AddMem.step]
  all_goals simp only [addInv, Sum.elim, AddPost, ne_eq, reduceCtorEq, not_false_eq_true,
    forall_const, addResult, carryBit, zext_slt_zext] at *
  all_goals simp_all [ret_aligned]
  all_goals omega

theorem add_correct (s : RVState) : ⦃AddPre s⦄ AddMem.run s ⦃AddPost s⦄ := by
  constructor
  intro h
  exact (run_spec AddMem.step (AddMem.initial s) (addInv s) (AddPost s) (add_block s)).le_wp
    (by simp [addInv, AddMem.initial, h])

#print axioms add_correct

/-! ## `stack32`: a 32-byte reservation with one spill, and `reserve256`. -/

def StackPost (s : RVState) : Exit → Prop
  | .ret out => out.mem = writeLE s.mem (s.x2 - 32#64) 8 s.x10 ∧ out.x2 = s.x2 ∧
      out.pc = s.x1 &&& ~~~1 ∧ out.x1 = s.x1
  | .stuck _ => False

private def stackInv (s : RVState) (f : Stack32.Frame) : Prop :=
  f.2.x1 = s.x1 ∧ f.2.x10 = s.x10 ∧ RamRegion (s.x2 - 32#64) 1 ∧
  match f.1 with
  | .p0 => f.2.x2 = s.x2 ∧ f.2.mem = s.mem
  | .p1 => f.2.x2 = s.x2 - 32#64 ∧ f.2.mem = s.mem
  | .p2 => f.2.x2 = s.x2 - 32#64 ∧ f.2.mem = writeLE s.mem (s.x2 - 32#64) 8 s.x10
  | .p3 => f.2.x2 = s.x2 ∧ f.2.mem = writeLE s.mem (s.x2 - 32#64) 8 s.x10

private theorem stack_block (s : RVState) (f : Stack32.Frame) :
    ⦃stackInv s f⦄ Stack32.step f ⦃Sum.elim (stackInv s) (StackPost s)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc
  case p1 =>
    vcgen [Stack32.step]
    all_goals simp only [stackInv, RamRegion, Sum.elim] at *
    all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
    all_goals omega
  all_goals vcgen [Stack32.step]
  all_goals simp_all [stackInv, Sum.elim, StackPost, ret_aligned, BitVec.sub_add_cancel]

/-- The spill lands 32 bytes below the entry `sp`, which must be aligned RAM. -/
theorem stack_correct (s : RVState) :
    ⦃RamRegion (s.x2 - 32#64) 1⦄ Stack32.run s ⦃StackPost s⦄ := by
  constructor
  intro h
  exact (run_spec Stack32.step (Stack32.initial s) (stackInv s) (StackPost s)
    (stack_block s)).le_wp (by simp [stackInv, Stack32.initial, h])

/-- A large temporary reservation still satisfies the ordinary exit frame. -/
theorem reserve_correct (s : RVState) :
    ⦃True⦄ Reserve256.run s ⦃fun
      | .ret out => out.x2 = s.x2 ∧ out.mem = s.mem ∧ out.pc = s.x1 &&& ~~~1
      | .stuck _ => False⦄ := by
  constructor
  intro _
  apply finishes_run _ _ _ (n := 3)
  simp [finishes, Reserve256.step, Reserve256.initial, pure, Sum.elim, ret_aligned,
    BitVec.sub_add_cancel]

-- Entry/exit agreement alone cannot establish a stack high-water bound.
theorem reserve_depth :
    (match Reserve256.step (.p0, ({ x2 := 0x80008000 } : RVState)) with
     | .inl f => f.2.x2
     | .inr _ => 0) = 0x80007f00 := by decide

/-! ## Stack bounds at every instruction boundary (`pcode-lean/Examples/StackBounds.lean`). -/

def StackWithin (entry : BitVec 64) (bytes : Nat) (sp : BitVec 64) : Prop :=
  entry.toNat - bytes ≤ sp.toNat ∧ sp.toNat ≤ entry.toNat

private def position (entry : BitVec 64) (f : Stack32.Frame) : Prop :=
  f.2.x2 = match f.1 with
    | .p1 | .p2 => entry - 32
    | .p0 | .p3 => entry

def SpRestored (entry : BitVec 64) : Exit → Prop
  | .ret out => out.x2 = entry
  | .stuck out => out.x2 = entry ∨ out.x2 = entry - 32

/-- The spill's guard tree leaves `sp` alone on every path, including the stuck ones. -/
private theorem spill_keeps_sp (state : RVState) :
    ⦃True⦄ Stack32.step (.p1, state) ⦃Sum.elim (fun f ↦ f.1 = .p2 ∧ f.2.x2 = state.x2)
      (fun | .stuck out => out.x2 = state.x2 | .ret _ => False)⦄ := by
  vcgen [Stack32.step]
  all_goals simp [Sum.elim]

private theorem movement (s : RVState) :
    Always Stack32.step (Stack32.initial s) (position s.x2) (SpRestored s.x2) := by
  apply always_invariant _ _ (by rfl)
  intro ⟨pc, state⟩ h
  cases pc <;> simp only [position] at h
  case p1 =>
    have hs := (spill_keeps_sp state).le_wp trivial
    change Sum.elim _ _ (Stack32.step (.p1, state)) at hs
    revert hs
    cases Stack32.step (.p1, state) with
    | inl f => rcases f with ⟨pc, out⟩; cases pc <;> simp_all [Sum.elim, position]
    | inr e => cases e <;> simp_all [Sum.elim, SpRestored]
  all_goals simp_all [Stack32.step, pure, position, Sum.elim, SpRestored, BitVec.sub_add_cancel,
    ret_aligned]

/-- Every instruction boundary stays within 32 bytes below entry, and `sp` is restored on
return. A stuck exit (e.g. a non-RAM stack) stops at entry or 32 bytes below, within the bound. -/
theorem stack32 (s : RVState) (hs : 32 ≤ s.x2.toNat) :
    Always Stack32.step (Stack32.initial s)
      (fun f ↦ StackWithin s.x2 32 f.2.x2) (SpRestored s.x2) := by
  apply (movement s).mono ?_ (fun _ h ↦ h)
  intro ⟨pc, state⟩ h
  have ht : (s.x2 - 32).toNat = s.x2.toNat - 32 :=
    BitVec.toNat_sub_of_le (by change 32 ≤ s.x2.toNat; exact hs)
  cases pc <;> simp only [position] at h
  all_goals simp only [StackWithin, h, ht]; omega

/-- An actual 256-byte reservation violates a 32-byte bound immediately, despite its exit frame. -/
theorem reserve256_exceeds32 (s : RVState) (hs : 256 ≤ s.x2.toNat) :
    ¬Always Reserve256.step (Reserve256.initial s)
      (fun f ↦ StackWithin s.x2 32 f.2.x2) (fun _ ↦ True) := by
  intro h
  have first := (h 1).2
  change StackWithin s.x2 32 (s.x2 - 256) at first
  have ht : (s.x2 - 256).toNat = s.x2.toNat - 256 :=
    BitVec.toNat_sub_of_le (by change 256 ≤ s.x2.toNat; exact hs)
  simp only [StackWithin, ht] at first
  omega

#print axioms stack_correct
#print axioms reserve_correct
#print axioms stack32
#print axioms reserve256_exceeds32

end IslaExamples.WriteProof
