import Examples.Generated.Scan
import IslaLean.Memory
import IslaLean.Rank

/-! `scan64` ORs `a0` limbs at `a1`, for every count, when the limbs are aligned and in RAM.
Mirrors `pcode-lean/Examples/ScanProofs.lean`. The RAM premise is new: for other addresses the
Sail model faults, splits the access, or reaches an MMIO device, all of which are `stuck`. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.ScanProof

def limbOr (mem : Memory) (base : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => readLE mem base 8 ||| limbOr mem (base + 8) n

def Post (s : RVState) : Exit → Prop
  | .ret out => out.x10 = limbOr s.mem s.x11 s.x10.toNat ∧ out.pc = s.x1 &&& ~~~1 ∧
      out.x1 = s.x1 ∧ out.x2 = s.x2 ∧ out.mem = s.mem
  | .stuck _ => False

private theorem limbOr_pos (mem : Memory) (base : BitVec 64) (n : Nat) (h : 0 < n) :
    limbOr mem base n = readLE mem base 8 ||| limbOr mem (base + 8) (n - 1) := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem sub_one (x : BitVec 64) (h : 0 < x.toNat) : (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub]; simp; omega

private theorem RamRegion.next (h : RamRegion p n) (hn : 0 < n) : RamRegion (p + 8#64) (n - 1) := by
  unfold RamRegion at *
  rw [BitVec.toNat_add]; simp
  omega

private def invariant (s : RVState) (f : Scan.Frame) : Prop :=
  f.2.mem = s.mem ∧ f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧
  let total := limbOr s.mem s.x11 s.x10.toNat
  match f.1 with
  | .p0 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ RamRegion s.x11 s.x10.toNat
  | .p1 => f.2.x5 = 0 ∧ f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ RamRegion s.x11 s.x10.toNat
  | .p2 => f.2.x5 ||| limbOr s.mem f.2.x11 f.2.x10.toNat = total ∧
      0 < f.2.x10.toNat ∧ RamRegion f.2.x11 f.2.x10.toNat
  | .p3 => f.2.x5 ||| limbOr s.mem f.2.x11 f.2.x10.toNat = total ∧
      0 < f.2.x10.toNat ∧ RamRegion f.2.x11 f.2.x10.toNat ∧ f.2.x6 = readLE s.mem f.2.x11 8
  | .p4 => f.2.x5 ||| limbOr s.mem (f.2.x11 + 8#64) (f.2.x10.toNat - 1) = total ∧
      0 < f.2.x10.toNat ∧ RamRegion f.2.x11 f.2.x10.toNat
  | .p5 => f.2.x5 ||| limbOr s.mem f.2.x11 (f.2.x10.toNat - 1) = total ∧
      0 < f.2.x10.toNat ∧ RamRegion f.2.x11 (f.2.x10.toNat - 1)
  | .p6 => f.2.x5 ||| limbOr s.mem f.2.x11 f.2.x10.toNat = total ∧
      RamRegion f.2.x11 f.2.x10.toNat
  | .p7 => f.2.x5 = total
  | .p8 => f.2.x10 = total

private theorem ret_aligned (x : BitVec 64) :
    BitVec.extractLsb 0 0 (x &&& 0xfffffffffffffffe#64) = 0#1 := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp

private theorem block (s : RVState) (f : Scan.Frame) :
    ⦃invariant s f⦄ Scan.step f ⦃Sum.elim (invariant s) (Post s)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc
  case p2 =>
    -- The load: every non-RAM or misaligned branch contradicts the region premise.
    vcgen [Scan.step]
    all_goals simp only [invariant, Sum.elim, RamRegion, Post] at *
    all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
    all_goals omega
  case p3 =>
    vcgen [Scan.step]
    simp only [invariant, Sum.elim] at *
    obtain ⟨hm, h1, h2, heq, hpos, hr, h6⟩ := ‹_›
    refine ⟨hm, h1, h2, ?_, hpos, hr⟩
    rw [limbOr_pos _ _ _ hpos, ← BitVec.or_assoc] at heq
    rw [h6]; exact heq
  case p4 =>
    vcgen [Scan.step]
    simp only [invariant, Sum.elim] at *
    obtain ⟨hm, h1, h2, heq, hpos, hr⟩ := ‹_›
    exact ⟨hm, h1, h2, heq, hpos, RamRegion.next hr hpos⟩
  case p5 =>
    vcgen [Scan.step]
    simp only [invariant, Sum.elim] at *
    obtain ⟨hm, h1, h2, heq, hpos, hr⟩ := ‹_›
    rw [sub_one _ hpos]
    exact ⟨hm, h1, h2, heq, hr⟩
  all_goals vcgen [Scan.step]
  all_goals simp_all [invariant, Sum.elim, Post, ret_aligned, limbOr]
  all_goals exact BitVec.toNat_pos_of_ne_zero ‹_›

theorem correct (s : RVState) :
    ⦃RamRegion s.x11 s.x10.toNat⦄ Scan.run s ⦃Post s⦄ := by
  constructor
  intro h
  exact (run_spec Scan.step (Scan.initial s) (invariant s) (Post s) (block s)).le_wp
    (by simp [invariant, Scan.initial, h])

#print axioms correct

private def rank (f : Scan.Frame) : Nat :=
  let n := f.2.x10.toNat
  match f.1 with
  | .p0 => 5 * n + 4
  | .p1 => 5 * n + 3
  | .p2 => 5 * n + 1
  | .p3 => 5 * n
  | .p4 => 5 * n - 1
  | .p5 => 5 * n - 2
  | .p6 => 5 * n + 2
  | .p7 => 1
  | .p8 => 0

private theorem decreases (s : RVState) (f : Scan.Frame) :
    ⦃invariant s f⦄ Scan.step f ⦃Sum.elim (fun f' ↦ rank f' < rank f) (fun _ ↦ True)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Scan.step]
  all_goals simp only [invariant, rank, Sum.elim, RamRegion] at *
  all_goals try simp_all [BitVec.toNat_sub, BitVec.toNat_add]
  all_goals try omega

/-- Completion within the rank bound, for every count; concrete fuel exhaustion is not success. -/
theorem terminates (s : RVState) (h : RamRegion s.x11 s.x10.toNat) :
    ∃ out, Scan.execute (5 * s.x10.toNat + 5) s = some out ∧ Post s out := by
  apply finishes_execute Scan.step (Scan.initial s)
  exact finishes_of_triples Scan.step (invariant s) rank (Post s) (block s) (decreases s)
    (Scan.initial s) (by simp [invariant, Scan.initial, h])

#print axioms terminates

end IslaExamples.ScanProof
