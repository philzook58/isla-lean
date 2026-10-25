import Examples.Generated.Fill
import IslaLean.Memory
import IslaLean.Rank

/-! `fill64` stores `a2` into `a1` limbs at `a0`, for every count, when the limbs are aligned
and in RAM. Mirrors pcode-lean's fill contract: the exact memory effect, return, and frame. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.FillProof

/-- The memory after storing `v` into `n` consecutive limbs from `p`. -/
def fillMem (mem : Memory) (p : BitVec 64) (v : BitVec 64) : Nat → Memory
  | 0 => mem
  | n + 1 => fillMem (writeLE mem p 8 v) (p + 8) v n

def Post (s : RVState) : Exit → Prop
  | .ret out => out.mem = fillMem s.mem s.x10 s.x12 s.x11.toNat ∧ out.pc = s.x1 &&& ~~~1 ∧
      out.x1 = s.x1 ∧ out.x2 = s.x2 ∧ out.x12 = s.x12
  | .stuck _ => False

private theorem fillMem_pos (mem : Memory) (p v : BitVec 64) (n : Nat) (h : 0 < n) :
    fillMem mem p v n = fillMem (writeLE mem p 8 v) (p + 8) v (n - 1) := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem sub_one (x : BitVec 64) (h : 0 < x.toNat) : (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub]; simp; omega

private theorem RamRegion.next (h : RamRegion p n) (hn : 0 < n) : RamRegion (p + 8#64) (n - 1) := by
  unfold RamRegion at *
  rw [BitVec.toNat_add]; simp
  omega

private theorem ret_aligned (x : BitVec 64) :
    BitVec.extractLsb 0 0 (x &&& 0xfffffffffffffffe#64) = 0#1 := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp

private def invariant (s : RVState) (f : Fill.Frame) : Prop :=
  f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧ f.2.x12 = s.x12 ∧
  let total := fillMem s.mem s.x10 s.x12 s.x11.toNat
  match f.1 with
  | .p0 => f.2.mem = s.mem ∧ f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ RamRegion s.x10 s.x11.toNat
  | .p1 => fillMem f.2.mem f.2.x10 s.x12 f.2.x11.toNat = total ∧ 0 < f.2.x11.toNat ∧
      RamRegion f.2.x10 f.2.x11.toNat
  | .p2 => fillMem f.2.mem (f.2.x10 + 8#64) s.x12 (f.2.x11.toNat - 1) = total ∧
      0 < f.2.x11.toNat ∧ RamRegion f.2.x10 f.2.x11.toNat
  | .p3 => fillMem f.2.mem f.2.x10 s.x12 (f.2.x11.toNat - 1) = total ∧ 0 < f.2.x11.toNat ∧
      RamRegion f.2.x10 (f.2.x11.toNat - 1)
  | .p4 => fillMem f.2.mem f.2.x10 s.x12 f.2.x11.toNat = total ∧ RamRegion f.2.x10 f.2.x11.toNat
  | .p5 => f.2.mem = total

private theorem block (s : RVState) (f : Fill.Frame) :
    ⦃invariant s f⦄ Fill.step f ⦃Sum.elim (invariant s) (Post s)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc
  case p1 =>
    -- The store: every non-RAM or misaligned branch contradicts the region premise.
    vcgen [Fill.step]
    all_goals simp only [invariant, Sum.elim, RamRegion, Post] at *
    all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
    all_goals first
      | omega
      | (obtain ⟨-, -, -, heq, hpos, -⟩ : _ ∧ _ ∧ _ ∧ fillMem _ _ _ _ = _ ∧ 0 < _ ∧ _ := by
           assumption
         rw [fillMem_pos _ _ _ _ hpos] at heq; exact heq)
  case p3 =>
    vcgen [Fill.step]
    simp only [invariant, Sum.elim] at *
    obtain ⟨h1, h2, h12, heq, hpos, hr⟩ := ‹_›
    rw [sub_one _ hpos]
    exact ⟨h1, h2, h12, heq, hr⟩
  case p2 =>
    vcgen [Fill.step]
    simp only [invariant, Sum.elim] at *
    obtain ⟨h1, h2, h12, heq, hpos, hr⟩ := ‹_›
    exact ⟨h1, h2, h12, heq, hpos, RamRegion.next hr hpos⟩
  all_goals vcgen [Fill.step]
  all_goals simp_all [invariant, Sum.elim, Post, ret_aligned, fillMem]
  all_goals exact BitVec.toNat_pos_of_ne_zero ‹_›

theorem correct (s : RVState) :
    ⦃RamRegion s.x10 s.x11.toNat⦄ Fill.run s ⦃Post s⦄ := by
  constructor
  intro h
  exact (run_spec Fill.step (Fill.initial s) (invariant s) (Post s) (block s)).le_wp
    (by simp [invariant, Fill.initial, h])

#print axioms correct

private def rank (f : Fill.Frame) : Nat :=
  let n := f.2.x11.toNat
  match f.1 with
  | .p0 => 4 * n + 1
  | .p1 => 4 * n
  | .p2 => 4 * n - 1
  | .p3 => 4 * n - 2
  | .p4 => 4 * n + 1
  | .p5 => 0

private theorem decreases (s : RVState) (f : Fill.Frame) :
    ⦃invariant s f⦄ Fill.step f ⦃Sum.elim (fun f' ↦ rank f' < rank f) (fun _ ↦ True)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Fill.step]
  all_goals simp only [invariant, rank, Sum.elim, RamRegion] at *
  all_goals try simp_all [BitVec.toNat_sub, BitVec.toNat_add]
  all_goals try omega

/-- Completion within the rank bound, for every count; concrete fuel exhaustion is not success. -/
theorem terminates (s : RVState) (h : RamRegion s.x10 s.x11.toNat) :
    ∃ out, Fill.execute (4 * s.x11.toNat + 2) s = some out ∧ Post s out := by
  apply finishes_execute Fill.step (Fill.initial s)
  exact finishes_of_triples Fill.step (invariant s) rank (Post s) (block s) (decreases s)
    (Fill.initial s) (by simp [invariant, Fill.initial, h])

#print axioms terminates

end IslaExamples.FillProof
