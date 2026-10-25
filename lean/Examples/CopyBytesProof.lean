import Examples.Generated.CopyBytesO2
import IslaLean.Memory

/-! `copy_bytes` from `examples/c/challenges.c`, compiled by GCC at `-O2` and linked, proved
against the C loop's own meaning: `dst[i] = src[i]` for `i < n`, each read seeing earlier writes.
That is the machine order, so overlapping buffers are covered too (no `restrict` premise).
As for `sum_u32`, the count must be ABI-canonical (`uint32_t` passed sign-extended). -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.CopyBytesProof

def copyMem (mem : Memory) (dst src : BitVec 64) : Nat → Memory
  | 0 => mem
  | k + 1 => copyMem (writeLE mem dst 1 (readLE mem src 1)) (dst + 1) (src + 1) k

def count (s : RVState) : Nat := s.x12.toNat % 2 ^ 32

def Pre (s : RVState) : Prop :=
  RamWords s.x10 1 (count s) ∧ RamWords s.x11 1 (count s) ∧ Canonical32 s.x12

def Post (s : RVState) : Exit → Prop
  | .ret out => out.mem = copyMem s.mem s.x10 s.x11 (count s) ∧ out.x10 = s.x12 ∧
      out.pc = s.x1 &&& ~~~1 ∧ out.x1 = s.x1 ∧ out.x2 = s.x2
  | .stuck _ => False

private theorem copyMem_pos (mem : Memory) (d s : BitVec 64) (k : Nat) (h : 0 < k) :
    copyMem mem d s k = copyMem (writeLE mem d 1 (readLE mem s 1)) (d + 1) (s + 1) (k - 1) := by
  cases k with
  | zero => omega
  | succ k => rfl

def rem (f : CopyBytesO2.Frame) : Nat := f.2.x14.toNat - f.2.x11.toNat

private def invariant (s : RVState) (f : CopyBytesO2.Frame) : Prop :=
  f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧ f.2.x12 = s.x12 ∧ Pre s ∧
  let n := count s
  let dst := s.x10.toNat
  let src := s.x11.toNat
  let total := copyMem s.mem s.x10 s.x11 n
  let a1 := f.2.x11.toNat
  match f.1 with
  | .p0 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.mem = s.mem
  | .p1 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.mem = s.mem ∧ 0 < n
  | .p2 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.mem = s.mem ∧ 0 < n ∧
      f.2.x14.toNat = n * 2 ^ 32
  | .p3 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.mem = s.mem ∧ 0 < n ∧ f.2.x14.toNat = n
  | .p4 => f.2.x14.toNat = src + n ∧ src ≤ a1 ∧ a1 < f.2.x14.toNat ∧
      f.2.x10.toNat = dst + (a1 - src) ∧ copyMem f.2.mem f.2.x10 f.2.x11 (rem f) = total
  | .p5 => f.2.x14.toNat = src + n ∧ src ≤ a1 ∧ a1 < f.2.x14.toNat ∧
      f.2.x10.toNat = dst + (a1 - src) ∧ copyMem f.2.mem f.2.x10 f.2.x11 (rem f) = total ∧
      f.2.x15 = (readLE f.2.mem f.2.x11 1).setWidth 64
  | .p6 => f.2.x14.toNat = src + n ∧ src + 1 ≤ a1 ∧ a1 ≤ f.2.x14.toNat ∧
      f.2.x10.toNat + 1 = dst + (a1 - src) ∧
      copyMem f.2.mem f.2.x10 (f.2.x11 - 1) (rem f + 1) = total ∧
      f.2.x15 = (readLE f.2.mem (f.2.x11 - 1) 1).setWidth 64
  | .p7 => f.2.x14.toNat = src + n ∧ src + 1 ≤ a1 ∧ a1 ≤ f.2.x14.toNat ∧
      f.2.x10.toNat = dst + (a1 - src) ∧
      copyMem f.2.mem (f.2.x10 - 1) (f.2.x11 - 1) (rem f + 1) = total ∧
      f.2.x15 = (readLE f.2.mem (f.2.x11 - 1) 1).setWidth 64
  | .p8 => f.2.x14.toNat = src + n ∧ src + 1 ≤ a1 ∧ a1 ≤ f.2.x14.toNat ∧
      f.2.x10.toNat = dst + (a1 - src) ∧ copyMem f.2.mem f.2.x10 f.2.x11 (rem f) = total
  | .p9 => f.2.mem = total
  | .p10 => f.2.mem = total ∧ f.2.x10 = s.x12

set_option maxHeartbeats 800000 in
private theorem block (s : RVState) (f : CopyBytesO2.Frame) :
    ⦃invariant s f⦄ CopyBytesO2.step f ⦃Sum.elim (invariant s) (Post s)⦄ := by
  rcases f with ⟨pc, state⟩
  have hd := s.x10.isLt
  have hs := s.x11.isLt
  have hn := s.x12.isLt
  have h10 := state.x10.isLt
  have h11 := state.x11.isLt
  cases pc
  case p4 =>
    -- The byte load: every non-RAM branch contradicts the region premise.
    vcgen [CopyBytesO2.step]
    all_goals simp only [invariant, Sum.elim, Pre, RamWords, count, Post, rem] at *
    all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
    all_goals first
      | omega
      | (obtain ⟨-, -, -, -, h14, hlo, hhi, hdst, hcopy⟩ := ‹state.x1 = s.x1 ∧ _›
         rw [h14] at hhi hcopy
         exact ⟨hhi, hcopy⟩)
  case p7 =>
    -- The byte store at `a0 - 1`.
    vcgen [CopyBytesO2.step]
    all_goals simp only [invariant, Sum.elim, Pre, RamWords, count, Post, rem] at *
    all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
    all_goals first
      | omega
      | (obtain ⟨-, -, -, -, h14, hlo, hhi, hdst, hcopy, h15⟩ := ‹state.x1 = s.x1 ∧ _›
         rw [copyMem_pos _ _ _ _ (by omega)] at hcopy
         simp only [sub1_add1, Nat.add_sub_cancel] at hcopy
         rw [h14] at hhi hcopy
         exact ⟨hhi, hcopy⟩)
  case p5 =>
    vcgen [CopyBytesO2.step]
    simp only [invariant, Sum.elim, rem] at *
    obtain ⟨h1, h2, h12, hp, h14, hlo, hhi, hdst, hcopy, h15⟩ := ‹_›
    have hadd : (state.x11 + 1#64).toNat = state.x11.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    have e : state.x11 + 1#64 - 1 = state.x11 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, hadd]; omega
    refine ⟨h1, h2, h12, hp, h14, by omega, by omega, by omega, ?_, ?_⟩
    · rw [e, show state.x14.toNat - (state.x11 + 1#64).toNat + 1 =
        state.x14.toNat - state.x11.toNat by omega]; exact hcopy
    · rw [e]; exact h15
  case p6 =>
    vcgen [CopyBytesO2.step]
    simp only [invariant, Sum.elim, rem] at *
    obtain ⟨h1, h2, h12, hp, h14, hlo, hhi, hdst, hcopy, h15⟩ := ‹_›
    have hadd : (state.x10 + 1#64).toNat = state.x10.toNat + 1 := by
      rw [BitVec.toNat_add]; simp
      have hp' := hp
      simp only [Pre, RamWords, count] at hp' h14; omega
    exact ⟨h1, h2, h12, hp, h14, hlo, hhi, by omega, by rw [add1_sub1]; exact hcopy, h15⟩
  case p8 =>
    vcgen [CopyBytesO2.step]
    all_goals simp only [invariant, Sum.elim, rem] at *
    · obtain ⟨h1, h2, h12, hp, h14, hlo, hhi, hdst, hcopy⟩ := ‹state.x1 = s.x1 ∧ _›
      have hne : state.x11.toNat ≠ state.x14.toNat := by
        intro h; simp_all [BitVec.eq_of_toNat_eq h]
      exact ⟨h1, h2, h12, hp, h14, by omega, by omega, hdst, hcopy⟩
    · obtain ⟨h1, h2, h12, hp, h14, hlo, hhi, hdst, hcopy⟩ := ‹state.x1 = s.x1 ∧ _›
      have heq : state.x11 = state.x14 := by simpa using ‹¬(!state.x11 == state.x14) = true›
      rw [heq, Nat.sub_self] at hcopy
      exact ⟨h1, h2, h12, hp, hcopy⟩
  all_goals vcgen [CopyBytesO2.step]
  all_goals simp only [invariant, Sum.elim, Post, count, Pre, RamWords, Canonical32, rem] at *
  all_goals simp_all [ret_aligned, copyMem, eq_zero_iff_toNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
  all_goals first
    | omega
    | (refine ⟨by omega, by omega, ?_⟩; congr 1; omega)

/-- For every count and all byte buffers in RAM, overlapping or not. -/
theorem correct (s : RVState) : ⦃Pre s⦄ CopyBytesO2.run s ⦃Post s⦄ := by
  constructor
  intro h
  exact (run_spec CopyBytesO2.step (CopyBytesO2.initial s) (invariant s) (Post s)
    (block s)).le_wp (by simp [invariant, CopyBytesO2.initial, h])

#print axioms correct

end IslaExamples.CopyBytesProof
