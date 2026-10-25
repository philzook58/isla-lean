import Examples.Generated.SumU32O2
import IslaLean.Memory
import IslaLean.Rank

/-! `sum_u32` from `examples/c/challenges.c`, compiled by GCC at `-O2` and linked, proved against
its C meaning: the sum of `n` 32-bit words modulo 2^32, returned sign-extended in `a0`.

The compiled loop runs from `a0` to `a0 + 4 * (a1 mod 2^32)`, but tests `a1 = 0` on all 64 bits.
It is therefore correct only for ABI-canonical arguments: the RISC-V psABI passes a `uint32_t`
sign-extended, which `Canonical32` states. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.SumU32Proof

def wordSum (mem : Memory) (p : BitVec 64) : Nat → BitVec 32
  | 0 => 0
  | k + 1 => readLE mem p 4 + wordSum mem (p + 4) k

def count (s : RVState) : Nat := s.x11.toNat % 2 ^ 32

def Post (s : RVState) : Exit → Prop
  | .ret out => out.x10 = (wordSum s.mem s.x10 (count s)).signExtend 64 ∧
      out.pc = s.x1 &&& ~~~1 ∧ out.x1 = s.x1 ∧ out.x2 = s.x2 ∧ out.mem = s.mem
  | .stuck _ => False

def Pre (s : RVState) : Prop := RamWords s.x10 4 (count s) ∧ Canonical32 s.x11

private theorem wordSum_pos (mem : Memory) (p : BitVec 64) (k : Nat) (h : 0 < k) :
    wordSum mem p k = readLE mem p 4 + wordSum mem (p + 4) (k - 1) := by
  cases k with
  | zero => omega
  | succ k => rfl

def acc (f : SumU32O2.Frame) : BitVec 32 := BitVec.extractLsb 31 0 f.2.x10

def rem (f : SumU32O2.Frame) : Nat := (f.2.x11.toNat - f.2.x15.toNat) / 4

private def invariant (s : RVState) (f : SumU32O2.Frame) : Prop :=
  f.2.mem = s.mem ∧ f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧ Pre s ∧
  let n := count s
  let base := s.x10.toNat
  let total := wordSum s.mem s.x10 n
  let x15 := f.2.x15.toNat
  match f.1 with
  | .p0 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11
  | .p1 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ 0 < n
  | .p2 => f.2.x10 = s.x10 ∧ f.2.x14.toNat = n * 2 ^ 32 ∧ 0 < n
  | .p3 => f.2.x10 = s.x10 ∧ f.2.x11.toNat = 4 * n ∧ 0 < n
  | .p4 => f.2.x10 = s.x10 ∧ f.2.x15 = s.x10 ∧ f.2.x11.toNat = 4 * n ∧ 0 < n
  | .p5 => f.2.x15 = s.x10 ∧ f.2.x11.toNat = base + 4 * n ∧ 0 < n
  | .p6 => f.2.x11.toNat = base + 4 * n ∧ base ≤ x15 ∧ x15 < f.2.x11.toNat ∧
      (x15 - base) % 4 = 0 ∧ (acc f).signExtend 64 = f.2.x10 ∧
      acc f + wordSum s.mem f.2.x15 (rem f) = total
  | .p7 => f.2.x11.toNat = base + 4 * n ∧ base ≤ x15 ∧ x15 < f.2.x11.toNat ∧
      (x15 - base) % 4 = 0 ∧ (acc f).signExtend 64 = f.2.x10 ∧
      f.2.x14 = (readLE s.mem f.2.x15 4).signExtend 64 ∧
      acc f + wordSum s.mem f.2.x15 (rem f) = total
  | .p8 => f.2.x11.toNat = base + 4 * n ∧ base + 4 ≤ x15 ∧ x15 ≤ f.2.x11.toNat ∧
      (x15 - base) % 4 = 0 ∧ (acc f).signExtend 64 = f.2.x10 ∧
      f.2.x14 = (readLE s.mem (f.2.x15 - 4) 4).signExtend 64 ∧
      acc f + wordSum s.mem (f.2.x15 - 4) (rem f + 1) = total
  | .p9 => f.2.x11.toNat = base + 4 * n ∧ base + 4 ≤ x15 ∧ x15 ≤ f.2.x11.toNat ∧
      (x15 - base) % 4 = 0 ∧ (acc f).signExtend 64 = f.2.x10 ∧
      acc f + wordSum s.mem f.2.x15 (rem f) = total
  | .p10 => f.2.x10 = total.signExtend 64
  | .p11 => n = 0
  | .p12 => n = 0 ∧ f.2.x10 = 0

set_option maxHeartbeats 800000 in
private theorem block (s : RVState) (f : SumU32O2.Frame) :
    ⦃invariant s f⦄ SumU32O2.step f ⦃Sum.elim (invariant s) (Post s)⦄ := by
  rcases f with ⟨pc, state⟩
  have hx := s.x10.isLt
  have hn := s.x11.isLt
  have h15 := state.x15.isLt
  cases pc
  case p6 =>
    -- The load: every non-RAM or misaligned branch contradicts the region premise.
    vcgen [SumU32O2.step]
    all_goals simp only [invariant, Sum.elim, Pre, RamWords, count, Post, acc, rem] at *
    all_goals simp_all [BitVec.toNat_sub, BitVec.toNat_add]
    all_goals first
      | omega
      | (obtain ⟨-, -, -, -, h11, -, hhi, -, -, hsum⟩ := ‹state.mem = s.mem ∧ _›
         rw [h11] at hhi hsum
         exact ⟨hhi, hsum⟩)
  case p7 =>
    vcgen [SumU32O2.step]
    simp only [invariant, Sum.elim, count, Pre, RamWords, acc, rem] at *
    obtain ⟨hm, h1, h2, hp, h11, hlo, hhi, hmod, h10, h14, hsum⟩ := ‹_›
    have hadd : (state.x15 + 4#64).toNat = state.x15.toNat + 4 := by
      rw [BitVec.toNat_add]; simp; omega
    have hr : (state.x11.toNat - (state.x15 + 4#64).toNat) / 4 + 1 =
        (state.x11.toNat - state.x15.toNat) / 4 := by omega
    have e : state.x15 + 4#64 - 4 = state.x15 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, hadd]; omega
    refine ⟨hm, h1, h2, hp, h11, by omega, by omega, by omega, h10, ?_, ?_⟩
    · rw [e]; exact h14
    · rw [hr, e]; exact hsum
  case p8 =>
    vcgen [SumU32O2.step]
    simp only [invariant, Sum.elim, count, Pre, RamWords, acc, rem] at *
    obtain ⟨hm, h1, h2, hp, h11, hlo, hhi, hmod, h10, h14, hsum⟩ := ‹_›
    refine ⟨hm, h1, h2, hp, h11, hlo, hhi, hmod, by simp, ?_⟩
    rw [wordSum_pos _ _ _ (by omega), BitVec.sub_add_cancel] at hsum
    rw [h14, ← h10, low_signExtend, low_signExtend, low_signExtend, ← hsum]
    simp only [Nat.add_sub_cancel]
    ac_rfl
  case p9 =>
    vcgen [SumU32O2.step]
    all_goals simp only [invariant, Sum.elim, count, acc, rem] at *
    · obtain ⟨hm, h1, h2, hp, h11, hlo, hhi, hmod, h10, hsum⟩ := ‹state.mem = s.mem ∧ _›
      have hne : state.x15.toNat ≠ state.x11.toNat := by
        intro h; simp_all [BitVec.eq_of_toNat_eq h]
      exact ⟨hm, h1, h2, hp, h11, by omega, by omega, hmod, h10, hsum⟩
    · obtain ⟨hm, h1, h2, hp, h11, hlo, hhi, hmod, h10, hsum⟩ := ‹state.mem = s.mem ∧ _›
      have heq : state.x15 = state.x11 := by simpa using ‹¬(!state.x15 == state.x11) = true›
      rw [heq, Nat.sub_self, Nat.zero_div] at hsum
      simp only [wordSum] at hsum
      exact ⟨hm, h1, h2, hp, by rw [← h10]; congr 1; simpa using hsum⟩
  all_goals vcgen [SumU32O2.step]
  all_goals simp only [invariant, Sum.elim, Post, count, Pre, RamWords, Canonical32, acc, rem] at *
  all_goals simp_all [ret_aligned, wordSum, eq_zero_iff_toNat, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
  all_goals omega

/-- For every array of `n` words in RAM and every ABI-canonical `n`. -/
theorem correct (s : RVState) : ⦃Pre s⦄ SumU32O2.run s ⦃Post s⦄ := by
  constructor
  intro h
  exact (run_spec SumU32O2.step (SumU32O2.initial s) (invariant s) (Post s) (block s)).le_wp
    (by simp [invariant, SumU32O2.initial, h])

#print axioms correct

end IslaExamples.SumU32Proof
