import Examples.Generated.Add128
import IslaLean.Memory

/-! `add128` adds `(a1:a0)` and `(a3:a2)`, returning the 129-bit sum in `(a2:a1:a0)`.
Mirrors `pcode-lean/Examples/Add128Proofs.lean`; RISC-V has no carry flag, so the carry is
computed with `sltu` and returned in `a2`. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.Add128Proof

def Post (s : RVState) : Exit → Prop
  | .ret out =>
      out.x10.toNat + 2 ^ 64 * out.x11.toNat + 2 ^ 128 * out.x12.toNat =
        s.x10.toNat + 2 ^ 64 * s.x11.toNat + s.x12.toNat + 2 ^ 64 * s.x13.toNat ∧
      out.pc = s.x1 &&& ~~~1 ∧ out.x1 = s.x1 ∧ out.x2 = s.x2 ∧ out.mem = s.mem
  | .stuck _ => False

private theorem or_bits (x y : BitVec 64) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ||| y).toNat = max x.toNat y.toNat := by
  rw [BitVec.toNat_or]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with h' | h' <;> simp [h, h']

private def invariant (s : RVState) (f : Add128.Frame) : Prop :=
  f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧ f.2.mem = s.mem ∧
  let a := s.x10.toNat; let b := s.x11.toNat; let c := s.x12.toNat; let d := s.x13.toNat
  let lo := (a + c) % 2 ^ 64; let carry := (a + c) / 2 ^ 64
  match f.1 with
  | .p0 => f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.x12 = s.x12 ∧ f.2.x13 = s.x13
  | .p1 => f.2.x5.toNat = lo ∧ f.2.x10 = s.x10 ∧ f.2.x11 = s.x11 ∧ f.2.x13 = s.x13
  | .p2 => f.2.x5.toNat = lo ∧ f.2.x6.toNat = carry ∧ f.2.x11 = s.x11 ∧ f.2.x13 = s.x13
  | .p3 => f.2.x5.toNat = lo ∧ f.2.x6.toNat = carry ∧ f.2.x11.toNat = (b + d) % 2 ^ 64 ∧
      f.2.x13 = s.x13
  | .p4 => f.2.x5.toNat = lo ∧ f.2.x6.toNat = carry ∧ f.2.x11.toNat = (b + d) % 2 ^ 64 ∧
      f.2.x7.toNat = (b + d) / 2 ^ 64
  | .p5 => f.2.x5.toNat = lo ∧ f.2.x6.toNat = carry ∧
      f.2.x11.toNat = (b + d + carry) % 2 ^ 64 ∧ f.2.x7.toNat = (b + d) / 2 ^ 64
  | .p6 => f.2.x5.toNat = lo ∧ f.2.x11.toNat = (b + d + carry) % 2 ^ 64 ∧
      f.2.x7.toNat = (b + d) / 2 ^ 64 ∧ f.2.x28.toNat = ((b + d) % 2 ^ 64 + carry) / 2 ^ 64
  | .p7 => f.2.x5.toNat = lo ∧ f.2.x11.toNat = (b + d + carry) % 2 ^ 64 ∧
      f.2.x12.toNat = (b + d + carry) / 2 ^ 64
  | .p8 => f.2.x10.toNat = lo ∧ f.2.x11.toNat = (b + d + carry) % 2 ^ 64 ∧
      f.2.x12.toNat = (b + d + carry) / 2 ^ 64

private theorem block (s : RVState) (f : Add128.Frame) :
    ⦃invariant s f⦄ Add128.step f ⦃Sum.elim (invariant s) (Post s)⦄ := by
  rcases f with ⟨pc, state⟩
  have ha := s.x10.isLt; have hb := s.x11.isLt; have hc := s.x12.isLt; have hd := s.x13.isLt
  cases pc
  case p6 =>
    vcgen [Add128.step]
    simp only [invariant, Sum.elim] at *
    obtain ⟨h1, h2, hm, h5, h11, h7, h28⟩ := ‹_›
    refine ⟨h1, h2, hm, h5, h11, ?_⟩
    rw [or_bits _ _ (by omega) (by omega), h7, h28]
    omega
  all_goals vcgen [Add128.step]
  all_goals simp only [invariant, Sum.elim, Post] at *
  all_goals simp_all [BitVec.toNat_add, ret_aligned]
  all_goals omega

theorem correct (s : RVState) : ⦃True⦄ Add128.run s ⦃Post s⦄ := by
  constructor
  intro _
  exact (run_spec Add128.step (Add128.initial s) (invariant s) (Post s) (block s)).le_wp
    (by simp [invariant, Add128.initial])

#print axioms correct

end IslaExamples.Add128Proof
