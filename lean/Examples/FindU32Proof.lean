import Examples.Generated.FindU32O2
import IslaLean.Cut
import IslaLean.Memory

/-! `find_u32` from `examples/c/challenges.c` at `-O2`, proved in cut-point style: the invariant
is stated only at entry and at the loop head, and `walk` executes everything in between.
Result: the first `i < n` with `a[i] = key`, or `n`, sign-extended as the psABI returns it. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples.FindU32Proof

def word (s : RVState) (j : Nat) : BitVec 32 := readLE s.mem (s.x10 + BitVec.ofNat 64 (4 * j)) 4
def count (s : RVState) : Nat := s.x11.toNat % 2 ^ 32
def key (s : RVState) : BitVec 32 := BitVec.extractLsb 31 0 s.x12

/-- `r` is the C result: no earlier match, and either a match at `r` or `r = n`. -/
def Found (s : RVState) (r : Nat) : Prop :=
  r ≤ count s ∧ (∀ j < r, word s j ≠ key s) ∧ (r < count s → word s r = key s)

def Pre (s : RVState) : Prop :=
  RamWords s.x10 4 (count s) ∧ Canonical32 s.x11 ∧ Canonical32 s.x12

def Post (s : RVState) : Exit → Prop
  | .ret out => (∃ r, Found s r ∧ out.x10 = (BitVec.ofNat 32 r).signExtend 64) ∧
      out.pc = s.x1 &&& ~~~1 ∧ out.x1 = s.x1 ∧ out.x2 = s.x2
  | .stuck _ => False

def cut (f : FindU32O2.Frame) : Bool := match f.1 with | .p0 | .p5 => true | _ => false

/-- Loop head: the cursor `a0` is at element `i`, `a5` holds `i`, and no earlier element
matched. `i` is read off the cursor, so the invariant has no existentials. -/
def I (s : RVState) (f : FindU32O2.Frame) : Prop :=
  f.2.x1 = s.x1 ∧ f.2.x2 = s.x2 ∧ f.2.mem = s.mem ∧ f.2.x11 = s.x11 ∧ f.2.x12 = s.x12 ∧
  Pre s ∧ match f.1 with
  | .p0 => f.2.x10 = s.x10
  | .p5 =>
    let i := (f.2.x10.toNat - s.x10.toNat) / 4
    s.x10.toNat ≤ f.2.x10.toNat ∧ (f.2.x10.toNat - s.x10.toNat) % 4 = 0 ∧ i < count s ∧
      f.2.x15 = (BitVec.ofNat 32 i).signExtend 64 ∧ ∀ j < i, word s j ≠ key s
  | _ => False

/-- Normalizes away the walked load's platform guards (non-RAM paths are contradictory). -/
macro "guards" : tactic => `(tactic|
  (simp only [I, Post, Pre, RamWords, count] at *; simp_all [BitVec.toNat_sub, BitVec.toNat_add] <;> omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem correct (s : RVState) (hp : Pre s) : ⦃True⦄ FindU32O2.run s ⦃Post s⦄ := by
  apply run_cuts _ cut (I s) _ _ _ (by simp [I, FindU32O2.initial, hp])
  intro ⟨pc, state⟩ h
  refine ⟨20, ?_⟩
  obtain ⟨h1, h2, hm, h11, h12, hpre, h⟩ := h
  have hpre' := hpre
  obtain ⟨⟨hb1, hb2, hb3⟩, hc11, hc12⟩ := hpre'
  cases pc <;> simp only at h
  case p0 =>
    walk FindU32O2.step, cut using guards
    all_goals simp only [I, Post, Found, word, key, count] at *
    all_goals simp_all
    all_goals first
      | exact ⟨0, ⟨rfl, by simp⟩, by simp⟩
      | (unfold Canonical32 at hc11
         have : s.x11.toNat ≠ 0 := fun h0 ↦ ‹¬s.x11 = 0#64› (BitVec.eq_of_toNat_eq (by simpa using h0))
         omega)
  case p5 =>
    obtain ⟨hle, hmod, hi, h15, hprev⟩ := h
    have hx := cursor_eq s.x10 state.x10 hle hmod
    have hlt := state.x10.isLt
    have hk := canonical_signExtend s.x12 hc12
    walk FindU32O2.step, cut using guards
    all_goals simp [I, Post, Found, word, key, count, h1, h2, hm, h11, h12, h15,
      BitVec.toNat_add] at *
    all_goals first
      | -- Element `i` matched: return `i`.
        (refine ⟨_, ⟨by omega, hprev, fun _ ↦ ?_⟩, rfl⟩
         rw [hx]; apply signExtend_inj; rw [hk]; assumption)
      | -- Not a match and more elements: continue at `i + 1`.
        (have hne : readLE s.mem state.x10 4 ≠ BitVec.extractLsb 31 0 s.x12 := fun e ↦
           ‹¬BitVec.signExtend 64 (readLE s.mem state.x10 4) = s.x12› (by rw [e, hk])
         have hmore : (state.x10.toNat - s.x10.toNat) / 4 + 1 ≠ s.x11.toNat % 2 ^ 32 := fun e ↦
           ‹¬s.x11 = BitVec.signExtend 64 (BitVec.ofNat 32 ((state.x10.toNat - s.x10.toNat) / 4) + 1#32)›
             (by rw [ofNat32_succ _ (by omega), e]; exact canonical_ofNat s.x11 hc11)
         refine ⟨hpre, by omega, by omega, by omega, ?_, fun j hj ↦ ?_⟩
         · rw [ofNat32_succ _ (by omega)]; congr 2; omega
         · rcases Nat.lt_or_ge j ((state.x10.toNat - s.x10.toNat) / 4) with hj' | hj'
           · exact hprev j hj'
           · rw [show j = (state.x10.toNat - s.x10.toNat) / 4 by omega, hx]; exact hne)
      | -- Not a match and the counter reached `n`: return `n`.
        (have hne : readLE s.mem state.x10 4 ≠ BitVec.extractLsb 31 0 s.x12 := fun e ↦
           ‹¬BitVec.signExtend 64 (readLE s.mem state.x10 4) = s.x12› (by rw [e, hk])
         have hn := canonical_ofNat s.x11 hc11
         have hlast :=
           ‹s.x11 = BitVec.signExtend 64 (BitVec.ofNat 32 ((state.x10.toNat - s.x10.toNat) / 4) + 1#32)›
         rw [ofNat32_succ _ (by omega), hn] at hlast
         have := signExtend_ofNat_inj (by omega) (by omega) hlast
         refine ⟨s.x11.toNat % 2 ^ 32, ⟨Nat.le_refl _, fun j hj ↦ ?_, fun h ↦ absurd h (Nat.lt_irrefl _)⟩, hn⟩
         rcases Nat.lt_or_ge j ((state.x10.toNat - s.x10.toNat) / 4) with hj' | hj'
         · exact hprev j hj'
         · rw [show j = (state.x10.toNat - s.x10.toNat) / 4 by omega, hx]; exact hne)

#print axioms correct

end IslaExamples.FindU32Proof
