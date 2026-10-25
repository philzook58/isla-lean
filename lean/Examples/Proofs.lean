import Examples.Generated.Increment
import Examples.Generated.Maximum
import Examples.Generated.Count
import IslaLean.Rank
import IslaLean.Memory

/-! Contracts for the RISC-V ports of pcode-lean's first examples, over Lean emitted from Isla
footprints of the Sail model. The proof shape follows `pcode-lean/Examples/Proofs.lean`. -/
open IslaLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace IslaExamples

def Returns (before : RVState) (result : BitVec 64) : Exit → Prop
  | .ret after => after.x10 = result ∧ after.pc = before.x1 &&& ~~~1 ∧
      after.x1 = before.x1 ∧ after.x2 = before.x2
  | .stuck _ => False

private def frame (before after : RVState) : Prop :=
  after.x1 = before.x1 ∧ after.x2 = before.x2

namespace IncrementProof

private def invariant (s : RVState) (f : Increment.Frame) : Prop :=
  frame s f.2 ∧ match f.1 with
    | .p0 => f.2.x10 = s.x10
    | .p1 => f.2.x10 = s.x10 + 1

private theorem block (s : RVState) (f : Increment.Frame) :
    ⦃invariant s f⦄ Increment.step f ⦃Sum.elim (invariant s) (Returns s (s.x10 + 1))⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Increment.step]
  all_goals simp_all [invariant, frame, Returns, Sum.elim, ret_aligned]

theorem correct (s : RVState) :
    ⦃True⦄ Increment.run s ⦃Returns s (s.x10 + 1)⦄ := by
  constructor
  intro _
  exact (run_spec Increment.step (Increment.initial s) (invariant s) _ (block s)).le_wp
    (by simp [invariant, frame, Increment.initial])

end IncrementProof

namespace MaximumProof

def result (s : RVState) : BitVec 64 := if s.x10.toNat < s.x11.toNat then s.x11 else s.x10

private def invariant (s : RVState) (f : Maximum.Frame) : Prop :=
  frame s f.2 ∧ f.2.x11 = s.x11 ∧ match f.1 with
    | .p0 => f.2.x10 = s.x10
    | .p1 => s.x10.toNat < s.x11.toNat
    | .p2 => f.2.x10 = result s

private theorem block (s : RVState) (f : Maximum.Frame) :
    ⦃invariant s f⦄ Maximum.step f ⦃Sum.elim (invariant s) (Returns s (result s))⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Maximum.step]
  all_goals simp_all [invariant, frame, Returns, Sum.elim, result]
  all_goals omega

theorem correct (s : RVState) :
    ⦃True⦄ Maximum.run s ⦃Returns s (result s)⦄ := by
  constructor
  intro _
  exact (run_spec Maximum.step (Maximum.initial s) (invariant s) _ (block s)).le_wp
    (by simp [invariant, frame, Maximum.initial])

end MaximumProof

namespace CountProof

private theorem inc_sum (a b n : BitVec 64) (h : a + b = n) : a + 1 + b = n + 1 := by
  rw [BitVec.add_assoc, BitVec.add_comm (1 : BitVec 64) b, ← BitVec.add_assoc, h]

private theorem dec_sum (a b n : BitVec 64) (h : a + b = n + 1) : a + (b - 1) = n := by
  calc
    a + (b - 1) = (a + b) - 1 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    _ = (n + 1) - 1 := congrArg (· - 1) h
    _ = n := BitVec.add_sub_cancel n 1

private def invariant (s : RVState) (f : Count.Frame) : Prop :=
  frame s f.2 ∧ match f.1 with
    | .p0 => f.2.x10 = s.x10
    | .p1 => f.2.x5 = 0 ∧ f.2.x10 = s.x10
    | .p2 => f.2.x5 + f.2.x10 = s.x10 ∧ f.2.x10 ≠ 0
    | .p3 => f.2.x5 + f.2.x10 = s.x10 + 1 ∧ f.2.x10 ≠ 0
    | .p4 => f.2.x5 + f.2.x10 = s.x10
    | .p5 => f.2.x5 = s.x10
    | .p6 => f.2.x10 = s.x10

private theorem block (s : RVState) (f : Count.Frame) :
    ⦃invariant s f⦄ Count.step f ⦃Sum.elim (invariant s) (Returns s s.x10)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Count.step]
  all_goals simp_all [invariant, frame, Returns, Sum.elim, ret_aligned]
  all_goals rename_i h
  · exact inc_sum _ _ _ h.2.1
  · exact dec_sum _ _ _ h.2.1

/-- The loop returns its original input for every 64-bit count, without an unwinding bound. -/
theorem correct (s : RVState) : ⦃True⦄ Count.run s ⦃Returns s s.x10⦄ := by
  constructor
  intro _
  exact (run_spec Count.step (Count.initial s) (invariant s) _ (block s)).le_wp
    (by simp [invariant, frame, Count.initial])

private def rank (f : Count.Frame) : Nat :=
  let n := f.2.x10.toNat
  match f.1 with
  | .p0 => 3 * n + 3
  | .p1 => 3 * n + 2
  | .p2 => 3 * n + 1
  | .p3 => 3 * n
  | .p4 => 3 * n + 2
  | .p5 => 1
  | .p6 => 0

private theorem decreases (s : RVState) (f : Count.Frame) :
    ⦃invariant s f⦄ Count.step f ⦃Sum.elim (fun f' ↦ rank f' < rank f) (fun _ ↦ True)⦄ := by
  rcases f with ⟨pc, state⟩
  have hn : ∀ x : BitVec 64, x ≠ 0 → 0 < x.toNat := fun x h ↦ BitVec.toNat_pos_of_ne_zero h
  cases pc <;> vcgen [Count.step]
  all_goals simp only [invariant, rank, Sum.elim] at *
  all_goals try simp_all [BitVec.toNat_sub]
  all_goals try omega
  all_goals
    rename_i h
    obtain ⟨-, -, hne⟩ := h
    have := hn _ hne
    have := state.x10.isLt
    omega

/-- Completion within `3 * a0 + 4` steps, for every 64-bit count. -/
theorem terminates (s : RVState) :
    ∃ out, Count.execute (3 * s.x10.toNat + 4) s = some out ∧ Returns s s.x10 out := by
  apply finishes_execute Count.step (Count.initial s)
  exact finishes_of_triples Count.step (invariant s) rank (Returns s s.x10) (block s)
    (decreases s) (Count.initial s) (by simp [invariant, frame, Count.initial])

end CountProof

theorem IncrementProof.terminates (s : RVState) :
    ∃ out, Increment.execute 2 s = some out ∧ Returns s (s.x10 + 1) out := by
  apply finishes_execute Increment.step (Increment.initial s)
  simp [finishes, Increment.step, Increment.initial, Returns, Sum.elim, pure, ret_aligned]

theorem MaximumProof.terminates (s : RVState) :
    ∃ out, Maximum.execute 3 s = some out ∧ Returns s (MaximumProof.result s) out := by
  apply finishes_execute Maximum.step (Maximum.initial s)
  simp [finishes, Maximum.step, Maximum.initial, Returns, Sum.elim, pure, ret_aligned,
    MaximumProof.result]
  split <;> split <;> simp_all <;> omega

/-! Concrete runs of the same generated step functions. -/
def returned : Option Exit → Option (BitVec 64 × BitVec 64)
  | some (.ret a) => some (a.x10, a.pc)
  | _ => none

example : returned (Increment.execute 2 { x10 := 41, x1 := 0x4001 }) = some (42, 0x4000) := by
  decide
example : returned (Maximum.execute 3 { x10 := 3, x11 := 0xffffffffffffffff, x1 := 0x4000 }) =
    some (0xffffffffffffffff, 0x4000) := by decide
example : returned (Count.execute 200 { x10 := 37, x1 := 0x4000 }) = some (37, 0x4000) := by
  decide

#print axioms IncrementProof.correct
#print axioms MaximumProof.correct
#print axioms CountProof.correct
#print axioms CountProof.terminates
#print axioms IncrementProof.terminates
#print axioms MaximumProof.terminates

end IslaExamples
