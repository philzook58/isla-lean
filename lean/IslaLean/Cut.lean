import IslaLean.Run

/-! Cut-point proofs: state an invariant `I` only at cut points (entry, loop heads) and let
`vcgen` execute the straight-line code between them. `run_spec` needs an invariant at every
instruction; here non-cut instructions get theirs implicitly, as "the rest of the segment".

`seg step cut I Q n s`: within `n` steps from `s`, every path reaches a cut state satisfying `I`
or exits satisfying `Q`. `seg_succ` restates one step as a Hoare triple so `vcgen` can do it, and
the `walk` tactic repeats that until only cut-point and exit goals remain. -/
namespace IslaLean
open Std.WP Lean.Order

def seg (step : Step σ α) (cut : σ → Bool) (I : σ → Prop) (Q : α → Prop) : Nat → σ → Prop
  | 0, _ => False
  | n + 1, s => Sum.elim (fun s' ↦ if cut s' then I s' else seg step cut I Q n s') Q (step s)

theorem seg_succ (step : Step σ α) (cut : σ → Bool) (I : σ → Prop) (Q : α → Prop) (s : σ)
    (h : ⦃True⦄ step s ⦃Sum.elim (fun s' ↦ if cut s' then I s' else seg step cut I Q n s') Q⦄) :
    seg step cut I Q (n + 1) s := h.le_wp trivial

/-- An invariant at cut points, and a bounded segment from each, prove the whole run. -/
theorem run_cuts (step : Step σ α) (cut : σ → Bool) (I : σ → Prop) (Q : α → Prop)
    (segments : ∀ s, I s → ∃ n, seg step cut I Q n s) (initial : σ) (hi : I initial) :
    ⦃True⦄ run step initial ⦃Q⦄ := by
  let Inv := fun s ↦ I s ∨ ∃ n, seg step cut I Q n s
  have preserves : ∀ s, Inv s → Sum.elim Inv Q (step s) := by
    intro s hs
    obtain ⟨n, hn⟩ : ∃ n, seg step cut I Q n s := hs.elim (segments s) id
    cases n with
    | zero => exact False.elim hn
    | succ n =>
      simp only [seg] at hn
      cases h : step s with
      | inr a => simpa [h] using hn
      | inl s' =>
        simp only [h, Sum.elim_inl] at hn ⊢
        by_cases hc : cut s' = true
        · simp only [hc, ite_true] at hn; exact Or.inl hn
        · simp only [hc] at hn; exact Or.inr ⟨n, by simpa using hn⟩
  constructor
  intro _
  exact (run_spec step initial Inv Q (fun s ↦ ⟨fun h ↦ preserves s h⟩)).le_wp (Or.inl hi)

/-- Execute instructions with `vcgen` until every goal is at a cut point or an exit.
`walk step, cut` names the generated step function and the cut predicate. With
`using tac`, `tac` is tried on every goal after each step, so infeasible branches (a load's
non-RAM paths under a RAM premise) are closed as they appear instead of being walked. -/
syntax "walk " ident ", " ident (" using " tacticSeq)? : tactic

macro_rules
  | `(tactic| walk $step:ident, $cut:ident) => `(tactic| walk $step:ident, $cut:ident using fail)
  | `(tactic| walk $step:ident, $cut:ident using $tac:tacticSeq) => `(tactic| (
    apply seg_succ
    vcgen [$step:ident]
    all_goals simp only [Sum.elim, $cut:ident, ite_true, ite_false, Bool.false_eq_true,
      ↓reduceIte] at *
    all_goals try ($tac)
    all_goals repeat' (
      apply seg_succ
      vcgen [$step:ident]
      all_goals simp only [Sum.elim, $cut:ident, ite_true, ite_false, Bool.false_eq_true,
        ↓reduceIte] at *
      all_goals try ($tac))))

end IslaLean
