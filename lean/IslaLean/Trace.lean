-- Vendored from pcode-lean/PcodeLean/Trace.lean (namespace renamed) so this project is self-contained.
import IslaLean.Run

namespace IslaLean

/-- Check the initial state, every visited instruction boundary, and the return state.
Zero steps still check the initial state; exhausting a prefix asserts no termination. -/
def traceSafe (step : Step σ α) (I : σ → Prop) (Q : α → Prop) : Nat → σ → Prop
  | 0, s => I s
  | n + 1, s => I s ∧ Sum.elim (traceSafe step I Q n) Q (step s)

/-- The observation holds along every finite execution prefix, including after return. -/
def Always (step : Step σ α) (s : σ) (I : σ → Prop) (Q : α → Prop) : Prop :=
  ∀ n, traceSafe step I Q n s

theorem always_invariant (step : Step σ α) (s : σ) (initial : I s)
    (preserves : ∀ s, I s → Sum.elim I Q (step s)) : Always step s I Q := by
  intro n
  induction n generalizing s with
  | zero => exact initial
  | succ n ih =>
    refine ⟨initial, ?_⟩
    have h := preserves s initial
    cases hs : step s with
    | inl next =>
      simp only [hs, Sum.elim_inl] at h ⊢
      exact ih next h
    | inr out => simpa only [hs, Sum.elim_inr] using h

theorem Always.mono (h : Always step s I Q)
    (states : ∀ s, I s → J s) (returns : ∀ a, Q a → R a) : Always step s J R := by
  intro n
  have hp := h n
  clear h
  induction n generalizing s with
  | zero => exact states s hp
  | succ n ih =>
    refine ⟨states s hp.1, ?_⟩
    cases hs : step s with
    | inl next => exact ih (s := next) (by simpa only [hs, Sum.elim_inl] using hp.2)
    | inr out => exact returns out (by simpa only [hs, Sum.elim_inr] using hp.2)

theorem Always.post (h : Always step s I Q) : (run step s).wp Q := by
  intro n
  have hp := h n
  clear h
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    simp only [safe]
    cases hs : step s with
    | inl next => exact ih (s := next) (by simpa only [hs, Sum.elim_inl] using hp.2)
    | inr out => simpa only [hs, Sum.elim_inr] using hp.2

end IslaLean
