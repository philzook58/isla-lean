import IslaLean.Run

/-! Termination from two Hoare triples per instruction block: the invariant is preserved, and a
natural-number rank strictly decreases. Stating the rank condition as a triple lets `vcgen`
discharge it through the Sail model's memory-guard trees, where unfolding `step` directly is
expensive. -/
namespace IslaLean
open Std.WP Lean.Order

theorem finishes_of_triples (step : Step σ α) (I : σ → Prop) (rank : σ → Nat) (Q : α → Prop)
    (preserves : ∀ f, ⦃I f⦄ step f ⦃Sum.elim I Q⦄)
    (decreases : ∀ f, ⦃I f⦄ step f ⦃Sum.elim (fun f' ↦ rank f' < rank f) (fun _ ↦ True)⦄)
    (s : σ) (hs : I s) : finishes step (rank s + 1) s Q := by
  apply finishes_of_rank step I rank Q _ s hs
  intro f hf
  have hp := (preserves f).le_wp hf
  have hd := (decreases f).le_wp hf
  change Sum.elim I Q (step f) at hp
  change Sum.elim (fun f' ↦ rank f' < rank f) (fun _ ↦ True) (step f) at hd
  cases h : step f with
  | inl f' => simp only [h, Sum.elim_inl] at hp hd ⊢; exact ⟨hp, hd⟩
  | inr a => simp only [h, Sum.elim_inr] at hp ⊢; exact hp

end IslaLean
