import Mathlib

/-!
Stage 237 (draft): Second Welfare Theorem — separating-hyperplane core.

The novel step of the SWT: given the aggregate strictly-preferred set `B` (convex, open,
nonempty — from convex preferences and continuity) and the efficient aggregate `Ω ∉ B`
(from Pareto efficiency), a nonzero supporting price vector `p` exists under which `Ω` is
cost-minimal over `B` (`∑ p·Ω ≤ ∑ p·g` for every preferred aggregate `g`). Proof: convex
separation gives a continuous functional; represent it as a price vector on the finite good
space and read off the inequality.
-/

noncomputable section
open scoped BigOperators

namespace SecondWelfare

variable {S : Type*} [Fintype S]

/-- **SWT separating-hyperplane core.** A nonzero supporting price exists at which the
efficient aggregate `Ω` is cost-minimal over the (convex, open) aggregate better set `B`. -/
theorem supporting_prices_of_separation
    (B : Set (S → ℝ)) (hBconv : Convex ℝ B) (hBopen : IsOpen B) (hBne : B.Nonempty)
    (Ω : S → ℝ) (hΩ : Ω ∉ B) :
    ∃ p : S → ℝ, (∃ s, p s ≠ 0) ∧ ∀ g ∈ B, ∑ s, p s * Ω s ≤ ∑ s, p s * g s := by
  classical
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hBconv hBopen hΩ
  -- hf : ∀ a ∈ B, f a < f Ω
  have hrepr : ∀ x : S → ℝ, f x = ∑ s, f (Pi.single s 1) * x s := by
    intro x
    have hx : x = ∑ s, x s • Pi.single s (1:ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun s _ => by rw [map_smul, smul_eq_mul]; ring)
  have hpx : ∀ x : S → ℝ, ∑ s, (- f (Pi.single s 1)) * x s = - f x := by
    intro x
    rw [hrepr x, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  refine ⟨fun s => - f (Pi.single s 1), ?_, ?_⟩
  · by_contra hall
    push_neg at hall
    obtain ⟨a, ha⟩ := hBne
    have hfa : f a = 0 := by
      have := hpx a; rw [show (∑ s, (- f (Pi.single s 1)) * a s) = 0 from ?_] at this
      · linarith
      · exact Finset.sum_eq_zero (fun s _ => by rw [hall s, zero_mul])
    have hfΩ : f Ω = 0 := by
      have := hpx Ω; rw [show (∑ s, (- f (Pi.single s 1)) * Ω s) = 0 from ?_] at this
      · linarith
      · exact Finset.sum_eq_zero (fun s _ => by rw [hall s, zero_mul])
    have := hf a ha; rw [hfa, hfΩ] at this; exact lt_irrefl 0 this
  · intro g hg
    rw [hpx Ω, hpx g]
    have := hf g hg
    linarith

end SecondWelfare

#print axioms SecondWelfare.supporting_prices_of_separation
