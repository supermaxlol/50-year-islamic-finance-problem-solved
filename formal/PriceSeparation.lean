import Mathlib

/-!
Stage 244 (draft): price-extraction + separating-price, factored standalone (upstream ③).

`exists_price_repr` — every continuous linear functional on the finite good space `S → ℝ`
is given by a price vector `p`: `f x = ∑ p·x`. This is the dual-representation core (the
`hrepr` step of stage 237), isolated for reuse.

`separating_price` — a convex, open, nonempty set `B` and an exterior point `Ω ∉ B` admit a
nonzero price `p` with `∑ p·Ω ≤ ∑ p·b` for all `b ∈ B`. One lemma behind the Second Welfare
econ-wrapper, no-arbitrage / FTAP (Farkas), core-equivalence, and production efficiency prices.
-/

noncomputable section
open scoped BigOperators

namespace PriceSeparation

variable {S : Type*} [Fintype S]

/-- Every continuous linear functional on the finite good space is a price vector. -/
theorem exists_price_repr (f : (S → ℝ) →L[ℝ] ℝ) :
    ∃ p : S → ℝ, ∀ x : S → ℝ, f x = ∑ s, p s * x s := by
  classical
  refine ⟨fun s => f (Pi.single s 1), fun x => ?_⟩
  have hx : x = ∑ s, x s • Pi.single s (1 : ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun s _ => by rw [map_smul, smul_eq_mul]; ring)

/-- **Separating price.** A convex, open, nonempty `B` and an exterior point `Ω ∉ B` admit a
nonzero price `p` under which `Ω` is cost-minimal over `B`. -/
theorem separating_price (B : Set (S → ℝ)) (hBconv : Convex ℝ B) (hBopen : IsOpen B)
    (hBne : B.Nonempty) (Ω : S → ℝ) (hΩ : Ω ∉ B) :
    ∃ p : S → ℝ, (∃ s, p s ≠ 0) ∧ ∀ b ∈ B, ∑ s, p s * Ω s ≤ ∑ s, p s * b s := by
  classical
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hBconv hBopen hΩ
  obtain ⟨p0, hp0⟩ := exists_price_repr f
  have hpx : ∀ x : S → ℝ, ∑ s, (- p0 s) * x s = - f x := by
    intro x
    rw [hp0 x, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  refine ⟨fun s => - p0 s, ?_, ?_⟩
  · by_contra hall
    push_neg at hall
    obtain ⟨a, ha⟩ := hBne
    have hfa : f a = 0 := by
      have h0 : ∑ s, (- p0 s) * a s = 0 :=
        Finset.sum_eq_zero (fun s _ => by rw [hall s, zero_mul])
      rw [hpx a] at h0; linarith
    have hfΩ : f Ω = 0 := by
      have h0 : ∑ s, (- p0 s) * Ω s = 0 :=
        Finset.sum_eq_zero (fun s _ => by rw [hall s, zero_mul])
      rw [hpx Ω] at h0; linarith
    have := hf a ha; rw [hfa, hfΩ] at this; exact lt_irrefl 0 this
  · intro b hb
    rw [hpx Ω, hpx b]
    have := hf b hb; linarith

end PriceSeparation

#print axioms PriceSeparation.exists_price_repr
#print axioms PriceSeparation.separating_price
