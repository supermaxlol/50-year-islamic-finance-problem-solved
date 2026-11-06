import Mathlib

/-!
Stage 241 (draft): Walras' law from local non-satiation.

`budget_binds_of_lns`: a utility maximizer over a budget set exhausts its budget
(`p·d = w`) whenever preferences are locally non-satiated and the price is nonzero. This is
the microeconomic source of Walras' law — it is what lets every welfare theorem assume
budget balance rather than postulate it.

`walras_law_of_binds`: if every household's demand binds at its own wealth `p·ω_h`, the
aggregate excess demand has value zero (`p·(∑ d_h − ∑ ω_h) = 0`) — Walras' law proper.
-/

noncomputable section
open scoped BigOperators

namespace WalrasLNS

variable {S : Type*} [Fintype S]

/-- **Budget binds under local non-satiation.** If `d` maximizes `U` over the budget
`{x : p·x ≤ w}`, preferences are locally non-satiated, and the price is not identically zero,
then the budget constraint binds: `p·d = w`. -/
theorem budget_binds_of_lns (p : S → ℝ) (w : ℝ) (U : (S → ℝ) → ℝ) (d : S → ℝ)
    (hd_budget : ∑ s, p s * d s ≤ w)
    (hd_opt : ∀ y : S → ℝ, ∑ s, p s * y s ≤ w → U y ≤ U d)
    (hLNS : ∀ (x : S → ℝ) (ε : ℝ), 0 < ε → ∃ y : S → ℝ, dist x y < ε ∧ U x < U y) :
    ∑ s, p s * d s = w := by
  by_contra hne
  have hlt : ∑ s, p s * d s < w := lt_of_le_of_ne hd_budget hne
  set C := ∑ s, |p s| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hDpos : 0 < w - ∑ s, p s * d s := by linarith
  set ε := (w - ∑ s, p s * d s) / (C + 1) with hε
  have hε0 : 0 < ε := div_pos hDpos (by linarith)
  obtain ⟨y, hdist, hUy⟩ := hLNS d ε hε0
  -- bound the price value of the move d → y by C · dist d y
  have hbound : ∑ s, p s * y s - ∑ s, p s * d s ≤ C * dist y d := by
    rw [← Finset.sum_sub_distrib, hC, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _
    calc p s * y s - p s * d s = p s * (y s - d s) := by ring
      _ ≤ |p s * (y s - d s)| := le_abs_self _
      _ = |p s| * |y s - d s| := abs_mul _ _
      _ ≤ |p s| * dist y d := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [← Real.dist_eq]; exact dist_le_pi_dist y d s
  -- the budget slack dominates that bound, so y is strictly affordable
  have hdy : dist y d < ε := by rwa [dist_comm] at hdist
  have hCe : C * ε < w - ∑ s, p s * d s := by
    rw [hε, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < C + 1)]
    nlinarith [hDpos, hC0]
  have hpy : ∑ s, p s * y s < w := by
    have h1 : C * dist y d ≤ C * ε := mul_le_mul_of_nonneg_left hdy.le hC0
    linarith [hbound, h1, hCe]
  exact absurd (hd_opt y hpy.le) (not_le.mpr hUy)

/-- **Walras' law.** If every household's demand binds at its own wealth `p·ω_h`, then the
value of aggregate excess demand is zero. -/
theorem walras_law_of_binds {H : Type*} [Fintype H] (p : S → ℝ) (d : H → S → ℝ) (ω : H → S → ℝ)
    (hbinds : ∀ h, ∑ s, p s * d h s = ∑ s, p s * ω h s) :
    ∑ s, p s * ((∑ h, d h s) - (∑ h, ω h s)) = 0 := by
  have hswap : ∀ f : H → S → ℝ, ∑ s, p s * (∑ h, f h s) = ∑ h, ∑ s, p s * f h s := by
    intro f; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  have e1 : ∑ s, p s * ((∑ h, d h s) - (∑ h, ω h s))
      = (∑ s, p s * (∑ h, d h s)) - (∑ s, p s * (∑ h, ω h s)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
  rw [e1, hswap d, hswap ω]
  rw [Finset.sum_congr rfl (fun h _ => hbinds h)]
  ring

end WalrasLNS

#print axioms WalrasLNS.budget_binds_of_lns
#print axioms WalrasLNS.walras_law_of_binds
