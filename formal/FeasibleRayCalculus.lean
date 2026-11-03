import CRRAScalar
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.Finite

/-!
Small positive trades suffice at a constrained optimum. Neither an interior
optimum nor an assumed first-order condition is used. These are scalar and
finite-coordinate analytic lemmas, not equilibrium existence assertions.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace OwnershipTrade

theorem right_derivative_nonpos {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0)
    (hmax : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ f 0) : d ≤ 0 := by
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [hmax, ht] with t hm hp
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hp.le) (sub_nonpos.mpr hm)

theorem positive_ray_in_box {G : Type*} [Fintype G]
    (M : ℝ) (x v : G → ℝ)
    (hx : ∀ g, 0 ≤ x g)
    (hcap : ∀ g, x g < M)
    (hnegative : ∀ g, v g < 0 → 0 < x g) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ g, x g + t * v g ∈ Icc (0 : ℝ) M := by
  apply Filter.eventually_all.mpr
  intro g
  have hc : ContinuousAt (fun t : ℝ => x g + t * v g) 0 := by fun_prop
  have hu : ∀ᶠ t in 𝓝[>] (0 : ℝ), x g + t * v g < M :=
    (hc.eventually (gt_mem_nhds (by simpa using hcap g))).filter_mono nhdsWithin_le_nhds
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  by_cases hv : v g < 0
  · have hl : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < x g + t * v g :=
      (hc.eventually (lt_mem_nhds (by simpa using hnegative g hv))).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hl, hu] with t hl hu
    exact ⟨hl.le, hu.le⟩
  · filter_upwards [ht, hu] with t ht hu
    exact ⟨add_nonneg (hx g) (mul_nonneg ht.le (le_of_not_gt hv)), hu.le⟩

end OwnershipTrade

#print axioms OwnershipTrade.right_derivative_nonpos
#print axioms OwnershipTrade.positive_ray_in_box
