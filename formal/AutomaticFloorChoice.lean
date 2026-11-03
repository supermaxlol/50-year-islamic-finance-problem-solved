import CRRAScalar
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
Finite positive primitives supply positive minorants and arbitrarily small
common floors. No equilibrium, prices, or optimization conditions are assumed.
These analytic choices will be instantiated in the economic module.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace OwnershipFloorChoice

theorem finite_positive_minorant {I : Type*} [Fintype I]
    (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m < f i := by
  have hall : ∀ᶠ m in 𝓝[>] (0 : ℝ), ∀ i, m < f i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (gt_mem_nhds (hf i)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ m in 𝓝[>] (0 : ℝ), 0 < m := self_mem_nhdsWithin
  obtain ⟨m, hm, hp⟩ := (hall.and hpos).exists
  exact ⟨m, hp, hm⟩

theorem finite_positive_majorant {I : Type*} [Fintype I] (f : I → ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, f i < M := by
  have hall : ∀ᶠ M : ℝ in atTop, ∀ i, f i < M :=
    Filter.eventually_all.mpr (fun i => eventually_gt_atTop (f i))
  obtain ⟨M, hm, hp⟩ := (hall.and (eventually_gt_atTop (0 : ℝ))).exists
  exact ⟨M, hp, hm⟩

theorem common_small_floor {I K : Type*} [Fintype I] [Fintype K]
    (gamma : I → ℝ) (U : I → K → ℝ) (L : K → ℝ) (m : ℝ)
    (hgamma : ∀ i, 0 < gamma i) (hL : ∀ k, 0 < L k) (hm : 0 < m) :
    ∃ delta : ℝ, 0 < delta ∧ delta < m ∧
      ∀ i k, U i k * delta^(gamma i) < L k := by
  have hsmall : ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      ∀ i k, U i k * delta^(gamma i) < L k := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro k
    have hc : Continuous (fun delta : ℝ => U i k * delta^(gamma i)) :=
      continuous_const.mul (Real.continuous_rpow_const (hgamma i).le)
    have hz : U i k * (0 : ℝ)^(gamma i) < L k := by
      simpa [Real.zero_rpow (hgamma i).ne'] using hL k
    exact (hc.continuousAt.eventually (gt_mem_nhds hz)).filter_mono nhdsWithin_le_nhds
  have hbelow : ∀ᶠ delta in 𝓝[>] (0 : ℝ), delta < m :=
    (gt_mem_nhds hm).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ delta in 𝓝[>] (0 : ℝ), 0 < delta := self_mem_nhdsWithin
  obtain ⟨delta, hs, hb, hp⟩ := (hsmall.and (hbelow.and hpos)).exists
  exact ⟨delta, hp, hb, hs⟩

namespace Controls

theorem zero_curvature_cannot_shrink_unit_weight :
    ¬ ∃ delta : ℝ, 0 < delta ∧ (1 : ℝ) * delta^(0 : ℝ) < 1/2 := by
  rintro ⟨delta, _, h⟩
  norm_num at h

theorem nonpositive_target_not_enough :
    ¬ ∃ delta : ℝ, 0 < delta ∧ (1 : ℝ) * delta^(1 : ℝ) < 0 := by
  rintro ⟨delta, hp, h⟩
  norm_num at h
  exact not_lt_of_ge hp.le h

end Controls
end OwnershipFloorChoice

#print axioms OwnershipFloorChoice.finite_positive_minorant
#print axioms OwnershipFloorChoice.finite_positive_majorant
#print axioms OwnershipFloorChoice.common_small_floor
#print axioms OwnershipFloorChoice.Controls.zero_curvature_cannot_shrink_unit_weight
#print axioms OwnershipFloorChoice.Controls.nonpositive_target_not_enough
