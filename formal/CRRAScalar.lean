import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Scalar CRRA facts for the heterogeneous ownership bridge. The utility and
derivative calculation agree with GeneralCRRA.CRRAUtilities (Stage 111),
restated here against Lean 4.35 without rebuilding the accepted 4.19 bank.
No upper curvature restriction is imposed. The globally continuous clipping
extension below is not asserted concave outside the economic domain.
-/

noncomputable section
open Set

namespace OwnershipCRRA

def utility (g : ℝ) : ℝ → ℝ :=
  if g = 1 then Real.log else fun c => c ^ (1 - g) / (1 - g)

theorem utility_hasDerivAt {g c : ℝ} (hc : 0 < c) :
    HasDerivAt (utility g) (c ^ (-g)) c := by
  by_cases hg : g = 1
  · simpa [utility, hg, Real.rpow_neg_one] using Real.hasDerivAt_log hc.ne'
  · have hden : 1 - g ≠ 0 := sub_ne_zero.mpr (Ne.symm hg)
    have hh := (Real.hasDerivAt_rpow_const (p := 1-g) (Or.inl hc.ne')).div_const (1-g)
    have heq : ((1-g)*c^((1-g)-1))/(1-g) = c^(-g) := by
      rw [show (1-g)-1 = -g by ring]
      field_simp [hden]
    simpa only [utility, ite_eq_right hg, heq] using hh

theorem utility_continuousOn (g : ℝ) : ContinuousOn (utility g) (Ioi 0) := by
  intro c hc
  exact (utility_hasDerivAt hc).continuousAt.continuousWithinAt

theorem utility_strictMonoOn (g : ℝ) : StrictMonoOn (utility g) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (utility_continuousOn g)
  intro c hc
  have hp : 0 < c := interior_subset hc
  rw [(utility_hasDerivAt (g := g) hp).deriv]
  exact Real.rpow_pos_of_pos hp _

theorem utility_strictConcaveOn {g : ℝ} (hg : 0 < g) :
    StrictConcaveOn ℝ (Ioi 0) (utility g) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (utility_continuousOn g)
  intro c hc d hd hcd
  have hcpos : 0 < c := interior_subset hc
  have hdpos : 0 < d := interior_subset hd
  rw [(utility_hasDerivAt (g := g) hcpos).deriv,
    (utility_hasDerivAt (g := g) hdpos).deriv]
  exact Real.rpow_lt_rpow_of_neg hcpos hcd (neg_neg_of_pos hg)

theorem utility_clipped_continuous {X : Type*} [TopologicalSpace X]
    (g floor : ℝ) (hf : 0 < floor) (f : X → ℝ) (hfc : Continuous f) :
    Continuous (fun x => utility g (max (f x) floor)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : 0 < max (f x) floor := lt_of_lt_of_le hf (le_max_right _ _)
  have hu : ContinuousAt (utility g) (max (f x) floor) :=
    (utility_hasDerivAt (g := g) hp).continuousAt
  have hm : ContinuousAt (fun z : X => max (f z) floor) x :=
    (hfc.max continuous_const).continuousAt
  exact ContinuousAt.comp (f := fun z : X => max (f z) floor) hu hm

end OwnershipCRRA

#print axioms OwnershipCRRA.utility_hasDerivAt
#print axioms OwnershipCRRA.utility_continuousOn
#print axioms OwnershipCRRA.utility_strictMonoOn
#print axioms OwnershipCRRA.utility_strictConcaveOn
#print axioms OwnershipCRRA.utility_clipped_continuous
