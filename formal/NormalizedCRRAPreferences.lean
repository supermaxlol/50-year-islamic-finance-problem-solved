import OverlapPayoffGlobal
import Mathlib.Analysis.Calculus.DSlope

/-! An ordinally identical normalization removes the curvature-one singular
constant in CRRA utility. Marginal utility and actual choices are unchanged. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored

namespace OwnershipNormalized

def scalar (g c : ℝ) : ℝ :=
  Real.log c * dslope Real.exp 0 ((1-g)*Real.log c)

theorem exp_dslope_continuous : Continuous (dslope Real.exp (0 : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    exact continuousAt_dslope_same.mpr (Real.differentiable_exp 0)
  · exact (continuousAt_dslope_of_ne hx).mpr Real.continuous_exp.continuousAt

theorem scalar_eq_difference (g c : ℝ) (hc : 0 < c) :
    scalar g c=utility g c-utility g 1 := by
  by_cases hg : g=1
  · subst g
    simp [scalar,utility,dslope_same,Real.deriv_exp]
  by_cases h1 : c=1
  · subst c
    simp [scalar]
  have hd : 1-g ≠ 0 := sub_ne_zero.mpr (Ne.symm hg)
  have hl := Real.log_ne_zero_of_pos_of_ne_one hc h1
  have ht : (1-g)*Real.log c ≠ 0 := mul_ne_zero hd hl
  have he : Real.exp ((1-g)*Real.log c)=c^(1-g) := by
    rw [Real.rpow_def_of_pos hc,mul_comm]
  unfold scalar
  rw [dslope_of_ne _ ht,slope_def_field]
  simp only [Real.exp_zero,sub_zero]
  rw [he]
  simp only [utility,ite_eq_right hg,Real.one_rpow]
  field_simp

theorem scalar_tendsto {g c : ℝ} {gn cn : ℕ → ℝ}
    (hc : 0 < c) (hg : Tendsto gn atTop (𝓝 g)) (hcn : Tendsto cn atTop (𝓝 c)) :
    Tendsto (fun n => scalar (gn n) (cn n)) atTop (𝓝 (scalar g c)) := by
  have hl := (Real.continuousAt_log (ne_of_gt hc)).tendsto.comp hcn
  have hh : Tendsto (fun n => (1-gn n)*Real.log (cn n)) atTop
      (𝓝 ((1-g)*Real.log c)) := (tendsto_const_nhds.sub hg).mul hl
  exact hl.mul ((exp_dslope_continuous.tendsto ((1-g)*Real.log c)).comp hh)

variable {J S : Type*} [Fintype J] [Fintype S]

def anchor (D : Data J S) : ℝ :=
  utility D.gamma 1+∑ s, D.weight s*utility (D.eta s) 1

def value (D : Data J S) (c : ℝ) (a : J → ℝ) : ℝ :=
  scalar D.gamma c+∑ s, D.weight s*scalar (D.eta s) (consumption D a s)

theorem value_eq_difference (D : Data J S) (c : ℝ) (a : J → ℝ)
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) :
    value D c a=economicValue D c a-anchor D := by
  unfold value anchor economicValue
  rw [scalar_eq_difference _ _ hc]
  simp_rw [scalar_eq_difference _ _ (consumption_positive D ha _),mul_sub,
    Finset.sum_sub_distrib]
  unfold consumption
  ring

theorem comparison_iff (D : Data J S) (c d : ℝ) (a b : J → ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    value D c a ≤ value D d b ↔ economicValue D c a ≤ economicValue D d b := by
  rw [value_eq_difference D c a hc ha,value_eq_difference D d b hd hb]
  exact sub_le_sub_iff_right _

theorem value_tendsto (Dn : ℕ → Data J S) (D : Data J S)
    {cn : ℕ → ℝ} {an : ℕ → J → ℝ} {c : ℝ} {a : J → ℝ}
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j)
    (hg : Tendsto (fun n => (Dn n).gamma) atTop (𝓝 D.gamma))
    (heta : ∀ s, Tendsto (fun n => (Dn n).eta s) atTop (𝓝 (D.eta s)))
    (hw : ∀ s, Tendsto (fun n => (Dn n).weight s) atTop (𝓝 (D.weight s)))
    (hcn : Tendsto cn atTop (𝓝 c))
    (hfuture : ∀ s, Tendsto (fun n => consumption (Dn n) (an n) s) atTop
      (𝓝 (consumption D a s))) :
    Tendsto (fun n => value (Dn n) (cn n) (an n)) atTop (𝓝 (value D c a)) := by
  apply Tendsto.add
  · exact scalar_tendsto hc hg hcn
  · apply tendsto_finsetSum
    intro s _
    exact (hw s).mul (scalar_tendsto (consumption_positive D ha s) (heta s) (hfuture s))

end OwnershipNormalized

#print axioms OwnershipNormalized.exp_dslope_continuous
#print axioms OwnershipNormalized.scalar_eq_difference
#print axioms OwnershipNormalized.scalar_tendsto
#print axioms OwnershipNormalized.value_eq_difference
#print axioms OwnershipNormalized.comparison_iff
#print axioms OwnershipNormalized.value_tendsto
