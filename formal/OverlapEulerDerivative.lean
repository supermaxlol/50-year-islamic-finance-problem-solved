import OverlapReferenceLinearization

/-!
The actual uncapped ownership-budget and Euler/clearing equations. Their joint
strict derivative at the initial allocation is the primitive invertible map
constructed in OverlapReferenceLinearization. A feasible root is lifted to
actual global household optimization, not treated as an assumed demand map.
-/

noncomputable section
open scoped BigOperators
open OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSufficiency

namespace OverlapLocal

section Forms
variable {H J : Type*} [Fintype H] [Fintype J]

def pairLinear (p : J → ℝ) : (J → ℝ) →ₗ[ℝ] ℝ where
  toFun := pair p
  map_add' := pair_add_right p
  map_smul' r v := by simpa [smul_eq_mul] using pair_smul_right p v r

def priceEval (j : J) : MarketState H J →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (J → ℝ) (H → J → ℝ))

def holdingEval (i : H) (j : J) : MarketState H J →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd ℝ (J → ℝ) (H → J → ℝ)))

def form (i : H) (p : J → ℝ) : MarketState H J →L[ℝ] ℝ :=
  (pairLinear p).toContinuousLinearMap.comp ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd ℝ (J → ℝ) (H → J → ℝ)))

omit [Fintype H] [Fintype J] in
@[simp] theorem priceEval_apply (j : J) (z : MarketState H J) : priceEval j z=z.1 j := rfl
omit [Fintype H] [Fintype J] in
@[simp] theorem holdingEval_apply (i : H) (j : J) (z : MarketState H J) :
    holdingEval i j z=z.2 i j := rfl
omit [Fintype H] in
@[simp] theorem form_apply (i : H) (p : J → ℝ) (z : MarketState H J) :
    form i p z=pair p (z.2 i) := rfl

def budgetValue (e : H → ℝ) (a0 : H → J → ℝ) (z : MarketState H J) (i : H) : ℝ :=
  e i+∑ j, z.1 j*(a0 i j-z.2 i j)

omit [Fintype H] in
theorem budget_reference (e : H → ℝ) (a0 : H → J → ℝ) (q : J → ℝ) (i : H) :
    budgetValue e a0 (q,a0) i=e i := by simp [budgetValue]

def budgetDerivative (q : J → ℝ) (i : H) : MarketState H J →L[ℝ] ℝ :=
  ∑ j, q j • (-holdingEval i j)

omit [Fintype H] in
theorem budgetDerivative_apply (q : J → ℝ) (i : H) (z : MarketState H J) :
    budgetDerivative q i z= -pair q (z.2 i) := by
  simp [budgetDerivative,pair,Finset.sum_neg_distrib]

theorem budget_hasStrictFDerivAt (e : H → ℝ) (a0 : H → J → ℝ)
    (q : J → ℝ) (i : H) :
    HasStrictFDerivAt (fun z => budgetValue e a0 z i) (budgetDerivative q i) (q,a0) := by
  have hterm : ∀ j, HasStrictFDerivAt
      (fun z : MarketState H J => z.1 j*(a0 i j-z.2 i j))
      (q j • (-holdingEval i j)) (q,a0) := by
    intro j
    have hp := (priceEval (H := H) j).hasStrictFDerivAt (x := (q,a0))
    have ha := (holdingEval i j).hasStrictFDerivAt (x := (q,a0))
    simpa only [Pi.mul_def,priceEval_apply,holdingEval_apply,sub_self,zero_smul,add_zero]
      using hp.mul (ha.const_sub (a0 i j))
  simpa only [budgetValue,budgetDerivative] using
    (HasStrictFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hterm j)).const_add (e i)

omit [Fintype H] in
theorem reconstructed_budget (e : H → ℝ) (a0 : H → J → ℝ)
    (z : MarketState H J) (i : H) :
    budgetValue e a0 z i+∑ j, z.1 j*z.2 i j=e i+∑ j, z.1 j*a0 i j := by
  simp only [budgetValue,mul_sub,Finset.sum_sub_distrib]
  ring

end Forms

section Equations
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

def choiceEquation (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (z : MarketState H J) (i : H) (j : J) : ℝ :=
  (budgetValue e a0 z i)^(-(D i).gamma)*z.1 j-marginal (D i) (z.2 i) j

def residual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (z : MarketState H J) : MarketState H J :=
  (fun j => (∑ i, z.2 i j)-supply j,fun i j => choiceEquation D e a0 z i j)

def marginalDerivative (D : H → Data J S) (a0 : H → J → ℝ) (i : H) (j : J) :
    MarketState H J →L[ℝ] ℝ :=
  ∑ s, ((D i).weight s*(D i).payoff s j) •
    ((-(D i).eta s*(consumption (D i) (a0 i) s)^(-(D i).eta s-1)) •
      form i ((D i).payoff s))

omit [Fintype S] in
theorem consumption_hasStrictFDerivAt (D : H → Data J S) (a0 : H → J → ℝ)
    (q : J → ℝ) (i : H) (s : S) :
    HasStrictFDerivAt (fun z : MarketState H J => consumption (D i) (z.2 i) s)
      (form i ((D i).payoff s)) (q,a0) := by
  simpa only [form_apply,pair,consumption] using
    ((form i ((D i).payoff s)).hasStrictFDerivAt (x := (q,a0))).const_add ((D i).income s)

theorem marginal_hasStrictFDerivAt (D : H → Data J S) (a0 : H → J → ℝ)
    (q : J → ℝ) (ha0 : ∀ i j, 0 ≤ a0 i j) (i : H) (j : J) :
    HasStrictFDerivAt (fun z : MarketState H J => marginal (D i) (z.2 i) j)
      (marginalDerivative D a0 i j) (q,a0) := by
  have hterm : ∀ s, HasStrictFDerivAt
      (fun z : MarketState H J => ((D i).weight s*(D i).payoff s j)*
        (consumption (D i) (z.2 i) s)^(-(D i).eta s))
      (((D i).weight s*(D i).payoff s j) •
        ((-(D i).eta s*(consumption (D i) (a0 i) s)^(-(D i).eta s-1)) •
          form i ((D i).payoff s))) (q,a0) := by
    intro s
    exact ((consumption_hasStrictFDerivAt D a0 q i s).rpow_const
      (Or.inl (ne_of_gt (consumption_positive (D i) (ha0 i) s)))).const_mul
        ((D i).weight s*(D i).payoff s j)
  simpa only [marginal,marginalDerivative] using
    HasStrictFDerivAt.fun_sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hterm s)

omit [Fintype H] in
theorem marginalDerivative_apply (D : H → Data J S) (a0 : H → J → ℝ)
    (i : H) (j : J) (z : MarketState H J) :
    marginalDerivative D a0 i j z=
      -(∑ s, physicalCoefficient (D i) (a0 i) s*(D i).payoff s j*
        pair ((D i).payoff s) (z.2 i)) := by
  simp only [marginalDerivative,sum_apply,
    smul_apply,smul_eq_mul,form_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  dsimp [physicalCoefficient]
  ring

def choiceDerivative (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (q : J → ℝ) (i : H) (j : J) : MarketState H J →L[ℝ] ℝ :=
  (e i)^(-(D i).gamma) • priceEval j+
    q j • ((-(D i).gamma*(e i)^(-(D i).gamma-1)) • budgetDerivative q i)-
      marginalDerivative D a0 i j

theorem choice_hasStrictFDerivAt (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (q : J → ℝ) (he : ∀ i, 0 < e i)
    (ha0 : ∀ i j, 0 ≤ a0 i j) (i : H) (j : J) :
    HasStrictFDerivAt (fun z => choiceEquation D e a0 z i j)
      (choiceDerivative D e a0 q i j) (q,a0) := by
  have hp := (budget_hasStrictFDerivAt e a0 q i).rpow_const
    (p := -(D i).gamma) (Or.inl (by rw [budget_reference]; exact ne_of_gt (he i)))
  have hprice := (priceEval (H := H) j).hasStrictFDerivAt (x := (q,a0))
  simpa only [Pi.mul_def,Pi.sub_def,choiceEquation,choiceDerivative,budget_reference,priceEval_apply] using
    (hp.mul hprice).sub (marginal_hasStrictFDerivAt D a0 q ha0 i j)

omit [Fintype H] in
theorem choiceDerivative_apply (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (q : J → ℝ) (he : ∀ i, 0 < e i)
    (i : H) (j : J) (z : MarketState H J) :
    choiceDerivative D e a0 q i j z=physicalLambda (D i) (e i)*z.1 j+
      physicalCurrentCurvature (D i) (e i)*q j*pair q (z.2 i)+
      ∑ s, physicalCoefficient (D i) (a0 i) s*(D i).payoff s j*
        pair ((D i).payoff s) (z.2 i) := by
  simp only [choiceDerivative,sub_apply,add_apply,
    smul_apply,smul_eq_mul,priceEval_apply,budgetDerivative_apply,
    marginalDerivative_apply]
  rw [Real.rpow_sub_one (ne_of_gt (he i))]
  dsimp [physicalLambda,physicalCurrentCurvature]
  ring

def rawDerivative (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (q : J → ℝ) : MarketState H J →L[ℝ] MarketState H J :=
  (ContinuousLinearMap.pi (fun j => ∑ i, holdingEval i j)).prod
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j => choiceDerivative D e a0 q i j)))

theorem residual_hasStrictFDerivAt_raw (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ) (he : ∀ i, 0 < e i)
    (ha0 : ∀ i j, 0 ≤ a0 i j) :
    HasStrictFDerivAt (residual D e a0 supply) (rawDerivative D e a0 q) (q,a0) := by
  have hclear : HasStrictFDerivAt
      (fun z : MarketState H J => fun j => (∑ i, z.2 i j)-supply j)
      (ContinuousLinearMap.pi (fun j => ∑ i, holdingEval i j)) (q,a0) := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    simpa only [sum_apply,holdingEval_apply] using
      ((∑ i, holdingEval (H := H) i j).hasStrictFDerivAt (x := (q,a0))).sub_const (supply j)
  have hchoice := hasStrictFDerivAt_pi.mpr (fun i =>
    hasStrictFDerivAt_pi.mpr (fun j => choice_hasStrictFDerivAt D e a0 q he ha0 i j))
  exact hclear.prodMk hchoice

theorem rawDerivative_eq_referenceDerivative [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (q : J → ℝ) (he : ∀ i, 0 < e i) :
    rawDerivative D e a0 q=referenceDerivative D e a0 q := by
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · funext j
    change (∑ i, holdingEval i j) z=∑ i, z.2 i j
    simp only [sum_apply,holdingEval_apply]
  · funext i j
    change choiceDerivative D e a0 q i j z=
      physicalHessian (D i) (e i) (a0 i) q (z.2 i) j+physicalLambda (D i) (e i)*z.1 j
    rw [choiceDerivative_apply D e a0 q he,physicalHessian,curvature_apply]
    ring

theorem actual_residual_reference_strict_derivative [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply q : J → ℝ) (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    HasStrictFDerivAt (residual D e a0 supply) (referenceDerivative D e a0 q) (q,a0) := by
  rw [← rawDerivative_eq_referenceDerivative D e a0 q he]
  exact residual_hasStrictFDerivAt_raw D e a0 supply q he ha0

theorem actual_reference_jacobian_isInvertible [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply q : J → ℝ) (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (fderiv ℝ (residual D e a0 supply) (q,a0)).IsInvertible := by
  rw [(actual_residual_reference_strict_derivative D e a0 supply q he ha0).hasFDerivAt.fderiv]
  exact referenceDerivative_isInvertible D e a0 q he ha0

theorem root_is_actual_equilibrium (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply : J → ℝ) (z : MarketState H J)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (hq : ∀ j, 0 < z.1 j) (hc : ∀ i, 0 < budgetValue e a0 z i)
    (ha : ∀ i j, 0 ≤ z.2 i j) (hroot : residual D e a0 supply z=0) :
    IsEquilibrium D e a0 supply z.1 (budgetValue e a0 z) z.2 := by
  have hclear : ∀ j, ∑ i, z.2 i j=supply j := by
    intro j
    have hh := congrFun (congrArg Prod.fst hroot) j
    change (∑ i, z.2 i j)-supply j=0 at hh
    linarith
  have heuler : ∀ i j, marginal (D i) (z.2 i) j=
      z.1 j*(budgetValue e a0 z i)^(-(D i).gamma) := by
    intro i j
    have hh := congrFun (congrFun (congrArg Prod.snd hroot) i) j
    change (budgetValue e a0 z i)^(-(D i).gamma)*z.1 j-
      marginal (D i) (z.2 i) j=0 at hh
    nlinarith
  have hkkt : ∀ i j,
      marginal (D i) (z.2 i) j ≤ z.1 j*(budgetValue e a0 z i)^(-(D i).gamma) ∧
      z.2 i j*(z.1 j*(budgetValue e a0 z i)^(-(D i).gamma)-marginal (D i) (z.2 i) j)=0 := by
    intro i j
    rw [heuler]
    exact ⟨le_rfl,by ring⟩
  have hcurrent : (∑ i, budgetValue e a0 z i)=∑ i, e i := by
    have hs := OwnershipSupported.aggregate_cost_equality z.1 (fun _ : H => 0)
      (fun _ : H => 0) z.2 a0 rfl (fun j => (hclear j).trans (hstock j).symm)
    simp only [zero_add] at hs
    have hb := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset H)) =>
      reconstructed_budget e a0 z i)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hs] at hb
    linarith
  refine ⟨hq,hc,ha,?_,?_,hcurrent,hclear,hkkt⟩
  · intro i; exact (reconstructed_budget e a0 z i).le
  · intro i
    exact global_optimality_of_corner_conditions (D i) z.1 (z.2 i)
      (budgetValue e a0 z i) (e i+∑ j, z.1 j*a0 i j)
      (hc i) (ha i) (reconstructed_budget e a0 z i) (hkkt i)

end Equations

theorem interior_control_isInvertible :
    (referenceDerivative OwnershipSupported.InteriorControl.D
      OwnershipSupported.InteriorControl.endowment OwnershipSupported.InteriorControl.initial
      OwnershipSupported.CornerControl.qstar).IsInvertible := by
  apply referenceDerivative_isInvertible
  · intro i; norm_num [OwnershipSupported.InteriorControl.endowment]
  · intro i j; exact (OwnershipSupported.InteriorControl.initial_interior i j).le

theorem interior_control_actual_derivative :
    HasStrictFDerivAt (residual OwnershipSupported.InteriorControl.D
      OwnershipSupported.InteriorControl.endowment OwnershipSupported.InteriorControl.initial
      OwnershipSupported.CornerControl.supply)
      (referenceDerivative OwnershipSupported.InteriorControl.D
        OwnershipSupported.InteriorControl.endowment OwnershipSupported.InteriorControl.initial
        OwnershipSupported.CornerControl.qstar)
      (OwnershipSupported.CornerControl.qstar,OwnershipSupported.InteriorControl.initial) := by
  apply actual_residual_reference_strict_derivative
  · intro i; norm_num [OwnershipSupported.InteriorControl.endowment]
  · intro i j; exact (OwnershipSupported.InteriorControl.initial_interior i j).le

end OverlapLocal

#print axioms OverlapLocal.budget_reference
#print axioms OverlapLocal.budgetDerivative_apply
#print axioms OverlapLocal.budget_hasStrictFDerivAt
#print axioms OverlapLocal.reconstructed_budget
#print axioms OverlapLocal.consumption_hasStrictFDerivAt
#print axioms OverlapLocal.marginal_hasStrictFDerivAt
#print axioms OverlapLocal.marginalDerivative_apply
#print axioms OverlapLocal.choice_hasStrictFDerivAt
#print axioms OverlapLocal.choiceDerivative_apply
#print axioms OverlapLocal.residual_hasStrictFDerivAt_raw
#print axioms OverlapLocal.rawDerivative_eq_referenceDerivative
#print axioms OverlapLocal.actual_residual_reference_strict_derivative
#print axioms OverlapLocal.actual_reference_jacobian_isInvertible
#print axioms OverlapLocal.root_is_actual_equilibrium
#print axioms OverlapLocal.interior_control_isInvertible
#print axioms OverlapLocal.interior_control_actual_derivative
