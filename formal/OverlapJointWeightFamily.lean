import OverlapGlobalWeightUniqueness

/-!
All household/state weight increments vary in one finite-dimensional parameter
space. The actual market derivative at zero is the already accepted physical
reference derivative. No direction-dependent scalar reduction is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OverlapLocal

namespace OverlapJoint
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

abbrev WeightShock (H S : Type*) := H → S → ℝ

def jointData (D : H → Data J S) (v : WeightShock H S)
    (hw : ∀ i s, 0 < (D i).weight s+v i s) (i : H) : Data J S :=
  { D i with weight := fun s => (D i).weight s+v i s, weight_pos := hw i }

def jointResidual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (p : WeightShock H S × MarketState H J) : MarketState H J :=
  (fun j => (∑ i, p.2.2 i j)-supply j,
   fun i j => (budgetValue e a0 p.2 i)^(-(D i).gamma)*p.2.1 j-
     ∑ s, ((D i).weight s+p.1 i s)*(D i).payoff s j*
       (consumption (D i) (p.2.2 i) s)^(-(D i).eta s))

theorem jointResidual_zero (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (z : MarketState H J) :
    jointResidual D e a0 supply (0,z)=residual D e a0 supply z := by
  simp [jointResidual,OverlapLocal.residual,choiceEquation,marginal]

theorem jointResidual_eq_actual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (v : WeightShock H S) (hw : ∀ i s, 0 < (D i).weight s+v i s)
    (z : MarketState H J) :
    jointResidual D e a0 supply (v,z)=residual (jointData D v hw) e a0 supply z := rfl

theorem jointResidual_line (D : H → Data J S) (W : WeightShock H S)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (t : ℝ) (z : MarketState H J) :
    jointResidual D e a0 supply ((fun i s => t*W i s),z)=affineResidual D W e a0 supply (t,z) := rfl

theorem jointResidual_contDiffAt (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ContDiffAt ℝ 1 (jointResidual D e a0 supply) (0,(q,a0)) := by
  have hbudget : ∀ i, ContDiffAt ℝ 1
      (fun p : WeightShock H S × MarketState H J => budgetValue e a0 p.2 i) (0,(q,a0)) := by
    intro i
    unfold budgetValue
    fun_prop
  have hfuture : ∀ i s, ContDiffAt ℝ 1
      (fun p : WeightShock H S × MarketState H J => consumption (D i) (p.2.2 i) s)
        (0,(q,a0)) := by
    intro i s
    unfold consumption
    fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ 1
      (fun p : WeightShock H S × MarketState H J => (∑ i, p.2.2 i j)-supply j) _
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    have hb := (hbudget i).rpow_const_of_ne (p := -(D i).gamma)
      (by rw [budget_reference]; exact ne_of_gt (he i))
    have hp : ContDiffAt ℝ 1 (fun p : WeightShock H S × MarketState H J => p.2.1 j)
        (0,(q,a0)) := by fun_prop
    have hs : ∀ s, ContDiffAt ℝ 1
        (fun p : WeightShock H S × MarketState H J => ((D i).weight s+p.1 i s)*
          (D i).payoff s j*(consumption (D i) (p.2.2 i) s)^(-(D i).eta s)) (0,(q,a0)) := by
      intro s
      have hw : ContDiffAt ℝ 1
          (fun p : WeightShock H S × MarketState H J => (D i).weight s+p.1 i s)
          (0,(q,a0)) := by fun_prop
      exact (hw.mul (contDiffAt_const (c := (D i).payoff s j))).mul
        ((hfuture i s).rpow_const_of_ne (ne_of_gt (consumption_positive (D i) (ha0 i) s)))
    exact (hb.mul hp).sub (ContDiffAt.sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hs s))

theorem joint_partial_isInvertible [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (fderiv ℝ (jointResidual D e a0 supply) (0,(q,a0)) ∘L
      ContinuousLinearMap.inr ℝ (WeightShock H S) (MarketState H J)).IsInvertible := by
  have hc := jointResidual_contDiffAt D e a0 supply q he ha0
  have hg : HasFDerivAt (fun z : MarketState H J => ((0 : WeightShock H S),z))
      (ContinuousLinearMap.inr ℝ (WeightShock H S) (MarketState H J)) (q,a0) := by
    exact (hasFDerivAt_const (0 : WeightShock H S) (q,a0)).prodMk (hasFDerivAt_id (q,a0))
  have hh := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (q,a0) hg
  have hfixed : HasFDerivAt (residual D e a0 supply)
      (fderiv ℝ (jointResidual D e a0 supply) (0,(q,a0)) ∘L
        ContinuousLinearMap.inr ℝ (WeightShock H S) (MarketState H J)) (q,a0) := by
    simpa only [Function.comp_def,jointResidual_zero] using hh
  rw [hfixed.unique
    (actual_residual_reference_strict_derivative D e a0 supply q he ha0).hasFDerivAt]
  exact referenceDerivative_isInvertible D e a0 q he ha0

theorem joint_local_root_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ∃ psi : WeightShock H S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, jointResidual D e a0 supply (v,psi v)=jointResidual D e a0 supply (0,(q,a0))) ∧
      (∀ᶠ p in 𝓝 (0,(q,a0)), jointResidual D e a0 supply p=jointResidual D e a0 supply (0,(q,a0)) ↔
        psi p.1=p.2) := by
  have hc := jointResidual_contDiffAt D e a0 supply q he ha0
  have hi := joint_partial_isInvertible D e a0 supply q he ha0
  exact ⟨hc.implicitFunction (by norm_num) hi,hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi,
    hc.eventually_apply_implicitFunction (by norm_num) hi,
    hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi⟩

theorem joint_local_actual_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < q j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=q j*(e i)^(-(D i).gamma)) :
    ∃ psi : WeightShock H S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, ∃ hw : ∀ i s, 0 < (D i).weight s+v i s,
        IsEquilibrium (jointData D v hw) e a0 supply
          (psi v).1 (budgetValue e a0 (psi v)) (psi v).2 ∧ jointResidual D e a0 supply (v,psi v)=0) ∧
      (∀ᶠ p : WeightShock H S × MarketState H J in 𝓝 (0,(q,a0)),
        ∀ hw : ∀ i s, 0 < (D i).weight s+p.1 i s, ∀ c : H → ℝ,
        IsEquilibrium (jointData D p.1 hw) e a0 supply p.2.1 c p.2.2 →
          p.2=psi p.1 ∧ c=budgetValue e a0 p.2) := by
  classical
  obtain ⟨psi,hpsi,hcd,hroot,hgraph⟩ := joint_local_root_family D e a0 supply q he
    (fun i j => (ha0 i j).le)
  have hbase : jointResidual D e a0 supply (0,(q,a0))=0 := by
    rw [jointResidual_zero]
    apply Prod.ext
    · funext j
      change (∑ i, a0 i j)-supply j=0
      rw [hstock j,sub_self]
    · funext i j
      change (budgetValue e a0 (q,a0) i)^(-(D i).gamma)*q j-marginal (D i) (a0 i) j=0
      rw [budget_reference,heuler i j]
      ring
  have hcont : ContinuousAt psi 0 := hcd.continuousAt
  have hprice : ∀ᶠ v in 𝓝 0, ∀ j, 0 < (psi v).1 j := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun v => (psi v).1 j) 0 :=
      (continuous_apply j).continuousAt.comp hcont.fst
    have hp : 0 < (psi 0).1 j := by rw [hpsi]; exact hq j
    exact hc.eventually (Ioi_mem_nhds hp)
  have hcurrent : ∀ᶠ v in 𝓝 0, ∀ i, 0 < budgetValue e a0 (psi v) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hb : Continuous (fun z : MarketState H J => budgetValue e a0 z i) := by
      unfold budgetValue
      fun_prop
    have hc := hb.continuousAt.comp hcont
    have hp : 0 < budgetValue e a0 (psi 0) i := by rw [hpsi,budget_reference]; exact he i
    exact hc.eventually (Ioi_mem_nhds hp)
  have hholding : ∀ᶠ v in 𝓝 0, ∀ i j, 0 < (psi v).2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun v => (psi v).2 i j) 0 :=
      (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hcont.snd)
    have hp : 0 < (psi 0).2 i j := by rw [hpsi]; exact ha0 i j
    exact hc.eventually (Ioi_mem_nhds hp)
  have hweights : ∀ᶠ v : WeightShock H S in 𝓝 0, ∀ i s, 0 < (D i).weight s+v i s := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro s
    have hi : Continuous (fun v : WeightShock H S => v i) := continuous_apply i
    have hs : Continuous (fun x : S → ℝ => x s) := continuous_apply s
    have heval : Continuous (fun v : WeightShock H S => v i s) := hs.comp hi
    have hsum : Continuous (fun v : WeightShock H S => (D i).weight s+v i s) :=
      continuous_const.add heval
    have hc : ContinuousAt (fun v : WeightShock H S => (D i).weight s+v i s) 0 := hsum.continuousAt
    have hp : 0 < (D i).weight s+(0 : WeightShock H S) i s := by simpa using (D i).weight_pos s
    exact hc.eventually (Ioi_mem_nhds hp)
  have hnear : ∀ᶠ p : WeightShock H S × MarketState H J in 𝓝 (0,(q,a0)),
      ∀ i j, 0 < p.2.2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun p : WeightShock H S × MarketState H J => p.2.2 i j)
        (0,(q,a0)) := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (ha0 i j))
  refine ⟨psi,hpsi,hcd,?_,?_⟩
  · filter_upwards [hroot,hprice,hcurrent,hholding,hweights] with v hv hqv hcv hav hwv
    refine ⟨hwv,root_is_actual_equilibrium (jointData D v hwv) e a0 supply (psi v)
      hstock hqv hcv (fun i j => (hav i j).le) ?_,hv.trans hbase⟩
    rw [← jointResidual_eq_actual]
    exact hv.trans hbase
  · filter_upwards [hgraph,hnear] with p hp hpa
    intro hw c hEq
    have hr := interior_equilibrium_is_root (jointData D p.1 hw) e a0 supply p.2.1 c p.2.2 hEq hpa
    have hraw : jointResidual D e a0 supply p=0 := by
      rw [jointResidual_eq_actual D e a0 supply p.1 hw p.2]
      exact hr
    exact ⟨(hp.mp (hraw.trans hbase.symm)).symm,
      (equilibrium_budget_value (jointData D p.1 hw) e a0 supply p.2.1 c p.2.2 hEq).symm⟩

end OverlapJoint

#print axioms OverlapJoint.jointResidual_zero
#print axioms OverlapJoint.jointResidual_eq_actual
#print axioms OverlapJoint.jointResidual_line
#print axioms OverlapJoint.jointResidual_contDiffAt
#print axioms OverlapJoint.joint_partial_isInvertible
#print axioms OverlapJoint.joint_local_root_family
#print axioms OverlapJoint.joint_local_actual_family
