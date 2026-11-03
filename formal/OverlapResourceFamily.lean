import OverlapJointWeightGlobal

/-! Joint perturbations of current resources, independent future incomes and
effective weights. Productive payoff maps and curvatures remain fixed. -/

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OverlapLocal

namespace OverlapResource
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

abbrev ResourceShock (H S : Type*) := (H → ℝ) × (H → S → ℝ) × (H → S → ℝ)

def changedEndowment (e : H → ℝ) (v : ResourceShock H S) (i : H) : ℝ := e i+v.1 i

def Admissible (D : H → Data J S) (e : H → ℝ) (v : ResourceShock H S) : Prop :=
  (∀ i, 0 < changedEndowment e v i) ∧
  (∀ i s, 0 < (D i).income s+v.2.1 i s) ∧
  (∀ i s, 0 < (D i).weight s+v.2.2 i s)

def changedData (D : H → Data J S) (e : H → ℝ) (v : ResourceShock H S)
    (h : Admissible D e v) (i : H) : Data J S :=
  { D i with
    income := fun s => (D i).income s+v.2.1 i s
    weight := fun s => (D i).weight s+v.2.2 i s
    income_pos := h.2.1 i
    weight_pos := h.2.2 i }

def futureReceipt (D : H → Data J S) (v : ResourceShock H S)
    (i : H) (a : J → ℝ) (s : S) : ℝ :=
  (D i).income s+v.2.1 i s+∑ j, (D i).payoff s j*a j

def resourceResidual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (p : ResourceShock H S × MarketState H J) : MarketState H J :=
  (fun j => (∑ i, p.2.2 i j)-supply j,
   fun i j => (budgetValue (changedEndowment e p.1) a0 p.2 i)^(-(D i).gamma)*p.2.1 j-
     ∑ s, ((D i).weight s+p.1.2.2 i s)*(D i).payoff s j*
       (futureReceipt D p.1 i (p.2.2 i) s)^(-(D i).eta s))

theorem resourceResidual_zero (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (z : MarketState H J) :
    resourceResidual D e a0 supply (0,z)=OverlapLocal.residual D e a0 supply z := by
  simp [resourceResidual,OverlapLocal.residual,choiceEquation,marginal,
    futureReceipt,consumption,changedEndowment,budgetValue]

theorem resourceResidual_eq_actual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (v : ResourceShock H S) (h : Admissible D e v) (z : MarketState H J) :
    resourceResidual D e a0 supply (v,z)=
      OverlapLocal.residual (changedData D e v h) (changedEndowment e v) a0 supply z := rfl

theorem resourceResidual_line (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (t : ℝ) (z : MarketState H J) :
    resourceResidual D e a0 supply ((0,0,fun i s => t*W i s),z)=
      affineResidual D W e a0 supply (t,z) := by
  simp [resourceResidual,affineResidual,changedEndowment,futureReceipt,consumption,budgetValue]

theorem admissible_near_zero (D : H → Data J S) (e : H → ℝ) (he : ∀ i, 0 < e i) :
    ∀ᶠ v : ResourceShock H S in 𝓝 0, Admissible D e v := by
  have hc : ∀ᶠ v : ResourceShock H S in 𝓝 0, ∀ i, 0 < changedEndowment e v i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun v : ResourceShock H S => changedEndowment e v i) := by
      unfold changedEndowment
      fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa [changedEndowment] using he i))
  have hy : ∀ᶠ v : ResourceShock H S in 𝓝 0, ∀ i s, 0 < (D i).income s+v.2.1 i s := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro s
    have hc : Continuous (fun v : ResourceShock H S => (D i).income s+v.2.1 i s) := by fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using (D i).income_pos s))
  have hw : ∀ᶠ v : ResourceShock H S in 𝓝 0, ∀ i s, 0 < (D i).weight s+v.2.2 i s := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro s
    have hc : Continuous (fun v : ResourceShock H S => (D i).weight s+v.2.2 i s) := by fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa using (D i).weight_pos s))
  filter_upwards [hc,hy,hw] with v hcv hyv hwv
  exact ⟨hcv,hyv,hwv⟩

theorem resourceResidual_contDiffAt (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ContDiffAt ℝ 1 (resourceResidual D e a0 supply) (0,(q,a0)) := by
  have hbudget : ∀ i, ContDiffAt ℝ 1
      (fun p : ResourceShock H S × MarketState H J =>
        budgetValue (changedEndowment e p.1) a0 p.2 i) (0,(q,a0)) := by
    intro i
    unfold budgetValue changedEndowment
    fun_prop
  have hfuture : ∀ i s, ContDiffAt ℝ 1
      (fun p : ResourceShock H S × MarketState H J => futureReceipt D p.1 i (p.2.2 i) s)
        (0,(q,a0)) := by
    intro i s
    unfold futureReceipt
    fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ 1
      (fun p : ResourceShock H S × MarketState H J => (∑ i, p.2.2 i j)-supply j) _
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    have hb := (hbudget i).rpow_const_of_ne (p := -(D i).gamma)
      (by simpa [changedEndowment,budget_reference] using ne_of_gt (he i))
    have hp : ContDiffAt ℝ 1 (fun p : ResourceShock H S × MarketState H J => p.2.1 j)
        (0,(q,a0)) := by fun_prop
    have hs : ∀ s, ContDiffAt ℝ 1
        (fun p : ResourceShock H S × MarketState H J => ((D i).weight s+p.1.2.2 i s)*
          (D i).payoff s j*(futureReceipt D p.1 i (p.2.2 i) s)^(-(D i).eta s)) (0,(q,a0)) := by
      intro s
      have hw : ContDiffAt ℝ 1
          (fun p : ResourceShock H S × MarketState H J => (D i).weight s+p.1.2.2 i s)
          (0,(q,a0)) := by fun_prop
      exact (hw.mul (contDiffAt_const (c := (D i).payoff s j))).mul
        ((hfuture i s).rpow_const_of_ne (by
          simpa [futureReceipt,consumption] using ne_of_gt (consumption_positive (D i) (ha0 i) s)))
    exact (hb.mul hp).sub (ContDiffAt.sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hs s))

theorem resource_partial_isInvertible [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (fderiv ℝ (resourceResidual D e a0 supply) (0,(q,a0)) ∘L
      ContinuousLinearMap.inr ℝ (ResourceShock H S) (MarketState H J)).IsInvertible := by
  have hc := resourceResidual_contDiffAt D e a0 supply q he ha0
  have hg : HasFDerivAt (fun z : MarketState H J => ((0 : ResourceShock H S),z))
      (ContinuousLinearMap.inr ℝ (ResourceShock H S) (MarketState H J)) (q,a0) :=
    (hasFDerivAt_const (0 : ResourceShock H S) (q,a0)).prodMk (hasFDerivAt_id (q,a0))
  have hh := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (q,a0) hg
  have hfixed : HasFDerivAt (OverlapLocal.residual D e a0 supply)
      (fderiv ℝ (resourceResidual D e a0 supply) (0,(q,a0)) ∘L
        ContinuousLinearMap.inr ℝ (ResourceShock H S) (MarketState H J)) (q,a0) := by
    simpa only [Function.comp_def,resourceResidual_zero] using hh
  rw [hfixed.unique
    (actual_residual_reference_strict_derivative D e a0 supply q he ha0).hasFDerivAt]
  exact referenceDerivative_isInvertible D e a0 q he ha0

theorem resource_local_root_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ∃ psi : ResourceShock H S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, resourceResidual D e a0 supply (v,psi v)=resourceResidual D e a0 supply (0,(q,a0))) ∧
      (∀ᶠ p in 𝓝 (0,(q,a0)), resourceResidual D e a0 supply p=resourceResidual D e a0 supply (0,(q,a0)) ↔
        psi p.1=p.2) := by
  have hc := resourceResidual_contDiffAt D e a0 supply q he ha0
  have hi := resource_partial_isInvertible D e a0 supply q he ha0
  exact ⟨hc.implicitFunction (by norm_num) hi,hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi,
    hc.eventually_apply_implicitFunction (by norm_num) hi,
    hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi⟩

theorem resource_local_actual_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < q j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=q j*(e i)^(-(D i).gamma)) :
    ∃ psi : ResourceShock H S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, ∃ h : Admissible D e v,
        IsEquilibrium (changedData D e v h) (changedEndowment e v) a0 supply
          (psi v).1 (budgetValue (changedEndowment e v) a0 (psi v)) (psi v).2 ∧
        resourceResidual D e a0 supply (v,psi v)=0) ∧
      (∀ᶠ p : ResourceShock H S × MarketState H J in 𝓝 (0,(q,a0)),
        ∀ h : Admissible D e p.1, ∀ c : H → ℝ,
        IsEquilibrium (changedData D e p.1 h) (changedEndowment e p.1) a0 supply p.2.1 c p.2.2 →
          p.2=psi p.1 ∧ c=budgetValue (changedEndowment e p.1) a0 p.2) := by
  classical
  obtain ⟨psi,hpsi,hcd,hroot,hgraph⟩ := resource_local_root_family D e a0 supply q he
    (fun i j => (ha0 i j).le)
  have hbase : resourceResidual D e a0 supply (0,(q,a0))=0 := by
    rw [resourceResidual_zero]
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
  have hcurrent : ∀ᶠ v in 𝓝 0, ∀ i, 0 < budgetValue (changedEndowment e v) a0 (psi v) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hb : Continuous (fun p : ResourceShock H S × MarketState H J =>
        budgetValue (changedEndowment e p.1) a0 p.2 i) := by
      unfold budgetValue changedEndowment
      fun_prop
    have hc := hb.continuousAt.comp (continuousAt_id.prodMk hcont)
    have hp : 0 < budgetValue (changedEndowment e (0 : ResourceShock H S)) a0 (psi 0) i := by
      rw [hpsi,budget_reference]
      simpa [changedEndowment] using he i
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
  have hnear : ∀ᶠ p : ResourceShock H S × MarketState H J in 𝓝 (0,(q,a0)),
      ∀ i j, 0 < p.2.2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun p : ResourceShock H S × MarketState H J => p.2.2 i j)
        (0,(q,a0)) := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (ha0 i j))
  refine ⟨psi,hpsi,hcd,?_,?_⟩
  · filter_upwards [hroot,hprice,hcurrent,hholding,admissible_near_zero D e he] with v hv hqv hcv hav hvv
    refine ⟨hvv,root_is_actual_equilibrium (changedData D e v hvv) (changedEndowment e v)
      a0 supply (psi v) hstock hqv hcv (fun i j => (hav i j).le) ?_,hv.trans hbase⟩
    rw [← resourceResidual_eq_actual]
    exact hv.trans hbase
  · filter_upwards [hgraph,hnear] with p hp hpa
    intro h c hEq
    have hr := interior_equilibrium_is_root (changedData D e p.1 h) (changedEndowment e p.1)
      a0 supply p.2.1 c p.2.2 hEq hpa
    have hraw : resourceResidual D e a0 supply p=0 := by
      rw [resourceResidual_eq_actual D e a0 supply p.1 h p.2]
      exact hr
    exact ⟨(hp.mp (hraw.trans hbase.symm)).symm,
      (equilibrium_budget_value (changedData D e p.1 h) (changedEndowment e p.1)
        a0 supply p.2.1 c p.2.2 hEq).symm⟩

end OverlapResource

#print axioms OverlapResource.resourceResidual_zero
#print axioms OverlapResource.resourceResidual_eq_actual
#print axioms OverlapResource.resourceResidual_line
#print axioms OverlapResource.admissible_near_zero
#print axioms OverlapResource.resourceResidual_contDiffAt
#print axioms OverlapResource.resource_partial_isInvertible
#print axioms OverlapResource.resource_local_root_family
#print axioms OverlapResource.resource_local_actual_family
