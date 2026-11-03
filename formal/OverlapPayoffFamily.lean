import OverlapPayoffDomain

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OverlapLocal

namespace OverlapPayoff
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

def payoffResidual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (p : PayoffShock H J S × MarketState H J) : MarketState H J :=
  (fun j => (∑ i, p.2.2 i j)-supply j,
   fun i j => (budgetValue (changedEndowment e p.1) a0 p.2 i)^(-(D i).gamma)*p.2.1 j-
     ∑ s, ((D i).weight s+p.1.1.2.2 i s)*changedPayoff D p.1 i s j*
       (futureReceipt D p.1 i (p.2.2 i) s)^(-(D i).eta s))

theorem payoffResidual_zero (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (z : MarketState H J) :
    payoffResidual D e a0 supply (0,z)=OverlapLocal.residual D e a0 supply z := by
  simp [payoffResidual,OverlapLocal.residual,choiceEquation,marginal,
    futureReceipt,changedPayoff,consumption,changedEndowment,OverlapResource.changedEndowment,budgetValue]

theorem payoffResidual_eq_actual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (v : PayoffShock H J S) (h : Admissible D e v) (z : MarketState H J) :
    payoffResidual D e a0 supply (v,z)=
      OverlapLocal.residual (changedData D e v h) (changedEndowment e v) a0 supply z := rfl

theorem payoffResidual_line (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (t : ℝ) (z : MarketState H J) :
    payoffResidual D e a0 supply (((0,0,fun i s => t*W i s),0),z)=
      affineResidual D W e a0 supply (t,z) := by
  simp [payoffResidual,affineResidual,changedEndowment,OverlapResource.changedEndowment,
    futureReceipt,changedPayoff,consumption,budgetValue]

theorem payoffResidual_contDiffAt (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ContDiffAt ℝ 1 (payoffResidual D e a0 supply) (0,(q,a0)) := by
  have hbudget : ∀ i, ContDiffAt ℝ 1
      (fun p : PayoffShock H J S × MarketState H J =>
        budgetValue (changedEndowment e p.1) a0 p.2 i) (0,(q,a0)) := by
    intro i
    unfold budgetValue changedEndowment OverlapResource.changedEndowment
    fun_prop
  have hfuture : ∀ i s, ContDiffAt ℝ 1
      (fun p : PayoffShock H J S × MarketState H J => futureReceipt D p.1 i (p.2.2 i) s)
        (0,(q,a0)) := by
    intro i s
    unfold futureReceipt changedPayoff
    fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ 1
      (fun p : PayoffShock H J S × MarketState H J => (∑ i, p.2.2 i j)-supply j) _
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    have hb := (hbudget i).rpow_const_of_ne (p := -(D i).gamma)
      (by simpa [changedEndowment,OverlapResource.changedEndowment,budget_reference] using ne_of_gt (he i))
    have hp : ContDiffAt ℝ 1 (fun p : PayoffShock H J S × MarketState H J => p.2.1 j)
        (0,(q,a0)) := by fun_prop
    have hs : ∀ s, ContDiffAt ℝ 1
        (fun p : PayoffShock H J S × MarketState H J => ((D i).weight s+p.1.1.2.2 i s)*
          changedPayoff D p.1 i s j*(futureReceipt D p.1 i (p.2.2 i) s)^(-(D i).eta s)) (0,(q,a0)) := by
      intro s
      have hw : ContDiffAt ℝ 1
          (fun p : PayoffShock H J S × MarketState H J => (D i).weight s+p.1.1.2.2 i s)
          (0,(q,a0)) := by fun_prop
      have hP : ContDiffAt ℝ 1
          (fun p : PayoffShock H J S × MarketState H J => changedPayoff D p.1 i s j)
          (0,(q,a0)) := by unfold changedPayoff; fun_prop
      exact (hw.mul hP).mul
        ((hfuture i s).rpow_const_of_ne (by
          simpa [futureReceipt,changedPayoff,consumption] using ne_of_gt (consumption_positive (D i) (ha0 i) s)))
    exact (hb.mul hp).sub (ContDiffAt.sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hs s))

theorem payoff_partial_isInvertible [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (fderiv ℝ (payoffResidual D e a0 supply) (0,(q,a0)) ∘L
      ContinuousLinearMap.inr ℝ (PayoffShock H J S) (MarketState H J)).IsInvertible := by
  have hc := payoffResidual_contDiffAt D e a0 supply q he ha0
  have hg : HasFDerivAt (fun z : MarketState H J => ((0 : PayoffShock H J S),z))
      (ContinuousLinearMap.inr ℝ (PayoffShock H J S) (MarketState H J)) (q,a0) :=
    (hasFDerivAt_const (0 : PayoffShock H J S) (q,a0)).prodMk (hasFDerivAt_id (q,a0))
  have hh := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (q,a0) hg
  have hfixed : HasFDerivAt (OverlapLocal.residual D e a0 supply)
      (fderiv ℝ (payoffResidual D e a0 supply) (0,(q,a0)) ∘L
        ContinuousLinearMap.inr ℝ (PayoffShock H J S) (MarketState H J)) (q,a0) := by
    simpa only [Function.comp_def,payoffResidual_zero] using hh
  rw [hfixed.unique
    (actual_residual_reference_strict_derivative D e a0 supply q he ha0).hasFDerivAt]
  exact referenceDerivative_isInvertible D e a0 q he ha0

theorem payoff_local_root_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ∃ psi : PayoffShock H J S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, payoffResidual D e a0 supply (v,psi v)=payoffResidual D e a0 supply (0,(q,a0))) ∧
      (∀ᶠ p in 𝓝 (0,(q,a0)), payoffResidual D e a0 supply p=payoffResidual D e a0 supply (0,(q,a0)) ↔
        psi p.1=p.2) := by
  have hc := payoffResidual_contDiffAt D e a0 supply q he ha0
  have hi := payoff_partial_isInvertible D e a0 supply q he ha0
  exact ⟨hc.implicitFunction (by norm_num) hi,hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi,
    hc.eventually_apply_implicitFunction (by norm_num) hi,
    hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi⟩

theorem payoff_local_actual_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < q j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=q j*(e i)^(-(D i).gamma)) :
    ∃ psi : PayoffShock H J S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, ∀ h : Admissible D e v,
        IsEquilibrium (changedData D e v h) (changedEndowment e v) a0 supply
          (psi v).1 (budgetValue (changedEndowment e v) a0 (psi v)) (psi v).2 ∧
        payoffResidual D e a0 supply (v,psi v)=0) ∧
      (∀ᶠ p : PayoffShock H J S × MarketState H J in 𝓝 (0,(q,a0)),
        ∀ h : Admissible D e p.1, ∀ c : H → ℝ,
        IsEquilibrium (changedData D e p.1 h) (changedEndowment e p.1) a0 supply p.2.1 c p.2.2 →
          p.2=psi p.1 ∧ c=budgetValue (changedEndowment e p.1) a0 p.2) := by
  classical
  obtain ⟨psi,hpsi,hcd,hroot,hgraph⟩ := payoff_local_root_family D e a0 supply q he
    (fun i j => (ha0 i j).le)
  have hbase : payoffResidual D e a0 supply (0,(q,a0))=0 := by
    rw [payoffResidual_zero]
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
    have hb : Continuous (fun p : PayoffShock H J S × MarketState H J =>
        budgetValue (changedEndowment e p.1) a0 p.2 i) := by
      unfold budgetValue changedEndowment OverlapResource.changedEndowment
      fun_prop
    have hc := hb.continuousAt.comp (continuousAt_id.prodMk hcont)
    have hp : 0 < budgetValue (changedEndowment e (0 : PayoffShock H J S)) a0 (psi 0) i := by
      rw [hpsi,budget_reference]
      simpa [changedEndowment,OverlapResource.changedEndowment] using he i
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
  have hnear : ∀ᶠ p : PayoffShock H J S × MarketState H J in 𝓝 (0,(q,a0)),
      ∀ i j, 0 < p.2.2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun p : PayoffShock H J S × MarketState H J => p.2.2 i j)
        (0,(q,a0)) := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (ha0 i j))
  refine ⟨psi,hpsi,hcd,?_,?_⟩
  · filter_upwards [hroot,hprice,hcurrent,hholding] with v hv hqv hcv hav
    intro hvv
    refine ⟨root_is_actual_equilibrium (changedData D e v hvv) (changedEndowment e v)
      a0 supply (psi v) hstock hqv hcv (fun i j => (hav i j).le) ?_,hv.trans hbase⟩
    rw [← payoffResidual_eq_actual]
    exact hv.trans hbase
  · filter_upwards [hgraph,hnear] with p hp hpa
    intro h c hEq
    have hr := interior_equilibrium_is_root (changedData D e p.1 h) (changedEndowment e p.1)
      a0 supply p.2.1 c p.2.2 hEq hpa
    have hraw : payoffResidual D e a0 supply p=0 := by
      rw [payoffResidual_eq_actual D e a0 supply p.1 h p.2]
      exact hr
    exact ⟨(hp.mp (hraw.trans hbase.symm)).symm,
      (equilibrium_budget_value (changedData D e p.1 h) (changedEndowment e p.1)
        a0 supply p.2.1 c p.2.2 hEq).symm⟩

end OverlapPayoff

#print axioms OverlapPayoff.payoffResidual_zero
#print axioms OverlapPayoff.payoffResidual_eq_actual
#print axioms OverlapPayoff.payoffResidual_line
#print axioms OverlapPayoff.payoffResidual_contDiffAt
#print axioms OverlapPayoff.payoff_partial_isInvertible
#print axioms OverlapPayoff.payoff_local_root_family
#print axioms OverlapPayoff.payoff_local_actual_family
