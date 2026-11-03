import OverlapEulerDerivative
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
Joint implicit-function construction for smooth affine state-weight shocks.
Physical resources, payoffs and initial ownership are fixed. Positivity and
actual global household optimality must be retained in the economic lift.
-/

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive

namespace OverlapLocal
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

def affineData (D : H → Data J S) (W : H → S → ℝ) (t : ℝ)
    (hw : ∀ i s, 0 < (D i).weight s+t*W i s) (i : H) : Data J S :=
  { D i with weight := fun s => (D i).weight s+t*W i s, weight_pos := hw i }

def affineResidual (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (p : ℝ × MarketState H J) : MarketState H J :=
  (fun j => (∑ i, p.2.2 i j)-supply j,
   fun i j => (budgetValue e a0 p.2 i)^(-(D i).gamma)*p.2.1 j-
     ∑ s, ((D i).weight s+p.1*W i s)*(D i).payoff s j*
       (consumption (D i) (p.2.2 i) s)^(-(D i).eta s))

theorem affineResidual_zero (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (z : MarketState H J) :
    affineResidual D W e a0 supply (0,z)=residual D e a0 supply z := by
  simp [affineResidual,residual,choiceEquation,marginal]

theorem affineResidual_eq_actual (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ) (t : ℝ)
    (hw : ∀ i s, 0 < (D i).weight s+t*W i s) (z : MarketState H J) :
    affineResidual D W e a0 supply (t,z)=residual (affineData D W t hw) e a0 supply z := rfl

theorem affineResidual_contDiffAt (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ContDiffAt ℝ 1 (affineResidual D W e a0 supply) (0,(q,a0)) := by
  have hbudget : ∀ i, ContDiffAt ℝ 1
      (fun p : ℝ × MarketState H J => budgetValue e a0 p.2 i) (0,(q,a0)) := by
    intro i
    unfold budgetValue
    fun_prop
  have hfuture : ∀ i s, ContDiffAt ℝ 1
      (fun p : ℝ × MarketState H J => consumption (D i) (p.2.2 i) s) (0,(q,a0)) := by
    intro i s
    unfold consumption
    fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ 1 (fun p : ℝ × MarketState H J => (∑ i, p.2.2 i j)-supply j) _
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    have hb := (hbudget i).rpow_const_of_ne (p := -(D i).gamma)
      (by rw [budget_reference]; exact ne_of_gt (he i))
    have hp : ContDiffAt ℝ 1 (fun p : ℝ × MarketState H J => p.2.1 j) (0,(q,a0)) := by
      fun_prop
    have hs : ∀ s, ContDiffAt ℝ 1
        (fun p : ℝ × MarketState H J => ((D i).weight s+p.1*W i s)*(D i).payoff s j*
          (consumption (D i) (p.2.2 i) s)^(-(D i).eta s)) (0,(q,a0)) := by
      intro s
      have hw : ContDiffAt ℝ 1
          (fun p : ℝ × MarketState H J => (D i).weight s+p.1*W i s) (0,(q,a0)) := by
        fun_prop
      exact (hw.mul (contDiffAt_const (c := (D i).payoff s j))).mul
        ((hfuture i s).rpow_const_of_ne (ne_of_gt (consumption_positive (D i) (ha0 i) s)))
    exact (hb.mul hp).sub (ContDiffAt.sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hs s))

theorem affine_partial_isInvertible [Nonempty H]
    (D : H → Data J S) (W : H → S → ℝ) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (fderiv ℝ (affineResidual D W e a0 supply) (0,(q,a0)) ∘L
      ContinuousLinearMap.inr ℝ ℝ (MarketState H J)).IsInvertible := by
  have hc := affineResidual_contDiffAt D W e a0 supply q he ha0
  have hg : HasFDerivAt (fun z : MarketState H J => ((0 : ℝ),z))
      (ContinuousLinearMap.inr ℝ ℝ (MarketState H J)) (q,a0) := by
    exact (hasFDerivAt_const (0 : ℝ) (q,a0)).prodMk (hasFDerivAt_id (q,a0))
  have hh := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (q,a0) hg
  have hfixed : HasFDerivAt (residual D e a0 supply)
      (fderiv ℝ (affineResidual D W e a0 supply) (0,(q,a0)) ∘L
        ContinuousLinearMap.inr ℝ ℝ (MarketState H J)) (q,a0) := by
    simpa only [Function.comp_def,affineResidual_zero] using hh
  rw [hfixed.unique
    (actual_residual_reference_strict_derivative D e a0 supply q he ha0).hasFDerivAt]
  exact referenceDerivative_isInvertible D e a0 q he ha0

theorem affine_local_root_family [Nonempty H]
    (D : H → Data J S) (W : H → S → ℝ) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ∃ psi : ℝ → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ t in 𝓝 0, affineResidual D W e a0 supply (t,psi t)=
        affineResidual D W e a0 supply (0,(q,a0))) ∧
      (∀ᶠ p in 𝓝 (0,(q,a0)), affineResidual D W e a0 supply p=
        affineResidual D W e a0 supply (0,(q,a0)) ↔ psi p.1=p.2) := by
  have hc := affineResidual_contDiffAt D W e a0 supply q he ha0
  have hi := affine_partial_isInvertible D W e a0 supply q he ha0
  exact ⟨hc.implicitFunction (by norm_num) hi,
    hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi,
    hc.eventually_apply_implicitFunction (by norm_num) hi,
    hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi⟩

theorem equilibrium_budget_value (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ) (c : H → ℝ) (a : H → J → ℝ)
    (hEq : IsEquilibrium D e a0 supply q c a) :
    budgetValue e a0 (q,a)=c := by
  funext i
  have h1 := OwnershipUniform.budget_exhausted hEq i
  have h2 := reconstructed_budget e a0 (q,a) i
  linarith

theorem interior_equilibrium_is_root (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ) (c : H → ℝ) (a : H → J → ℝ)
    (hEq : IsEquilibrium D e a0 supply q c a) (ha : ∀ i j, 0 < a i j) :
    residual D e a0 supply (q,a)=0 := by
  apply Prod.ext
  · funext j
    change (∑ i, a i j)-supply j=0
    rw [hEq.ownership_clears j,sub_self]
  · funext i j
    change (budgetValue e a0 (q,a) i)^(-(D i).gamma)*q j-marginal (D i) (a i) j=0
    rw [equilibrium_budget_value D e a0 supply q c a hEq,
      OwnershipUniform.owned_asset_euler hEq i j (ha i j)]
    ring

theorem affine_local_actual_family [Nonempty H]
    (D : H → Data J S) (W : H → S → ℝ) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < q j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=q j*(e i)^(-(D i).gamma)) :
    ∃ psi : ℝ → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ t in 𝓝 0, ∃ hw : ∀ i s, 0 < (D i).weight s+t*W i s,
        IsEquilibrium (affineData D W t hw) e a0 supply
          (psi t).1 (budgetValue e a0 (psi t)) (psi t).2 ∧
          affineResidual D W e a0 supply (t,psi t)=0) ∧
      (∀ᶠ p : ℝ × MarketState H J in 𝓝 (0,(q,a0)),
        ∀ hw : ∀ i s, 0 < (D i).weight s+p.1*W i s,
        ∀ c : H → ℝ, IsEquilibrium (affineData D W p.1 hw) e a0 supply p.2.1 c p.2.2 →
          p.2=psi p.1 ∧ c=budgetValue e a0 p.2) := by
  classical
  obtain ⟨psi,hpsi,hcd,hroot,hgraph⟩ := affine_local_root_family D W e a0 supply q he
    (fun i j => (ha0 i j).le)
  have hbase : affineResidual D W e a0 supply (0,(q,a0))=0 := by
    rw [affineResidual_zero]
    apply Prod.ext
    · funext j
      change (∑ i, a0 i j)-supply j=0
      rw [hstock j,sub_self]
    · funext i j
      change (budgetValue e a0 (q,a0) i)^(-(D i).gamma)*q j-
        marginal (D i) (a0 i) j=0
      rw [budget_reference,heuler i j]
      ring
  have hcont : ContinuousAt psi 0 := hcd.continuousAt
  have hprice : ∀ᶠ t in 𝓝 0, ∀ j, 0 < (psi t).1 j := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun t => (psi t).1 j) 0 :=
      (continuous_apply j).continuousAt.comp hcont.fst
    have hp : 0 < (psi 0).1 j := by rw [hpsi]; exact hq j
    exact hc.eventually (Ioi_mem_nhds hp)
  have hcurrent : ∀ᶠ t in 𝓝 0, ∀ i, 0 < budgetValue e a0 (psi t) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hb : Continuous (fun z : MarketState H J => budgetValue e a0 z i) := by
      unfold budgetValue
      fun_prop
    have hc := hb.continuousAt.comp hcont
    have hp : 0 < budgetValue e a0 (psi 0) i := by rw [hpsi,budget_reference]; exact he i
    exact hc.eventually (Ioi_mem_nhds hp)
  have hholding : ∀ᶠ t in 𝓝 0, ∀ i j, 0 < (psi t).2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun t => (psi t).2 i j) 0 :=
      (continuous_apply j).continuousAt.comp
        ((continuous_apply i).continuousAt.comp hcont.snd)
    have hp : 0 < (psi 0).2 i j := by rw [hpsi]; exact ha0 i j
    exact hc.eventually (Ioi_mem_nhds hp)
  have hweights : ∀ᶠ t : ℝ in 𝓝 0, ∀ i s, 0 < (D i).weight s+t*W i s := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro s
    have hc : ContinuousAt (fun t : ℝ => (D i).weight s+t*W i s) 0 := by fun_prop
    have hp : 0 < (D i).weight s+(0 : ℝ)*W i s := by simpa using (D i).weight_pos s
    exact hc.eventually (Ioi_mem_nhds hp)
  have hnear : ∀ᶠ p : ℝ × MarketState H J in 𝓝 (0,(q,a0)), ∀ i j, 0 < p.2.2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun p : ℝ × MarketState H J => p.2.2 i j) (0,(q,a0)) := by
      fun_prop
    exact hc.eventually (Ioi_mem_nhds (ha0 i j))
  refine ⟨psi,hpsi,hcd,?_,?_⟩
  · filter_upwards [hroot,hprice,hcurrent,hholding,hweights] with t ht hqt hct hat hwt
    refine ⟨hwt,root_is_actual_equilibrium (affineData D W t hwt) e a0 supply (psi t)
      hstock hqt hct (fun i j => (hat i j).le) ?_,ht.trans hbase⟩
    rw [← affineResidual_eq_actual]
    exact ht.trans hbase
  · filter_upwards [hgraph,hnear] with p hp hpa
    intro hw c hEq
    have hr := interior_equilibrium_is_root (affineData D W p.1 hw) e a0 supply
      p.2.1 c p.2.2 hEq hpa
    have hraw : affineResidual D W e a0 supply p=0 := by
      rw [affineResidual_eq_actual D W e a0 supply p.1 hw p.2]
      exact hr
    exact ⟨(hp.mp (hraw.trans hbase.symm)).symm,
      (equilibrium_budget_value (affineData D W p.1 hw) e a0 supply p.2.1 c p.2.2 hEq).symm⟩

def interiorShock (i : Fin 2) (s : Fin 4) : ℝ :=
  if i=1 ∧ s=0 then OwnershipSupported.InteriorControl.weight i s else 0

theorem interior_nonzero_root_trades (t : ℝ) (z : MarketState (Fin 2) (Fin 2))
    (hroot : affineResidual OwnershipSupported.InteriorControl.D interiorShock
      OwnershipSupported.InteriorControl.endowment OwnershipSupported.InteriorControl.initial
      OwnershipSupported.CornerControl.supply (t,z)=0) (ht : t ≠ 0) :
    z.2 ≠ OwnershipSupported.InteriorControl.initial := by
  intro ha
  have hz : z=(z.1,OwnershipSupported.InteriorControl.initial) := Prod.ext rfl ha
  rw [hz] at hroot
  have h0 := congrFun (congrFun (congrArg Prod.snd hroot) 0) 0
  have h1 := congrFun (congrFun (congrArg Prod.snd hroot) 1) 0
  simp only [affineResidual,budget_reference,OwnershipSupported.InteriorControl.D,
    OwnershipSupported.CornerControl.D,OwnershipMultiplicity.negative_nat_power] at h0 h1
  norm_num [consumption,OwnershipSupported.InteriorControl.initial,
    OwnershipSupported.InteriorControl.endowment,OwnershipSupported.InteriorControl.weight,
    OwnershipSupported.InteriorControl.referenceReceipt,OwnershipSupported.InteriorControl.baseMass,
    OwnershipSupported.CornerControl.gammaNat,OwnershipMultiplicity.payoff,
    interiorShock,Fin.sum_univ_succ] at h0 h1
  exact ht (by nlinarith [h0,h1])

theorem interior_actual_trading_family :
    ∃ psi : ℝ → MarketState (Fin 2) (Fin 2),
      psi 0=(OwnershipSupported.CornerControl.qstar,OwnershipSupported.InteriorControl.initial) ∧
      ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ t in 𝓝 0, ∃ hw : ∀ i s,
        0 < (OwnershipSupported.InteriorControl.D i).weight s+t*interiorShock i s,
        IsEquilibrium (affineData OwnershipSupported.InteriorControl.D interiorShock t hw)
          OwnershipSupported.InteriorControl.endowment OwnershipSupported.InteriorControl.initial
          OwnershipSupported.CornerControl.supply (psi t).1
          (budgetValue OwnershipSupported.InteriorControl.endowment
            OwnershipSupported.InteriorControl.initial (psi t)) (psi t).2 ∧
        (t ≠ 0 → (psi t).2 ≠ OwnershipSupported.InteriorControl.initial)) := by
  have heuler : ∀ i j, marginal (OwnershipSupported.InteriorControl.D i)
      (OwnershipSupported.InteriorControl.initial i) j=
      OwnershipSupported.CornerControl.qstar j*
        (OwnershipSupported.InteriorControl.endowment i)^(-(OwnershipSupported.InteriorControl.D i).gamma) := by
    intro i j
    have hh := (OwnershipSupported.InteriorControl.primitive_support i j).2
    have hz := (mul_eq_zero.mp hh).resolve_left
      (ne_of_gt (OwnershipSupported.InteriorControl.initial_interior i j))
    linarith
  obtain ⟨psi,hpsi,hcd,hcert,_⟩ := affine_local_actual_family
    OwnershipSupported.InteriorControl.D interiorShock
    OwnershipSupported.InteriorControl.endowment OwnershipSupported.InteriorControl.initial
    OwnershipSupported.CornerControl.supply OwnershipSupported.CornerControl.qstar
    (by intro i; norm_num [OwnershipSupported.InteriorControl.endowment])
    OwnershipSupported.InteriorControl.initial_interior
    (by intro j; fin_cases j <;> norm_num [OwnershipSupported.CornerControl.qstar])
    (by intro j; fin_cases j <;>
      norm_num [OwnershipSupported.InteriorControl.initial,OwnershipSupported.CornerControl.supply,
        Fin.sum_univ_succ]) heuler
  refine ⟨psi,hpsi,hcd,?_⟩
  filter_upwards [hcert] with t ht
  obtain ⟨hw,hEq,hr⟩ := ht
  exact ⟨hw,hEq,fun hne => interior_nonzero_root_trades t (psi t) hr hne⟩

end OverlapLocal

#print axioms OverlapLocal.affineResidual_zero
#print axioms OverlapLocal.affineResidual_eq_actual
#print axioms OverlapLocal.affineResidual_contDiffAt
#print axioms OverlapLocal.affine_partial_isInvertible
#print axioms OverlapLocal.affine_local_root_family
#print axioms OverlapLocal.equilibrium_budget_value
#print axioms OverlapLocal.interior_equilibrium_is_root
#print axioms OverlapLocal.affine_local_actual_family
#print axioms OverlapLocal.interior_nonzero_root_trades
#print axioms OverlapLocal.interior_actual_trading_family
