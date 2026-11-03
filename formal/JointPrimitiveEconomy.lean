import NormalizedCRRAPreferences

/-! One joint CRRA-primitive market theorem. Sources are not accepted until
the compiler, axiom audits and bound receipts pass. See THEOREM.md. -/

noncomputable section
open scoped BigOperators Topology
open Filter OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open Set OwnershipSupported OverlapLocal OverlapStability

namespace OverlapPrimitive
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

abbrev PrimitiveShock (H J S : Type*) := OverlapPayoff.PayoffShock H J S ×
  (H → J → ℝ) × (H → ℝ) × (H → S → ℝ)

def currentResources (e : H → ℝ) (v : PrimitiveShock H J S) : H → ℝ :=
  OverlapPayoff.changedEndowment e v.1

def changedPayoff (D : H → Data J S) (v : PrimitiveShock H J S) : H → S → J → ℝ :=
  OverlapPayoff.changedPayoff D v.1

def futureReceipt (D : H → Data J S) (v : PrimitiveShock H J S)
    (i : H) (a : J → ℝ) (s : S) : ℝ :=
  OverlapPayoff.futureReceipt D v.1 i a s

def initialPortfolio (a0 : H → J → ℝ) (v : PrimitiveShock H J S) (i : H) (j : J) : ℝ :=
  a0 i j+v.2.1 i j

def assetSupply (supply : J → ℝ) (v : PrimitiveShock H J S) (j : J) : ℝ :=
  supply j+∑ i, v.2.1 i j

def currentCurvature (D : H → Data J S) (v : PrimitiveShock H J S) (i : H) : ℝ :=
  (D i).gamma+v.2.2.1 i

def futureCurvature (D : H → Data J S) (v : PrimitiveShock H J S) (i : H) (s : S) : ℝ :=
  (D i).eta s+v.2.2.2 i s

def Nonnegative (D : H → Data J S) (v : PrimitiveShock H J S) : Prop :=
  OverlapPayoff.Nonnegative D v.1

def Admissible (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (v : PrimitiveShock H J S) : Prop :=
  OverlapPayoff.Admissible D e v.1 ∧
  (∀ i j, 0 ≤ initialPortfolio a0 v i j) ∧
  (∀ i, 0 < currentCurvature D v i) ∧ (∀ i s, 0 < futureCurvature D v i s)

def changedData (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (v : PrimitiveShock H J S) (h : Admissible D e a0 v) (i : H) : Data J S :=
  { OverlapPayoff.changedData D e v.1 h.1 i with
    gamma := currentCurvature D v i
    eta := futureCurvature D v i
    gamma_pos := h.2.2.1 i
    eta_pos := h.2.2.2 i }

def currentBudget (e : H → ℝ) (a0 : H → J → ℝ) (v : PrimitiveShock H J S)
    (z : MarketState H J) : H → ℝ :=
  budgetValue (currentResources e v) (initialPortfolio a0 v) z

omit [Fintype J] [Fintype S] in
theorem inventory_consistency (a0 : H → J → ℝ) (supply : J → ℝ)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (v : PrimitiveShock H J S) :
    ∀ j, ∑ i, initialPortfolio a0 v i j=assetSupply supply v j := by
  intro j
  simp only [initialPortfolio,assetSupply,Finset.sum_add_distrib,hstock j]

theorem admissible_near_zero (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) :
    ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, Nonnegative D v → Admissible D e a0 v := by
  have hp : ∀ᶠ v : PrimitiveShock H J S in 𝓝 0,
      OverlapPayoff.Nonnegative D v.1 → OverlapPayoff.Admissible D e v.1 :=
    (continuous_fst.tendsto (0 : PrimitiveShock H J S)).eventually
      (OverlapPayoff.admissible_near_zero D e he)
  have ha : ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, ∀ i j, 0 < initialPortfolio a0 v i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun v : PrimitiveShock H J S => initialPortfolio a0 v i j) := by
      unfold initialPortfolio
      fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa [initialPortfolio] using ha0 i j))
  have hg : ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, ∀ i, 0 < currentCurvature D v i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun v : PrimitiveShock H J S => currentCurvature D v i) := by
      unfold currentCurvature
      fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa [currentCurvature] using (D i).gamma_pos))
  have heta : ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, ∀ i s, 0 < futureCurvature D v i s := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro s
    have hc : Continuous (fun v : PrimitiveShock H J S => futureCurvature D v i s) := by
      unfold futureCurvature
      fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (by simpa [futureCurvature] using (D i).eta_pos s))
  filter_upwards [hp,ha,hg,heta] with v hpv hav hgv hetav
  intro hnonneg
  exact ⟨hpv hnonneg,fun i j => (hav i j).le,hgv,hetav⟩


def primitiveResidual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (p : PrimitiveShock H J S × MarketState H J) : MarketState H J :=
  (fun j => (∑ i, p.2.2 i j)-assetSupply supply p.1 j,
   fun i j => (currentBudget e a0 p.1 p.2 i)^(-currentCurvature D p.1 i)*p.2.1 j-
     ∑ s, ((D i).weight s+p.1.1.1.2.2 i s)*OverlapPayoff.changedPayoff D p.1.1 i s j*
       (OverlapPayoff.futureReceipt D p.1.1 i (p.2.2 i) s)^(-futureCurvature D p.1 i s))

theorem primitiveResidual_zero (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (z : MarketState H J) :
    primitiveResidual D e a0 supply (0,z)=OverlapLocal.residual D e a0 supply z := by
  simp [primitiveResidual,OverlapLocal.residual,choiceEquation,marginal,
    OverlapPayoff.futureReceipt,OverlapPayoff.changedPayoff,consumption,
    currentBudget,currentResources,initialPortfolio,assetSupply,currentCurvature,
    futureCurvature,OverlapPayoff.changedEndowment,OverlapResource.changedEndowment,budgetValue]

theorem primitiveResidual_eq_actual (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ)
    (supply : J → ℝ) (v : PrimitiveShock H J S) (h : Admissible D e a0 v) (z : MarketState H J) :
    primitiveResidual D e a0 supply (v,z)=
      OverlapLocal.residual (changedData D e a0 v h) (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v) z := rfl

theorem primitiveResidual_contDiffAt (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ContDiffAt ℝ 1 (primitiveResidual D e a0 supply) (0,(q,a0)) := by
  have hbudget : ∀ i, ContDiffAt ℝ 1
      (fun p : PrimitiveShock H J S × MarketState H J =>
        currentBudget e a0 p.1 p.2 i) (0,(q,a0)) := by
    intro i
    unfold currentBudget budgetValue currentResources initialPortfolio OverlapPayoff.changedEndowment OverlapResource.changedEndowment
    fun_prop
  have hfuture : ∀ i s, ContDiffAt ℝ 1
      (fun p : PrimitiveShock H J S × MarketState H J => OverlapPayoff.futureReceipt D p.1.1 i (p.2.2 i) s)
        (0,(q,a0)) := by
    intro i s
    unfold OverlapPayoff.futureReceipt OverlapPayoff.changedPayoff
    fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ 1
      (fun p : PrimitiveShock H J S × MarketState H J => (∑ i, p.2.2 i j)-assetSupply supply p.1 j) _
    unfold assetSupply
    fun_prop
  · apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    have hg : ContDiffAt ℝ 1 (fun p : PrimitiveShock H J S × MarketState H J =>
        -currentCurvature D p.1 i) (0,(q,a0)) := by unfold currentCurvature; fun_prop
    have hb := (hbudget i).rpow hg (by
      simpa [currentBudget,currentResources,initialPortfolio,budgetValue,
        OverlapPayoff.changedEndowment,OverlapResource.changedEndowment] using ne_of_gt (he i))
    have hp : ContDiffAt ℝ 1 (fun p : PrimitiveShock H J S × MarketState H J => p.2.1 j)
        (0,(q,a0)) := by fun_prop
    have hs : ∀ s, ContDiffAt ℝ 1
        (fun p : PrimitiveShock H J S × MarketState H J => ((D i).weight s+p.1.1.1.2.2 i s)*
          OverlapPayoff.changedPayoff D p.1.1 i s j*(OverlapPayoff.futureReceipt D p.1.1 i (p.2.2 i) s)^(-futureCurvature D p.1 i s)) (0,(q,a0)) := by
      intro s
      have hw : ContDiffAt ℝ 1
          (fun p : PrimitiveShock H J S × MarketState H J => (D i).weight s+p.1.1.1.2.2 i s)
          (0,(q,a0)) := by fun_prop
      have hP : ContDiffAt ℝ 1
          (fun p : PrimitiveShock H J S × MarketState H J => OverlapPayoff.changedPayoff D p.1.1 i s j)
          (0,(q,a0)) := by unfold OverlapPayoff.changedPayoff; fun_prop
      have heta : ContDiffAt ℝ 1 (fun p : PrimitiveShock H J S × MarketState H J =>
          -futureCurvature D p.1 i s) (0,(q,a0)) := by unfold futureCurvature; fun_prop
      exact (hw.mul hP).mul
        ((hfuture i s).rpow heta (by
          simpa [OverlapPayoff.futureReceipt,OverlapPayoff.changedPayoff,consumption]
            using ne_of_gt (consumption_positive (D i) (ha0 i) s)))
    exact (hb.mul hp).sub (ContDiffAt.sum (fun s (_ : s ∈ (Finset.univ : Finset S)) => hs s))

theorem primitive_partial_isInvertible [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    (fderiv ℝ (primitiveResidual D e a0 supply) (0,(q,a0)) ∘L
      ContinuousLinearMap.inr ℝ (PrimitiveShock H J S) (MarketState H J)).IsInvertible := by
  have hc := primitiveResidual_contDiffAt D e a0 supply q he ha0
  have hg : HasFDerivAt (fun z : MarketState H J => ((0 : PrimitiveShock H J S),z))
      (ContinuousLinearMap.inr ℝ (PrimitiveShock H J S) (MarketState H J)) (q,a0) :=
    (hasFDerivAt_const (0 : PrimitiveShock H J S) (q,a0)).prodMk (hasFDerivAt_id (q,a0))
  have hh := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp (q,a0) hg
  have hfixed : HasFDerivAt (OverlapLocal.residual D e a0 supply)
      (fderiv ℝ (primitiveResidual D e a0 supply) (0,(q,a0)) ∘L
        ContinuousLinearMap.inr ℝ (PrimitiveShock H J S) (MarketState H J)) (q,a0) := by
    simpa only [Function.comp_def,primitiveResidual_zero] using hh
  rw [hfixed.unique
    (actual_residual_reference_strict_derivative D e a0 supply q he ha0).hasFDerivAt]
  exact referenceDerivative_isInvertible D e a0 q he ha0

theorem primitive_local_root_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j) :
    ∃ psi : PrimitiveShock H J S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, primitiveResidual D e a0 supply (v,psi v)=primitiveResidual D e a0 supply (0,(q,a0))) ∧
      (∀ᶠ p in 𝓝 (0,(q,a0)), primitiveResidual D e a0 supply p=primitiveResidual D e a0 supply (0,(q,a0)) ↔
        psi p.1=p.2) := by
  have hc := primitiveResidual_contDiffAt D e a0 supply q he ha0
  have hi := primitive_partial_isInvertible D e a0 supply q he ha0
  exact ⟨hc.implicitFunction (by norm_num) hi,hc.implicitFunction_apply_self (by norm_num) hi,
    hc.contDiffAt_implicitFunction (by norm_num) hi,
    hc.eventually_apply_implicitFunction (by norm_num) hi,
    hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hi⟩

theorem primitive_local_actual_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply q : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < q j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=q j*(e i)^(-(D i).gamma)) :
    ∃ psi : PrimitiveShock H J S → MarketState H J, psi 0=(q,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v,
        IsEquilibrium (changedData D e a0 v h) (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v)
          (psi v).1 (currentBudget e a0 v (psi v)) (psi v).2 ∧
        primitiveResidual D e a0 supply (v,psi v)=0) ∧
      (∀ᶠ p : PrimitiveShock H J S × MarketState H J in 𝓝 (0,(q,a0)),
        ∀ h : Admissible D e a0 p.1, ∀ c : H → ℝ,
        IsEquilibrium (changedData D e a0 p.1 h) (currentResources e p.1) (initialPortfolio a0 p.1) (assetSupply supply p.1) p.2.1 c p.2.2 →
          p.2=psi p.1 ∧ c=currentBudget e a0 p.1 p.2) := by
  classical
  obtain ⟨psi,hpsi,hcd,hroot,hgraph⟩ := primitive_local_root_family D e a0 supply q he
    (fun i j => (ha0 i j).le)
  have hbase : primitiveResidual D e a0 supply (0,(q,a0))=0 := by
    rw [primitiveResidual_zero]
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
  have hcurrent : ∀ᶠ v in 𝓝 0, ∀ i, 0 < currentBudget e a0 v (psi v) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hb : Continuous (fun p : PrimitiveShock H J S × MarketState H J =>
        currentBudget e a0 p.1 p.2 i) := by
      unfold currentBudget budgetValue currentResources initialPortfolio OverlapPayoff.changedEndowment OverlapResource.changedEndowment
      fun_prop
    have hc := hb.continuousAt.comp (continuousAt_id.prodMk hcont)
    have hp : 0 < currentBudget e a0 (0 : PrimitiveShock H J S) (psi 0) i := by
      rw [hpsi]
      simpa [currentBudget,currentResources,initialPortfolio,budgetValue,
        OverlapPayoff.changedEndowment,OverlapResource.changedEndowment] using he i
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
  have hnear : ∀ᶠ p : PrimitiveShock H J S × MarketState H J in 𝓝 (0,(q,a0)),
      ∀ i j, 0 < p.2.2 i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun p : PrimitiveShock H J S × MarketState H J => p.2.2 i j)
        (0,(q,a0)) := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (ha0 i j))
  refine ⟨psi,hpsi,hcd,?_,?_⟩
  · filter_upwards [hroot,hprice,hcurrent,hholding] with v hv hqv hcv hav
    intro hvv
    refine ⟨root_is_actual_equilibrium (changedData D e a0 v hvv) (currentResources e v)
      (initialPortfolio a0 v) (assetSupply supply v) (psi v)
      (inventory_consistency a0 supply hstock v) hqv hcv (fun i j => (hav i j).le) ?_,hv.trans hbase⟩
    rw [← primitiveResidual_eq_actual]
    exact hv.trans hbase
  · filter_upwards [hgraph,hnear] with p hp hpa
    intro h c hEq
    have hr := interior_equilibrium_is_root (changedData D e a0 p.1 h) (currentResources e p.1)
      (initialPortfolio a0 p.1) (assetSupply supply p.1) p.2.1 c p.2.2 hEq hpa
    have hraw : primitiveResidual D e a0 supply p=0 := by
      rw [primitiveResidual_eq_actual D e a0 supply p.1 h p.2]
      exact hr
    exact ⟨(hp.mp (hraw.trans hbase.symm)).symm,
      (equilibrium_budget_value (changedData D e a0 p.1 h) (currentResources e p.1)
        (initialPortfolio a0 p.1) (assetSupply supply p.1) p.2.1 c p.2.2 hEq).symm⟩


omit [Fintype H] [Fintype J] [Fintype S] in
theorem endowment_tendsto (e : H → ℝ) {v : ℕ → PrimitiveShock H J S}
    (hv : Tendsto v atTop (𝓝 0)) (i : H) :
    Tendsto (fun n => currentResources e (v n) i) atTop (𝓝 (e i)) := by
  exact OverlapPayoff.endowment_tendsto e hv.fst_nhds i

omit [Fintype H] [Fintype S] in
theorem primitive_coefficient_tendsto (D : H → Data J S) {v : ℕ → PrimitiveShock H J S}
    (hv : Tendsto v atTop (𝓝 0)) (i : H) (s : S) (j : J) :
    Tendsto (fun n => changedPayoff D (v n) i s j) atTop (𝓝 ((D i).payoff s j)) := by
  exact OverlapPayoff.payoff_coefficient_tendsto D hv.fst_nhds i s j

omit [Fintype H] [Fintype S] in
theorem futureReceipt_tendsto (D : H → Data J S) (i : H)
    {v : ℕ → PrimitiveShock H J S} {an : ℕ → J → ℝ} {a : J → ℝ}
    (hv : Tendsto v atTop (𝓝 0))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) (s : S) :
    Tendsto (fun n => futureReceipt D (v n) i (an n) s) atTop
      (𝓝 (consumption (D i) a s)) := by
  exact OverlapPayoff.futureReceipt_tendsto D i hv.fst_nhds han s

omit [Fintype H] [Fintype J] [Fintype S] in
theorem initial_tendsto (a0 : H → J → ℝ) {v : ℕ → PrimitiveShock H J S}
    (hv : Tendsto v atTop (𝓝 0)) (i : H) (j : J) :
    Tendsto (fun n => initialPortfolio a0 (v n) i j) atTop (𝓝 (a0 i j)) := by
  have hh := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.snd_nhds.fst_nhds) i)) j
  simpa [initialPortfolio] using tendsto_const_nhds.add hh

omit [Fintype J] [Fintype S] in
theorem supply_tendsto (supply : J → ℝ) {v : ℕ → PrimitiveShock H J S}
    (hv : Tendsto v atTop (𝓝 0)) (j : J) :
    Tendsto (fun n => assetSupply supply (v n) j) atTop (𝓝 (supply j)) := by
  have hh : Tendsto (fun n => ∑ i, (v n).2.1 i j) atTop (𝓝 (∑ i : H, (0 : ℝ))) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.snd_nhds.fst_nhds) i)) j)
  simpa [assetSupply] using tendsto_const_nhds.add hh

omit [Fintype H] [Fintype S] in
theorem gamma_tendsto (D : H → Data J S) {v : ℕ → PrimitiveShock H J S}
    (hv : Tendsto v atTop (𝓝 0)) (i : H) :
    Tendsto (fun n => currentCurvature D (v n) i) atTop (𝓝 ((D i).gamma)) := by
  have hh := (tendsto_pi_nhds.mp hv.snd_nhds.snd_nhds.fst_nhds) i
  simpa [currentCurvature] using tendsto_const_nhds.add hh

omit [Fintype H] [Fintype S] in
theorem eta_tendsto (D : H → Data J S) {v : ℕ → PrimitiveShock H J S}
    (hv : Tendsto v atTop (𝓝 0)) (i : H) (s : S) :
    Tendsto (fun n => futureCurvature D (v n) i s) atTop (𝓝 ((D i).eta s)) := by
  have hh := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.snd_nhds.snd_nhds.snd_nhds) i)) s
  simpa [futureCurvature] using tendsto_const_nhds.add hh

omit [Fintype H] in
theorem primitive_value_tendsto (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (i : H)
    (v : ℕ → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    {cn : ℕ → ℝ} {an : ℕ → J → ℝ} {c : ℝ} {a : J → ℝ}
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) (hv : Tendsto v atTop (𝓝 0))
    (hcn : Tendsto cn atTop (𝓝 c))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) :
    Tendsto (fun n => OwnershipNormalized.value (changedData D e a0 (v n) (h n) i) (cn n) (an n))
      atTop (𝓝 (OwnershipNormalized.value (D i) c a)) := by
  apply OwnershipNormalized.value_tendsto _ _ hc ha (gamma_tendsto D hv i)
    (eta_tendsto D hv i) _ hcn (futureReceipt_tendsto D i hv han)
  intro s
  have hh := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp
    hv.fst_nhds.fst_nhds.snd_nhds.snd_nhds) i)) s
  simpa [changedData,OverlapPayoff.changedData] using tendsto_const_nhds.add hh

omit [Fintype H] in
theorem primitive_marginal_tendsto (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (i : H)
    (v : ℕ → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    {an : ℕ → J → ℝ} {a : J → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hv : Tendsto v atTop (𝓝 0))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) (j : J) :
    Tendsto (fun n => marginal (changedData D e a0 (v n) (h n) i) (an n) j)
      atTop (𝓝 (marginal (D i) a j)) := by
  apply tendsto_finsetSum
  intro s _
  have hvs := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.fst_nhds.fst_nhds.snd_nhds.snd_nhds) i)) s
  have hwlim : Tendsto (fun n => (D i).weight s+(v n).1.1.2.2 i s) atTop (𝓝 ((D i).weight s)) := by
    simpa using tendsto_const_nhds.add hvs
  exact (hwlim.mul (primitive_coefficient_tendsto D hv i s j)).mul
    ((futureReceipt_tendsto D i hv han s).rpow (eta_tendsto D hv i s).neg
      (Or.inl (ne_of_gt (consumption_positive (D i) ha s))))

theorem primitive_allocation_limit_reference (D : H → Data J S)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hsupport : SupportsInitial D e a0 qstar)
    (v : ℕ → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e a0 (v n) (h n)) (currentResources e (v n))
      (initialPortfolio a0 (v n)) (assetSupply supply (v n)) (qn n) (cn n) (an n))
    (c : H → ℝ) (a : H → J → ℝ) (hv : Tendsto v atTop (𝓝 0))
    (hcn : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (c i)))
    (han : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a i j))) : c=e ∧ a=a0 := by
  have hcp : ∀ i, 0 ≤ c i := fun i => le_of_tendsto_of_tendsto'
    tendsto_const_nhds (hcn i) (fun n => ((hEq n).consumption_positive i).le)
  have hap : ∀ i j, 0 ≤ a i j := fun i j => le_of_tendsto_of_tendsto'
    tendsto_const_nhds (han i j) (fun n => (hEq n).holdings_nonneg i j)
  have hcTotal : ∑ i, c i=∑ i, e i :=
    tendsto_nhds_unique_of_forall (tendsto_finsetSum Finset.univ (fun i _ => hcn i))
      (tendsto_finsetSum Finset.univ (fun i _ => endowment_tendsto e hv i))
      (fun n => (hEq n).consumption_clears)
  have haTotal : ∀ j, ∑ i, a i j=supply j := fun j =>
    tendsto_nhds_unique_of_forall (tendsto_finsetSum Finset.univ (fun i _ => han i j))
      (supply_tendsto supply hv j) (fun n => (hEq n).ownership_clears j)
  have hmidc : ∀ i, 0 < (e i+c i)/2 := by intro i; linarith [he i,hcp i]
  have hmida : ∀ i j, 0 ≤ (a0 i j+a i j)/2 := by intro i j; linarith [ha0 i j,hap i j]
  have hbetter : ∀ i, economicValue (D i) (e i) (a0 i) ≤
      economicValue (D i) ((e i+c i)/2) (fun j => (a0 i j+a i j)/2) := by
    intro i
    apply (OwnershipNormalized.comparison_iff (D i) (e i) ((e i+c i)/2)
      (a0 i) (fun j => (a0 i j+a i j)/2) (he i) (hmidc i) (ha0 i) (hmida i)).mp
    have hcm : Tendsto (fun n => (currentResources e (v n) i+cn n i)/2) atTop
        (𝓝 ((e i+c i)/2)) := ((endowment_tendsto e hv i).add (hcn i)).div_const 2
    have ham : ∀ j, Tendsto (fun n => (initialPortfolio a0 (v n) i j+an n i j)/2) atTop
        (𝓝 ((a0 i j+a i j)/2)) := fun j =>
      ((initial_tendsto a0 hv i j).add (han i j)).div_const 2
    exact le_of_tendsto_of_tendsto'
      (primitive_value_tendsto D e a0 i v h (he i) (ha0 i) hv (endowment_tendsto e hv i)
        (initial_tendsto a0 hv i))
      (primitive_value_tendsto D e a0 i v h (hmidc i) (hmida i) hv hcm ham)
      (fun n => by
        have hi : 0 < currentResources e (v n) i := (h n).1.1.1 i
        have hci := (hEq n).consumption_positive i
        have hai := (h n).2.1 i
        have hani := (hEq n).holdings_nonneg i
        have hcmid : 0 < (currentResources e (v n) i+cn n i)/2 := by linarith
        have hamid : ∀ j, 0 ≤ (initialPortfolio a0 (v n) i j+an n i j)/2 := by
          intro j; linarith [hai j,hani j]
        apply (OwnershipNormalized.comparison_iff (changedData D e a0 (v n) (h n) i)
          _ _ _ _ hi hcmid hai hamid).mpr
        exact midpoint_not_worse (changedData D e a0 (v n) (h n) i)
          _ _ _ _ hi hci hai hani
          ((hEq n).optimal i _ hi _ hai le_rfl))
  have hcClear : (∑ i, (e i+c i)/2)=∑ i, e i := by
    simp_rw [add_div]
    rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div,hcTotal]
    ring
  have haClear : ∀ j, (∑ i, (a0 i j+a i j)/2)=∑ i, a0 i j := by
    intro j
    simp_rw [add_div]
    rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div,haTotal j,← hstock j]
    ring
  obtain ⟨hcEq,haEq⟩ := reference_pareto_rigidity D e (fun i => (e i+c i)/2)
    a0 (fun i j => (a0 i j+a i j)/2) qstar he hmidc ha0 hmida hsupport hcClear haClear hbetter
  constructor
  · funext i
    have hh := congrFun hcEq i
    change (e i+c i)/2=e i at hh
    linarith
  · funext i j
    have hh := congrFun (congrFun haEq i) j
    change (a0 i j+a i j)/2=a0 i j at hh
    linarith

theorem primitive_prices_tendsto_reference [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma))
    (v : ℕ → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e a0 (v n) (h n)) (currentResources e (v n))
      (initialPortfolio a0 (v n)) (assetSupply supply (v n)) (qn n) (cn n) (an n))
    (hv : Tendsto v atTop (𝓝 0))
    (hcn : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (e i)))
    (han : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a0 i j))) :
    ∀ j, Tendsto (fun n => qn n j) atTop (𝓝 (qstar j)) := by
  classical
  let i : H := Classical.choice ‹Nonempty H›
  intro j
  have hown : ∀ᶠ n in atTop, 0 < an n i j := (han i j).eventually (Ioi_mem_nhds (ha0 i j))
  have hformula : (fun n => qn n j) =ᶠ[atTop]
      (fun n => marginal (changedData D e a0 (v n) (h n) i) (an n i) j /
        (cn n i)^(-currentCurvature D (v n) i)) := by
    filter_upwards [hown] with n hn
    apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos
      ((hEq n).consumption_positive i) (-currentCurvature D (v n) i)))).mpr
    exact (OwnershipUniform.owned_asset_euler (hEq n) i j hn).symm
  have hm := primitive_marginal_tendsto D e a0 i v h (fun j => (ha0 i j).le) hv (han i) j
  have hl := (hcn i).rpow (gamma_tendsto D hv i).neg (Or.inl (ne_of_gt (he i)))
  have hd := hm.div hl (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))
  have hval : marginal (D i) (a0 i) j/(e i)^(-(D i).gamma)=qstar j :=
    (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))).mpr (heuler i j)
  rw [hval] at hd
  exact (tendsto_congr' hformula).mpr hd

theorem primitive_all_actual_equilibria_near_reference [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma))
    (U : Set (PrimitiveShock H J S × MarketState H J)) (hU : U ∈ 𝓝 (0,(qstar,a0))) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v,
      ∀ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → (v,(q,a)) ∈ U := by
  classical
  have hsupport : SupportsInitial D e a0 qstar := by
    intro i j
    rw [heuler i j]
    exact ⟨le_rfl,by ring⟩
  by_contra hn
  have hfreq : ∃ᶠ v in 𝓝 (0 : PrimitiveShock H J S), ¬ (∀ h : Admissible D e a0 v,
      ∀ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → (v,(q,a)) ∈ U) := Filter.not_eventually.mp hn
  obtain ⟨v,hv,hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hex : ∀ n, ∃ h : Admissible D e a0 (v n), ∃ q c a,
      IsEquilibrium (changedData D e a0 (v n) h) (currentResources e (v n)) (initialPortfolio a0 (v n)) (assetSupply supply (v n)) q c a ∧
        (v n,(q,a)) ∉ U := by
    intro n
    simpa only [not_forall,not_imp,exists_prop] using hbad n
  choose h qn cn an hEq hout using hex
  let upper : Allocation H J := (fun _ => (∑ i, e i)+1, fun _ j => supply j+1)
  have htotal : Tendsto (fun n => ∑ i, currentResources e (v n) i) atTop (𝓝 (∑ i, e i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => endowment_tendsto e hv i)
  have hsup : ∀ᶠ n in atTop, ∀ j, assetSupply supply (v n) j<supply j+1 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (supply_tendsto supply hv j).eventually (Iio_mem_nhds (by linarith))
  have hbound : ∀ᶠ n in atTop, (cn n,an n) ∈ Icc (allocationBottom : Allocation H J) upper := by
    filter_upwards [htotal.eventually (Iio_mem_nhds (show (∑ i, e i)<(∑ i, e i)+1 by linarith)),hsup]
      with n hn hsn
    constructor
    · exact ⟨fun i => ((hEq n).consumption_positive i).le,fun i j => (hEq n).holdings_nonneg i j⟩
    · exact ⟨fun i => (OwnershipUniform.consumption_le_total (hEq n) i).trans hn.le,
        fun i j => (OwnershipUniform.holdings_le_supply (hEq n) i j).trans (hsn j).le⟩
  have hcompact : IsCompact (Icc (allocationBottom : Allocation H J) upper) := isCompact_Icc
  obtain ⟨z,_,phi,hphi,hlim⟩ := hcompact.tendsto_subseq' hbound.frequently
  have hc : ∀ i, Tendsto (fun n => cn (phi n) i) atTop (𝓝 (z.1 i)) :=
    fun i => (tendsto_pi_nhds.mp hlim.fst_nhds) i
  have ha : ∀ i j, Tendsto (fun n => an (phi n) i j) atTop (𝓝 (z.2 i j)) :=
    fun i j => (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hlim.snd_nhds) i)) j
  have hv' := hv.comp hphi.tendsto_atTop
  obtain ⟨hceq,haeq⟩ := primitive_allocation_limit_reference D e a0 supply qstar he
    (fun i j => (ha0 i j).le) hstock hsupport (fun n => v (phi n))
    (fun n => h (phi n)) (fun n => qn (phi n)) (fun n => cn (phi n))
    (fun n => an (phi n)) (fun n => hEq (phi n)) z.1 z.2 hv' hc ha
  rw [hceq] at hc
  rw [haeq] at ha
  have hq := primitive_prices_tendsto_reference D e a0 supply qstar he ha0 heuler
    (fun n => v (phi n)) (fun n => h (phi n)) (fun n => qn (phi n))
    (fun n => cn (phi n)) (fun n => an (phi n)) (fun n => hEq (phi n)) hv' hc ha
  have hq' : Tendsto (fun n => qn (phi n)) atTop (𝓝 qstar) := tendsto_pi_nhds.mpr hq
  have ha' : Tendsto (fun n => an (phi n)) atTop (𝓝 a0) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (ha i))
  have hp : Tendsto (fun n => (v (phi n),(qn (phi n),an (phi n)))) atTop
      (𝓝 (0,(qstar,a0))) := hv'.prodMk_nhds (hq'.prodMk_nhds ha')
  obtain ⟨n,hn⟩ := (hp.eventually hU).exists
  exact hout (phi n) hn

def GlobalAt (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (z : MarketState H J) (v : PrimitiveShock H J S) : Prop :=
  ∃ h : Admissible D e a0 v,
    IsEquilibrium (changedData D e a0 v h) (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v)
      z.1 (currentBudget e a0 v z) z.2 ∧
    primitiveResidual D e a0 supply (v,z)=0 ∧
    ∀ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v) q c a →
      q=z.1 ∧ c=currentBudget e a0 v z ∧ a=z.2

theorem primitive_global_actual_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < qstar j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma)) :
    ∃ psi : PrimitiveShock H J S → MarketState H J, psi 0=(qstar,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      ∀ᶠ v in 𝓝 0, Nonnegative D v → GlobalAt D e a0 supply (psi v) v := by
  obtain ⟨psi,hpsi,hcd,hcert,hgraph⟩ := primitive_local_actual_family D e a0 supply qstar
    he ha0 hq hstock heuler
  let U : Set (PrimitiveShock H J S × MarketState H J) := {p | ∀ h : Admissible D e a0 p.1,
      ∀ c : H → ℝ, IsEquilibrium (changedData D e a0 p.1 h) (currentResources e p.1)
        (initialPortfolio a0 p.1) (assetSupply supply p.1) p.2.1 c p.2.2 → p.2=psi p.1 ∧ c=currentBudget e a0 p.1 p.2}
  have hU : U ∈ 𝓝 (0,(qstar,a0)) := hgraph
  have hnear := primitive_all_actual_equilibria_near_reference D e a0 supply qstar he ha0 hstock heuler U hU
  refine ⟨psi,hpsi,hcd,?_⟩
  filter_upwards [hcert,hnear,admissible_near_zero D e a0 he ha0] with v hcv hnv hadm
  intro hp
  have h := hadm hp
  obtain ⟨hEq,hr⟩ := hcv h
  refine ⟨h,hEq,hr,?_⟩
  intro q c a hEq'
  have hh := hnv h q c a hEq'
  change (∀ h : Admissible D e a0 v, ∀ c : H → ℝ,
    IsEquilibrium (changedData D e a0 v h) (currentResources e v) (initialPortfolio a0 v) (assetSupply supply v) q c a →
      (q,a)=psi v ∧ c=currentBudget e a0 v (q,a)) at hh
  obtain ⟨hz,hc⟩ := hh h c hEq'
  exact ⟨congrArg Prod.fst hz,by simpa only [hz] using hc,congrArg Prod.snd hz⟩

theorem primitive_current_consumption_contDiffOn (e : H → ℝ) (a0 : H → J → ℝ)
    (psi : PrimitiveShock H J S → MarketState H J) (u : Set (PrimitiveShock H J S))
    (hcd : ContDiffOn ℝ 1 psi u) :
    ContDiffOn ℝ 1 (fun v => currentBudget e a0 v (psi v)) u := by
  have hb : ContDiff ℝ 1 (fun p : PrimitiveShock H J S × MarketState H J =>
      currentBudget e a0 p.1 p.2) := by
    apply contDiff_pi.mpr
    intro i
    unfold currentBudget budgetValue currentResources initialPortfolio OverlapPayoff.changedEndowment OverlapResource.changedEndowment
    fun_prop
  exact hb.comp_contDiffOn (contDiffOn_id.prodMk hcd)

theorem joint_all_primitive_global_actual_ball [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < qstar j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma)) :
    ∃ psi : PrimitiveShock H J S → MarketState H J, ∃ radius : ℝ,
      0 < radius ∧ psi 0=(qstar,a0) ∧ ContDiffOn ℝ 1 psi (Metric.ball 0 radius) ∧
        ContDiffOn ℝ 1 (fun v => currentBudget e a0 v (psi v)) (Metric.ball 0 radius) ∧
        ∀ v, ‖v‖ < radius → Nonnegative D v → GlobalAt D e a0 supply (psi v) v := by
  obtain ⟨psi,hpsi,hcd,hcert⟩ := primitive_global_actual_family D e a0 supply qstar he ha0 hq hstock heuler
  obtain ⟨u,hu,hcdu⟩ := hcd.contDiffOn (m := 1) le_rfl (by norm_num)
  have hboth : {v | Nonnegative D v → GlobalAt D e a0 supply (psi v) v} ∩ u ∈ 𝓝 (0 : PrimitiveShock H J S) :=
    inter_mem hcert hu
  obtain ⟨radius,hr,hball⟩ := Metric.mem_nhds_iff.mp hboth
  have hcdBall := hcdu.mono (fun _ hv => (hball hv).2)
  refine ⟨psi,radius,hr,hpsi,hcdBall,primitive_current_consumption_contDiffOn e a0 psi _ hcdBall,?_⟩
  intro v hv
  exact (hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv)).1

theorem positive_payoffs_near_zero (D : H → Data J S)
    (hP : ∀ i s j, 0 < (D i).payoff s j) :
    ∀ᶠ v : PrimitiveShock H J S in 𝓝 0, Nonnegative D v :=
  (continuous_fst.tendsto (0 : PrimitiveShock H J S)).eventually
    (OverlapPayoff.positive_payoffs_near_zero D hP)

theorem positive_joint_all_primitive_global_actual_ball [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < qstar j)
    (hP : ∀ i s j, 0 < (D i).payoff s j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma)) :
    ∃ psi : PrimitiveShock H J S → MarketState H J, ∃ radius : ℝ,
      0 < radius ∧ psi 0=(qstar,a0) ∧ ContDiffOn ℝ 1 psi (Metric.ball 0 radius) ∧
        ContDiffOn ℝ 1 (fun v => currentBudget e a0 v (psi v)) (Metric.ball 0 radius) ∧
        ∀ v, ‖v‖ < radius → GlobalAt D e a0 supply (psi v) v := by
  obtain ⟨psi,r0,hr0,hpsi,hcd,hcons,hcert⟩ :=
    joint_all_primitive_global_actual_ball D e a0 supply qstar he ha0 hq hstock heuler
  obtain ⟨r1,hr1,hball⟩ := Metric.mem_nhds_iff.mp (positive_payoffs_near_zero D hP)
  have hsub : Metric.ball (0 : PrimitiveShock H J S) (min r0 r1) ⊆ Metric.ball 0 r0 :=
    Metric.ball_subset_ball (min_le_left r0 r1)
  refine ⟨psi,min r0 r1,lt_min hr0 hr1,hpsi,hcd.mono hsub,hcons.mono hsub,?_⟩
  intro v hv
  have hv0 := lt_of_lt_of_le hv (min_le_left r0 r1)
  have hv1 := lt_of_lt_of_le hv (min_le_right r0 r1)
  exact hcert v hv0 (hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv1))


end OverlapPrimitive

#print axioms OverlapPrimitive.inventory_consistency
#print axioms OverlapPrimitive.admissible_near_zero
#print axioms OverlapPrimitive.primitiveResidual_zero
#print axioms OverlapPrimitive.primitiveResidual_eq_actual
#print axioms OverlapPrimitive.primitiveResidual_contDiffAt
#print axioms OverlapPrimitive.primitive_partial_isInvertible
#print axioms OverlapPrimitive.primitive_local_root_family
#print axioms OverlapPrimitive.primitive_local_actual_family
#print axioms OverlapPrimitive.endowment_tendsto
#print axioms OverlapPrimitive.primitive_coefficient_tendsto
#print axioms OverlapPrimitive.futureReceipt_tendsto
#print axioms OverlapPrimitive.initial_tendsto
#print axioms OverlapPrimitive.supply_tendsto
#print axioms OverlapPrimitive.gamma_tendsto
#print axioms OverlapPrimitive.eta_tendsto
#print axioms OverlapPrimitive.primitive_value_tendsto
#print axioms OverlapPrimitive.primitive_marginal_tendsto
#print axioms OverlapPrimitive.primitive_allocation_limit_reference
#print axioms OverlapPrimitive.primitive_prices_tendsto_reference
#print axioms OverlapPrimitive.primitive_all_actual_equilibria_near_reference
#print axioms OverlapPrimitive.primitive_global_actual_family
#print axioms OverlapPrimitive.primitive_current_consumption_contDiffOn
#print axioms OverlapPrimitive.joint_all_primitive_global_actual_ball
#print axioms OverlapPrimitive.positive_payoffs_near_zero
#print axioms OverlapPrimitive.positive_joint_all_primitive_global_actual_ball
