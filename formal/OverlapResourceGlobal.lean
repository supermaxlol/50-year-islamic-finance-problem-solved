import OverlapResourceFamily

/-! Changing aggregate resources require a new common allocation box. Varying
income/weight utility limits and the affordable changed initial bundles feed
the accepted midpoint rigidity argument. Prices are recovered from actual
Euler equalities, not assumed bounded before compactness. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSupported OverlapLocal OverlapStability

namespace OverlapResource
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

omit [Fintype H] [Fintype S] in
theorem resource_budget_identity (e : H → ℝ) (a0 : H → J → ℝ)
    (v : ResourceShock H S) (z : MarketState H J) (i : H) :
    budgetValue (changedEndowment e v) a0 z i=budgetValue e a0 z i+v.1 i := by
  unfold budgetValue changedEndowment
  ring

omit [Fintype H] [Fintype S] in
theorem independent_income_identity (D : H → Data J S) (v : ResourceShock H S)
    (i : H) (a : J → ℝ) (s : S) :
    futureReceipt D v i a s=consumption (D i) a s+v.2.1 i s := by
  unfold futureReceipt consumption
  ring

omit [Fintype H] [Fintype S] in
theorem endowment_tendsto (e : H → ℝ) {v : ℕ → ResourceShock H S}
    (hv : Tendsto v atTop (𝓝 0)) (i : H) :
    Tendsto (fun n => changedEndowment e (v n) i) atTop (𝓝 (e i)) := by
  have hi := (tendsto_pi_nhds.mp hv.fst_nhds) i
  simpa [changedEndowment] using tendsto_const_nhds.add hi

omit [Fintype H] [Fintype S] in
theorem futureReceipt_tendsto (D : H → Data J S) (i : H)
    {v : ℕ → ResourceShock H S} {an : ℕ → J → ℝ} {a : J → ℝ}
    (hv : Tendsto v atTop (𝓝 0))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) (s : S) :
    Tendsto (fun n => futureReceipt D (v n) i (an n) s) atTop
      (𝓝 (consumption (D i) a s)) := by
  have hy := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.snd_nhds.fst_nhds) i)) s
  have hy' : Tendsto (fun n => (D i).income s+(v n).2.1 i s) atTop (𝓝 ((D i).income s)) := by
    simpa using tendsto_const_nhds.add hy
  exact hy'.add (tendsto_finsetSum Finset.univ (fun j _ => (han j).const_mul ((D i).payoff s j)))

omit [Fintype H] in
theorem resource_value_tendsto (D : H → Data J S) (e : H → ℝ) (i : H)
    (v : ℕ → ResourceShock H S) (h : ∀ n, Admissible D e (v n))
    {cn : ℕ → ℝ} {an : ℕ → J → ℝ} {c : ℝ} {a : J → ℝ}
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) (hv : Tendsto v atTop (𝓝 0))
    (hcn : Tendsto cn atTop (𝓝 c))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) :
    Tendsto (fun n => economicValue (changedData D e (v n) (h n) i) (cn n) (an n))
      atTop (𝓝 (economicValue (D i) c a)) := by
  change Tendsto (fun n => utility (D i).gamma (cn n)+
    ∑ s, ((D i).weight s+(v n).2.2 i s)*utility ((D i).eta s)
      (futureReceipt D (v n) i (an n) s)) atTop _
  apply Tendsto.add
  · exact (utility_hasDerivAt (g := (D i).gamma) hc).continuousAt.tendsto.comp hcn
  · apply tendsto_finsetSum
    intro s _
    have hvs := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.snd_nhds.snd_nhds) i)) s
    have hwlim : Tendsto (fun n => (D i).weight s+(v n).2.2 i s) atTop (𝓝 ((D i).weight s)) := by
      simpa using tendsto_const_nhds.add hvs
    exact hwlim.mul ((utility_hasDerivAt (g := (D i).eta s)
      (consumption_positive (D i) ha s)).continuousAt.tendsto.comp
        (futureReceipt_tendsto D i hv han s))

omit [Fintype H] in
theorem resource_marginal_tendsto (D : H → Data J S) (e : H → ℝ) (i : H)
    (v : ℕ → ResourceShock H S) (h : ∀ n, Admissible D e (v n))
    {an : ℕ → J → ℝ} {a : J → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hv : Tendsto v atTop (𝓝 0))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j))) (j : J) :
    Tendsto (fun n => marginal (changedData D e (v n) (h n) i) (an n) j)
      atTop (𝓝 (marginal (D i) a j)) := by
  apply tendsto_finsetSum
  intro s _
  have hvs := (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hv.snd_nhds.snd_nhds) i)) s
  have hwlim : Tendsto (fun n => (D i).weight s+(v n).2.2 i s) atTop (𝓝 ((D i).weight s)) := by
    simpa using tendsto_const_nhds.add hvs
  exact (hwlim.mul_const ((D i).payoff s j)).mul
    ((futureReceipt_tendsto D i hv han s).rpow_const
      (Or.inl (ne_of_gt (consumption_positive (D i) ha s))))

theorem resource_allocation_limit_reference (D : H → Data J S)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hsupport : SupportsInitial D e a0 qstar)
    (v : ℕ → ResourceShock H S) (h : ∀ n, Admissible D e (v n))
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e (v n) (h n)) (changedEndowment e (v n))
      a0 supply (qn n) (cn n) (an n))
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
      tendsto_const_nhds (fun n => (hEq n).ownership_clears j)
  have hmidc : ∀ i, 0 < (e i+c i)/2 := by intro i; linarith [he i,hcp i]
  have hmida : ∀ i j, 0 ≤ (a0 i j+a i j)/2 := by intro i j; linarith [ha0 i j,hap i j]
  have hbetter : ∀ i, economicValue (D i) (e i) (a0 i) ≤
      economicValue (D i) ((e i+c i)/2) (fun j => (a0 i j+a i j)/2) := by
    intro i
    have hcm : Tendsto (fun n => (changedEndowment e (v n) i+cn n i)/2) atTop
        (𝓝 ((e i+c i)/2)) := ((endowment_tendsto e hv i).add (hcn i)).div_const 2
    have ham : ∀ j, Tendsto (fun n => (a0 i j+an n i j)/2) atTop
        (𝓝 ((a0 i j+a i j)/2)) := fun j =>
      (tendsto_const_nhds.add (han i j)).div_const 2
    exact le_of_tendsto_of_tendsto'
      (resource_value_tendsto D e i v h (he i) (ha0 i) hv (endowment_tendsto e hv i)
        (fun _ => tendsto_const_nhds))
      (resource_value_tendsto D e i v h (hmidc i) (hmida i) hv hcm ham)
      (fun n => midpoint_not_worse (changedData D e (v n) (h n) i)
        (changedEndowment e (v n) i) (cn n i) (a0 i) (an n i)
        ((h n).1 i) ((hEq n).consumption_positive i) (ha0 i) ((hEq n).holdings_nonneg i)
        ((hEq n).optimal i (changedEndowment e (v n) i) ((h n).1 i) (a0 i) (ha0 i) le_rfl))
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

theorem resource_prices_tendsto_reference [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma))
    (v : ℕ → ResourceShock H S) (h : ∀ n, Admissible D e (v n))
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e (v n) (h n)) (changedEndowment e (v n))
      a0 supply (qn n) (cn n) (an n))
    (hv : Tendsto v atTop (𝓝 0))
    (hcn : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (e i)))
    (han : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a0 i j))) :
    ∀ j, Tendsto (fun n => qn n j) atTop (𝓝 (qstar j)) := by
  classical
  let i : H := Classical.choice ‹Nonempty H›
  intro j
  have hown : ∀ᶠ n in atTop, 0 < an n i j := (han i j).eventually (Ioi_mem_nhds (ha0 i j))
  have hformula : (fun n => qn n j) =ᶠ[atTop]
      (fun n => marginal (changedData D e (v n) (h n) i) (an n i) j /(cn n i)^(-(D i).gamma)) := by
    filter_upwards [hown] with n hn
    apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos
      ((hEq n).consumption_positive i) (-(D i).gamma)))).mpr
    exact (OwnershipUniform.owned_asset_euler (hEq n) i j hn).symm
  have hm := resource_marginal_tendsto D e i v h (fun j => (ha0 i j).le) hv (han i) j
  have hl := (hcn i).rpow_const (p := -(D i).gamma) (Or.inl (ne_of_gt (he i)))
  have hd := hm.div hl (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))
  have hval : marginal (D i) (a0 i) j/(e i)^(-(D i).gamma)=qstar j :=
    (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))).mpr (heuler i j)
  rw [hval] at hd
  exact (tendsto_congr' hformula).mpr hd

theorem resource_all_actual_equilibria_near_reference [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma))
    (U : Set (ResourceShock H S × MarketState H J)) (hU : U ∈ 𝓝 (0,(qstar,a0))) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e v,
      ∀ q c a, IsEquilibrium (changedData D e v h) (changedEndowment e v)
        a0 supply q c a → (v,(q,a)) ∈ U := by
  classical
  have hsupport : SupportsInitial D e a0 qstar := by
    intro i j
    rw [heuler i j]
    exact ⟨le_rfl,by ring⟩
  by_contra hn
  have hfreq : ∃ᶠ v in 𝓝 (0 : ResourceShock H S), ¬ (∀ h : Admissible D e v,
      ∀ q c a, IsEquilibrium (changedData D e v h) (changedEndowment e v)
        a0 supply q c a → (v,(q,a)) ∈ U) := Filter.not_eventually.mp hn
  obtain ⟨v,hv,hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hex : ∀ n, ∃ h : Admissible D e (v n), ∃ q c a,
      IsEquilibrium (changedData D e (v n) h) (changedEndowment e (v n)) a0 supply q c a ∧
        (v n,(q,a)) ∉ U := by
    intro n
    simpa only [not_forall,not_imp,exists_prop] using hbad n
  choose h qn cn an hEq hout using hex
  let upper : Allocation H J := (fun _ => (∑ i, e i)+1, fun _ j => supply j)
  have htotal : Tendsto (fun n => ∑ i, changedEndowment e (v n) i) atTop (𝓝 (∑ i, e i)) :=
    tendsto_finsetSum Finset.univ (fun i _ => endowment_tendsto e hv i)
  have hbound : ∀ᶠ n in atTop, (cn n,an n) ∈ Icc (allocationBottom : Allocation H J) upper := by
    filter_upwards [htotal.eventually (Iio_mem_nhds (show (∑ i, e i)<(∑ i, e i)+1 by linarith))]
      with n hn
    constructor
    · exact ⟨fun i => ((hEq n).consumption_positive i).le,fun i j => (hEq n).holdings_nonneg i j⟩
    · exact ⟨fun i => (OwnershipUniform.consumption_le_total (hEq n) i).trans hn.le,
        fun i j => OwnershipUniform.holdings_le_supply (hEq n) i j⟩
  have hcompact : IsCompact (Icc (allocationBottom : Allocation H J) upper) := isCompact_Icc
  obtain ⟨z,_,phi,hphi,hlim⟩ := hcompact.tendsto_subseq' hbound.frequently
  have hc : ∀ i, Tendsto (fun n => cn (phi n) i) atTop (𝓝 (z.1 i)) :=
    fun i => (tendsto_pi_nhds.mp hlim.fst_nhds) i
  have ha : ∀ i j, Tendsto (fun n => an (phi n) i j) atTop (𝓝 (z.2 i j)) :=
    fun i j => (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hlim.snd_nhds) i)) j
  have hv' := hv.comp hphi.tendsto_atTop
  obtain ⟨hceq,haeq⟩ := resource_allocation_limit_reference D e a0 supply qstar he
    (fun i j => (ha0 i j).le) hstock hsupport (fun n => v (phi n))
    (fun n => h (phi n)) (fun n => qn (phi n)) (fun n => cn (phi n))
    (fun n => an (phi n)) (fun n => hEq (phi n)) z.1 z.2 hv' hc ha
  rw [hceq] at hc
  rw [haeq] at ha
  have hq := resource_prices_tendsto_reference D e a0 supply qstar he ha0 heuler
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
    (z : MarketState H J) (v : ResourceShock H S) : Prop :=
  ∃ h : Admissible D e v,
    IsEquilibrium (changedData D e v h) (changedEndowment e v) a0 supply
      z.1 (budgetValue (changedEndowment e v) a0 z) z.2 ∧
    resourceResidual D e a0 supply (v,z)=0 ∧
    ∀ q c a, IsEquilibrium (changedData D e v h) (changedEndowment e v) a0 supply q c a →
      q=z.1 ∧ c=budgetValue (changedEndowment e v) a0 z ∧ a=z.2

theorem resource_global_actual_family [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < qstar j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma)) :
    ∃ psi : ResourceShock H S → MarketState H J, psi 0=(qstar,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      ∀ᶠ v in 𝓝 0, GlobalAt D e a0 supply (psi v) v := by
  obtain ⟨psi,hpsi,hcd,hcert,hgraph⟩ := resource_local_actual_family D e a0 supply qstar
    he ha0 hq hstock heuler
  let U : Set (ResourceShock H S × MarketState H J) := {p | ∀ h : Admissible D e p.1,
      ∀ c : H → ℝ, IsEquilibrium (changedData D e p.1 h) (changedEndowment e p.1)
        a0 supply p.2.1 c p.2.2 → p.2=psi p.1 ∧ c=budgetValue (changedEndowment e p.1) a0 p.2}
  have hU : U ∈ 𝓝 (0,(qstar,a0)) := hgraph
  have hnear := resource_all_actual_equilibria_near_reference D e a0 supply qstar he ha0 hstock heuler U hU
  refine ⟨psi,hpsi,hcd,?_⟩
  filter_upwards [hcert,hnear] with v hcv hnv
  obtain ⟨h,hEq,hr⟩ := hcv
  refine ⟨h,hEq,hr,?_⟩
  intro q c a hEq'
  have hh := hnv h q c a hEq'
  change (∀ h : Admissible D e v, ∀ c : H → ℝ,
    IsEquilibrium (changedData D e v h) (changedEndowment e v) a0 supply q c a →
      (q,a)=psi v ∧ c=budgetValue (changedEndowment e v) a0 (q,a)) at hh
  obtain ⟨hz,hc⟩ := hh h c hEq'
  exact ⟨congrArg Prod.fst hz,by simpa only [hz] using hc,congrArg Prod.snd hz⟩

theorem resource_current_consumption_contDiffOn (e : H → ℝ) (a0 : H → J → ℝ)
    (psi : ResourceShock H S → MarketState H J) (u : Set (ResourceShock H S))
    (hcd : ContDiffOn ℝ 1 psi u) :
    ContDiffOn ℝ 1 (fun v => budgetValue (changedEndowment e v) a0 (psi v)) u := by
  have hb : ContDiff ℝ 1 (fun p : ResourceShock H S × MarketState H J =>
      budgetValue (changedEndowment e p.1) a0 p.2) := by
    apply contDiff_pi.mpr
    intro i
    unfold budgetValue changedEndowment
    fun_prop
  exact hb.comp_contDiffOn (contDiffOn_id.prodMk hcd)

theorem resource_global_actual_ball [Nonempty H]
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < qstar j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma)) :
    ∃ psi : ResourceShock H S → MarketState H J, ∃ radius : ℝ,
      0 < radius ∧ psi 0=(qstar,a0) ∧ ContDiffOn ℝ 1 psi (Metric.ball 0 radius) ∧
        ContDiffOn ℝ 1 (fun v => budgetValue (changedEndowment e v) a0 (psi v)) (Metric.ball 0 radius) ∧
        ∀ v, ‖v‖ < radius → GlobalAt D e a0 supply (psi v) v := by
  obtain ⟨psi,hpsi,hcd,hcert⟩ := resource_global_actual_family D e a0 supply qstar he ha0 hq hstock heuler
  obtain ⟨u,hu,hcdu⟩ := hcd.contDiffOn (m := 1) le_rfl (by norm_num)
  have hboth : {v | GlobalAt D e a0 supply (psi v) v} ∩ u ∈ 𝓝 (0 : ResourceShock H S) :=
    inter_mem hcert hu
  obtain ⟨radius,hr,hball⟩ := Metric.mem_nhds_iff.mp hboth
  have hcdBall := hcdu.mono (fun _ hv => (hball hv).2)
  refine ⟨psi,radius,hr,hpsi,hcdBall,resource_current_consumption_contDiffOn e a0 psi _ hcdBall,?_⟩
  intro v hv
  exact (hball (by simpa only [Metric.mem_ball,dist_zero_right] using hv)).1

theorem interior_resource_trading_control :
    ∃ psi : ResourceShock (Fin 2) (Fin 4) → MarketState (Fin 2) (Fin 2), ∃ radius : ℝ,
      0 < radius ∧ psi 0=(CornerControl.qstar,InteriorControl.initial) ∧
      ContDiffOn ℝ 1 psi (Metric.ball 0 radius) ∧
      ContDiffOn ℝ 1 (fun v => budgetValue (changedEndowment InteriorControl.endowment v)
        InteriorControl.initial (psi v)) (Metric.ball 0 radius) ∧
      (∀ v, ‖v‖ < radius → GlobalAt InteriorControl.D InteriorControl.endowment
        InteriorControl.initial CornerControl.supply (psi v) v) ∧
      (∀ t : ℝ, ‖((0,0,fun i s => t*interiorShock i s) : ResourceShock (Fin 2) (Fin 4))‖ < radius →
        t ≠ 0 → (psi (0,0,fun i s => t*interiorShock i s)).2 ≠ InteriorControl.initial) := by
  have heuler : ∀ i j, marginal (InteriorControl.D i) (InteriorControl.initial i) j=
      CornerControl.qstar j*(InteriorControl.endowment i)^(-(InteriorControl.D i).gamma) := by
    intro i j
    have hh := (InteriorControl.primitive_support i j).2
    have hz := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (InteriorControl.initial_interior i j))
    linarith
  obtain ⟨psi,radius,hr,hpsi,hcd,hcons,hcert⟩ := resource_global_actual_ball InteriorControl.D
    InteriorControl.endowment InteriorControl.initial CornerControl.supply CornerControl.qstar
    (by intro i; norm_num [InteriorControl.endowment]) InteriorControl.initial_interior
    (by intro j; fin_cases j <;> norm_num [CornerControl.qstar])
    (by intro j; fin_cases j <;>
      norm_num [InteriorControl.initial,CornerControl.supply,Fin.sum_univ_succ]) heuler
  refine ⟨psi,radius,hr,hpsi,hcd,hcons,hcert,?_⟩
  intro t ht hne
  obtain ⟨_,_,hroot,_⟩ := hcert (0,0,fun i s => t*interiorShock i s) ht
  rw [resourceResidual_line] at hroot
  exact interior_nonzero_root_trades t _ hroot hne

end OverlapResource

#print axioms OverlapResource.resource_budget_identity
#print axioms OverlapResource.independent_income_identity
#print axioms OverlapResource.endowment_tendsto
#print axioms OverlapResource.futureReceipt_tendsto
#print axioms OverlapResource.resource_value_tendsto
#print axioms OverlapResource.resource_marginal_tendsto
#print axioms OverlapResource.resource_allocation_limit_reference
#print axioms OverlapResource.resource_prices_tendsto_reference
#print axioms OverlapResource.resource_all_actual_equilibria_near_reference
#print axioms OverlapResource.resource_global_actual_family
#print axioms OverlapResource.resource_current_consumption_contDiffOn
#print axioms OverlapResource.resource_global_actual_ball
#print axioms OverlapResource.interior_resource_trading_control
