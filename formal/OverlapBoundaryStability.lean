import JointPrimitiveEconomy

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSupported OverlapLocal OverlapStability OverlapPrimitive

namespace OverlapBoundary
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

omit [Fintype J] [Fintype S] in
theorem positive_reference_owner (a0 : H → J → ℝ) (supply : J → ℝ)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j) (j : J) :
    ∃ i, 0 < a0 i j := by
  classical
  by_contra hn
  push Not at hn
  have hh : ∑ i, a0 i j ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
  rw [hstock j] at hh
  linarith [hs j]

theorem boundary_prices_tendsto_reference
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (v : ℕ → PrimitiveShock H J S) (h : ∀ n, Admissible D e a0 (v n))
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (changedData D e a0 (v n) (h n)) (currentResources e (v n))
      (initialPortfolio a0 (v n)) (assetSupply supply (v n)) (qn n) (cn n) (an n))
    (hv : Tendsto v atTop (𝓝 0))
    (hcn : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (e i)))
    (han : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a0 i j))) :
    ∀ j, Tendsto (fun n => qn n j) atTop (𝓝 (qstar j)) := by
  intro j
  obtain ⟨i,hi⟩ := positive_reference_owner a0 supply hstock hs j
  have hown : ∀ᶠ n in atTop, 0 < an n i j := (han i j).eventually (Ioi_mem_nhds hi)
  have hformula : (fun n => qn n j) =ᶠ[atTop]
      (fun n => marginal (changedData D e a0 (v n) (h n) i) (an n i) j /
        (cn n i)^(-currentCurvature D (v n) i)) := by
    filter_upwards [hown] with n hn
    apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos
      ((hEq n).consumption_positive i) (-currentCurvature D (v n) i)))).mpr
    exact (OwnershipUniform.owned_asset_euler (hEq n) i j hn).symm
  have hm := primitive_marginal_tendsto D e a0 i v h (ha0 i) hv (han i) j
  have hl := (hcn i).rpow (gamma_tendsto D hv i).neg (Or.inl (ne_of_gt (he i)))
  have hd := hm.div hl (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))
  have hval := (supported_price_from_owner D e a0 qstar he hsupport i j hi).symm
  rw [hval] at hd
  exact (tendsto_congr' hformula).mpr hd

theorem all_actual_equilibria_near_boundary_reference
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar)
    (U : Set (PrimitiveShock H J S × MarketState H J)) (hU : U ∈ 𝓝 (0,(qstar,a0))) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v,
      ∀ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → (v,(q,a)) ∈ U := by
  classical
  by_contra hn
  have hfreq : ∃ᶠ v in 𝓝 (0 : PrimitiveShock H J S), ¬ (∀ h : Admissible D e a0 v,
      ∀ q c a, IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → (v,(q,a)) ∈ U) := Filter.not_eventually.mp hn
  obtain ⟨v,hv,hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hex : ∀ n, ∃ h : Admissible D e a0 (v n), ∃ q c a,
      IsEquilibrium (changedData D e a0 (v n) h) (currentResources e (v n))
        (initialPortfolio a0 (v n)) (assetSupply supply (v n)) q c a ∧ (v n,(q,a)) ∉ U := by
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
    ha0 hstock hsupport (fun n => v (phi n)) (fun n => h (phi n))
    (fun n => qn (phi n)) (fun n => cn (phi n)) (fun n => an (phi n))
    (fun n => hEq (phi n)) z.1 z.2 hv' hc ha
  rw [hceq] at hc
  rw [haeq] at ha
  have hq := boundary_prices_tendsto_reference D e a0 supply qstar he ha0 hstock hs hsupport
    (fun n => v (phi n)) (fun n => h (phi n)) (fun n => qn (phi n))
    (fun n => cn (phi n)) (fun n => an (phi n)) (fun n => hEq (phi n)) hv' hc ha
  have hq' : Tendsto (fun n => qn (phi n)) atTop (𝓝 qstar) := tendsto_pi_nhds.mpr hq
  have ha' : Tendsto (fun n => an (phi n)) atTop (𝓝 a0) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (ha i))
  have hp : Tendsto (fun n => (v (phi n),(qn (phi n),an (phi n)))) atTop
      (𝓝 (0,(qstar,a0))) := hv'.prodMk_nhds (hq'.prodMk_nhds ha')
  obtain ⟨n,hn⟩ := (hp.eventually hU).exists
  exact hout (phi n) hn

theorem strict_nonowner_persists
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j) (hs : ∀ j, 0 < supply j)
    (hsupport : SupportsInitial D e a0 qstar) (i : H) (j : J)
    (hstrict : marginal (D i) (a0 i) j < qstar j*(e i)^(-(D i).gamma)) :
    ∀ᶠ v in 𝓝 0, ∀ h : Admissible D e a0 v, ∀ q c a,
      IsEquilibrium (changedData D e a0 v h) (currentResources e v)
        (initialPortfolio a0 v) (assetSupply supply v) q c a → a i j=0 := by
  have hc := (primitiveResidual_contDiffAt D e a0 supply qstar he ha0).continuousAt
  have hg : ContinuousAt (fun p => (primitiveResidual D e a0 supply p).2 i j)
      (0,(qstar,a0)) :=
    (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hc.snd)
  have hbase : 0 < (primitiveResidual D e a0 supply (0,(qstar,a0))).2 i j := by
    rw [primitiveResidual_zero]
    change 0 < (budgetValue e a0 (qstar,a0) i)^(-(D i).gamma)*qstar j-marginal (D i) (a0 i) j
    rw [budget_reference]
    nlinarith
  let U : Set (PrimitiveShock H J S × MarketState H J) :=
    {p | 0 < (primitiveResidual D e a0 supply p).2 i j}
  have hU : U ∈ 𝓝 (0,(qstar,a0)) := hg.eventually (Ioi_mem_nhds hbase)
  filter_upwards [all_actual_equilibria_near_boundary_reference D e a0 supply qstar
    he ha0 hstock hs hsupport U hU] with v hv
  intro h q c a hEq
  have hp := hv h q c a hEq
  change 0 < (primitiveResidual D e a0 supply (v,(q,a))).2 i j at hp
  rw [primitiveResidual_eq_actual] at hp
  change 0 < (budgetValue (currentResources e v) (initialPortfolio a0 v) (q,a) i)^
    (-(changedData D e a0 v h i).gamma)*q j-marginal (changedData D e a0 v h i) (a i) j at hp
  rw [equilibrium_budget_value _ _ _ _ _ _ _ hEq] at hp
  have hgap : 0 < q j*(c i)^(-(changedData D e a0 v h i).gamma)-
      marginal (changedData D e a0 v h i) (a i) j := by nlinarith
  exact (mul_eq_zero.mp (hEq.corner_conditions i j).2).resolve_right (ne_of_gt hgap)

end OverlapBoundary

#print axioms OverlapBoundary.positive_reference_owner
#print axioms OverlapBoundary.boundary_prices_tendsto_reference
#print axioms OverlapBoundary.all_actual_equilibria_near_boundary_reference
#print axioms OverlapBoundary.strict_nonowner_persists
