import OverlapAllocationStability
import Mathlib.Topology.Sequences

/-!
All-equilibrium compact stability and global uniqueness in a parameter
neighborhood of an interior supported reference. Compactness is needed only
for allocations; prices are recovered from actual Euler equations after the
midpoint/Pareto argument identifies allocation limits. This is not uniqueness
throughout the unrestricted heterogeneous-overlap existence class.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipPositive
open OwnershipSupported OverlapLocal

namespace OverlapStability
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

abbrev Allocation (H J : Type*) := (H → ℝ) × (H → J → ℝ)

def allocationBottom : Allocation H J := (fun _ => 0,fun _ _ => 0)
def allocationTop (e : H → ℝ) (supply : J → ℝ) : Allocation H J :=
  (fun _ => ∑ i, e i,fun _ j => supply j)

theorem all_equilibrium_allocation_box (D : H → Data J S) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply q : J → ℝ) (c : H → ℝ) (a : H → J → ℝ)
    (hEq : IsEquilibrium D e a0 supply q c a) :
    (c,a) ∈ Icc (allocationBottom : Allocation H J) (allocationTop e supply) := by
  exact ⟨⟨fun i => (hEq.consumption_positive i).le,hEq.holdings_nonneg⟩,
    ⟨fun i => OwnershipUniform.consumption_le_total hEq i,
      fun i j => OwnershipUniform.holdings_le_supply hEq i j⟩⟩

theorem actual_allocation_subsequence (D : H → Data J S) (W : H → S → ℝ)
    (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (t : ℕ → ℝ) (hw : ∀ n i s, 0 < (D i).weight s+t n*W i s)
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (affineData D W (t n) (hw n)) e a0 supply
      (qn n) (cn n) (an n)) :
    ∃ z : Allocation H J, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun n => (cn (phi n),an (phi n))) atTop (𝓝 z) := by
  have hcompact : IsCompact
      (Icc (allocationBottom : Allocation H J) (allocationTop e supply)) := isCompact_Icc
  obtain ⟨z,_,phi,hphi,hlim⟩ := hcompact.tendsto_subseq
    (fun n => all_equilibrium_allocation_box (affineData D W (t n) (hw n))
      e a0 supply (qn n) (cn n) (an n) (hEq n))
  exact ⟨z,phi,hphi,hlim⟩

theorem prices_tendsto_reference [Nonempty H]
    (D : H → Data J S) (W : H → S → ℝ) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma))
    (t : ℕ → ℝ) (hw : ∀ n i s, 0 < (D i).weight s+t n*W i s)
    (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ) (an : ℕ → H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium (affineData D W (t n) (hw n)) e a0 supply
      (qn n) (cn n) (an n))
    (ht : Tendsto t atTop (𝓝 0))
    (hcn : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (e i)))
    (han : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a0 i j))) :
    ∀ j, Tendsto (fun n => qn n j) atTop (𝓝 (qstar j)) := by
  classical
  let i : H := Classical.choice ‹Nonempty H›
  intro j
  have hown : ∀ᶠ n in atTop, 0 < an n i j :=
    (han i j).eventually (Ioi_mem_nhds (ha0 i j))
  have hformula : (fun n => qn n j) =ᶠ[atTop]
      (fun n => marginal (affineData D W (t n) (hw n) i) (an n i) j /
        (cn n i)^(-(D i).gamma)) := by
    filter_upwards [hown] with n hn
    apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos
      ((hEq n).consumption_positive i) (-(D i).gamma)))).mpr
    exact (OwnershipUniform.owned_asset_euler (hEq n) i j hn).symm
  have hm := affine_marginal_tendsto D W i hw (fun j => (ha0 i j).le) ht (han i) j
  have hl := (hcn i).rpow_const (p := -(D i).gamma) (Or.inl (ne_of_gt (he i)))
  have hd := hm.div hl (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))
  have hval : marginal (D i) (a0 i) j / (e i)^(-(D i).gamma)=qstar j :=
    (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos (he i) (-(D i).gamma)))).mpr (heuler i j)
  rw [hval] at hd
  exact (tendsto_congr' hformula).mpr hd

theorem all_actual_equilibria_near_reference [Nonempty H]
    (D : H → Data J S) (W : H → S → ℝ) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma))
    (U : Set (ℝ × MarketState H J)) (hU : U ∈ 𝓝 (0,(qstar,a0))) :
    ∀ᶠ t in 𝓝 0, ∀ hw : ∀ i s, 0 < (D i).weight s+t*W i s,
      ∀ q c a, IsEquilibrium (affineData D W t hw) e a0 supply q c a →
        (t,(q,a)) ∈ U := by
  classical
  have hsupport : SupportsInitial D e a0 qstar := by
    intro i j
    rw [heuler i j]
    exact ⟨le_rfl,by ring⟩
  by_contra hn
  have hfreq : ∃ᶠ t in 𝓝 (0 : ℝ), ¬ (∀ hw : ∀ i s, 0 < (D i).weight s+t*W i s,
      ∀ q c a, IsEquilibrium (affineData D W t hw) e a0 supply q c a → (t,(q,a)) ∈ U) :=
    Filter.not_eventually.mp hn
  obtain ⟨t,ht,hbad⟩ := exists_seq_forall_of_frequently hfreq
  have hex : ∀ n, ∃ hw : ∀ i s, 0 < (D i).weight s+t n*W i s,
      ∃ q c a, IsEquilibrium (affineData D W (t n) hw) e a0 supply q c a ∧
        (t n,(q,a)) ∉ U := by
    intro n
    simpa only [not_forall,not_imp,exists_prop] using hbad n
  choose hw qn cn an hEq hout using hex
  obtain ⟨z,phi,hphi,hlim⟩ := actual_allocation_subsequence D W e a0 supply t hw qn cn an hEq
  have hc : ∀ i, Tendsto (fun n => cn (phi n) i) atTop (𝓝 (z.1 i)) :=
    fun i => (tendsto_pi_nhds.mp hlim.fst_nhds) i
  have ha : ∀ i j, Tendsto (fun n => an (phi n) i j) atTop (𝓝 (z.2 i j)) :=
    fun i j => (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hlim.snd_nhds) i)) j
  have ht' := ht.comp hphi.tendsto_atTop
  obtain ⟨hceq,haeq⟩ := allocation_limit_reference D W e a0 supply qstar he
    (fun i j => (ha0 i j).le) hstock hsupport (fun n => t (phi n))
    (fun n => hw (phi n)) (fun n => qn (phi n)) (fun n => cn (phi n))
    (fun n => an (phi n)) (fun n => hEq (phi n)) z.1 z.2 ht' hc ha
  rw [hceq] at hc
  rw [haeq] at ha
  have hq := prices_tendsto_reference D W e a0 supply qstar he ha0 heuler
    (fun n => t (phi n)) (fun n => hw (phi n)) (fun n => qn (phi n))
    (fun n => cn (phi n)) (fun n => an (phi n)) (fun n => hEq (phi n)) ht' hc ha
  have hq' : Tendsto (fun n => qn (phi n)) atTop (𝓝 qstar) := tendsto_pi_nhds.mpr hq
  have ha' : Tendsto (fun n => an (phi n)) atTop (𝓝 a0) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (ha i))
  have hp : Tendsto (fun n => (t (phi n),(qn (phi n),an (phi n)))) atTop
      (𝓝 (0,(qstar,a0))) := ht'.prodMk_nhds (hq'.prodMk_nhds ha')
  have hev := hp.eventually hU
  obtain ⟨n,hn⟩ := hev.exists
  exact hout (phi n) hn

theorem affine_global_actual_family [Nonempty H]
    (D : H → Data J S) (W : H → S → ℝ) (e : H → ℝ)
    (a0 : H → J → ℝ) (supply qstar : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 < a0 i j) (hq : ∀ j, 0 < qstar j)
    (hstock : ∀ j, ∑ i, a0 i j=supply j)
    (heuler : ∀ i j, marginal (D i) (a0 i) j=qstar j*(e i)^(-(D i).gamma)) :
    ∃ psi : ℝ → MarketState H J, psi 0=(qstar,a0) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ t in 𝓝 0, ∃ hw : ∀ i s, 0 < (D i).weight s+t*W i s,
        IsEquilibrium (affineData D W t hw) e a0 supply
          (psi t).1 (budgetValue e a0 (psi t)) (psi t).2 ∧
        affineResidual D W e a0 supply (t,psi t)=0 ∧
        ∀ q c a, IsEquilibrium (affineData D W t hw) e a0 supply q c a →
          q=(psi t).1 ∧ c=budgetValue e a0 (psi t) ∧ a=(psi t).2) := by
  obtain ⟨psi,hpsi,hcd,hcert,hgraph⟩ := affine_local_actual_family D W e a0 supply qstar
    he ha0 hq hstock heuler
  let U : Set (ℝ × MarketState H J) := {p | ∀ hw : ∀ i s,
      0 < (D i).weight s+p.1*W i s, ∀ c : H → ℝ,
      IsEquilibrium (affineData D W p.1 hw) e a0 supply p.2.1 c p.2.2 →
        p.2=psi p.1 ∧ c=budgetValue e a0 p.2}
  have hU : U ∈ 𝓝 (0,(qstar,a0)) := hgraph
  have hnear := all_actual_equilibria_near_reference D W e a0 supply qstar
    he ha0 hstock heuler U hU
  refine ⟨psi,hpsi,hcd,?_⟩
  filter_upwards [hcert,hnear] with t hct hnt
  obtain ⟨hw,hEq,hr⟩ := hct
  refine ⟨hw,hEq,hr,?_⟩
  intro q c a hEq'
  have hh := hnt hw q c a hEq'
  change (∀ hw : ∀ i s, 0 < (D i).weight s+t*W i s,
    ∀ c : H → ℝ, IsEquilibrium (affineData D W t hw) e a0 supply q c a →
      (q,a)=psi t ∧ c=budgetValue e a0 (q,a)) at hh
  obtain ⟨hz,hc⟩ := hh hw c hEq'
  exact ⟨congrArg Prod.fst hz,by simpa only [hz] using hc,congrArg Prod.snd hz⟩

theorem interior_globally_unique_trading_family :
    ∃ psi : ℝ → MarketState (Fin 2) (Fin 2),
      psi 0=(CornerControl.qstar,InteriorControl.initial) ∧ ContDiffAt ℝ 1 psi 0 ∧
      (∀ᶠ t in 𝓝 0, ∃ hw : ∀ i s, 0 < (InteriorControl.D i).weight s+t*interiorShock i s,
        IsEquilibrium (affineData InteriorControl.D interiorShock t hw)
          InteriorControl.endowment InteriorControl.initial CornerControl.supply
          (psi t).1 (budgetValue InteriorControl.endowment InteriorControl.initial (psi t))
          (psi t).2 ∧
        (∀ q c a, IsEquilibrium (affineData InteriorControl.D interiorShock t hw)
          InteriorControl.endowment InteriorControl.initial CornerControl.supply q c a →
          q=(psi t).1 ∧ c=budgetValue InteriorControl.endowment InteriorControl.initial (psi t) ∧
          a=(psi t).2) ∧
        (t ≠ 0 → (psi t).2 ≠ InteriorControl.initial)) := by
  have heuler : ∀ i j, marginal (InteriorControl.D i) (InteriorControl.initial i) j=
      CornerControl.qstar j*(InteriorControl.endowment i)^(-(InteriorControl.D i).gamma) := by
    intro i j
    have hh := (InteriorControl.primitive_support i j).2
    have hz := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (InteriorControl.initial_interior i j))
    linarith
  obtain ⟨psi,hpsi,hcd,hcert⟩ := affine_global_actual_family InteriorControl.D interiorShock
    InteriorControl.endowment InteriorControl.initial CornerControl.supply CornerControl.qstar
    (by intro i; norm_num [InteriorControl.endowment]) InteriorControl.initial_interior
    (by intro j; fin_cases j <;> norm_num [CornerControl.qstar])
    (by intro j; fin_cases j <;>
      norm_num [InteriorControl.initial,CornerControl.supply,Fin.sum_univ_succ]) heuler
  refine ⟨psi,hpsi,hcd,?_⟩
  filter_upwards [hcert] with t ht
  obtain ⟨hw,hEq,hr,hu⟩ := ht
  exact ⟨hw,hEq,hu,fun hne => interior_nonzero_root_trades t (psi t) hr hne⟩

end OverlapStability

#print axioms OverlapStability.all_equilibrium_allocation_box
#print axioms OverlapStability.actual_allocation_subsequence
#print axioms OverlapStability.prices_tendsto_reference
#print axioms OverlapStability.all_actual_equilibria_near_reference
#print axioms OverlapStability.affine_global_actual_family
#print axioms OverlapStability.interior_globally_unique_trading_family
