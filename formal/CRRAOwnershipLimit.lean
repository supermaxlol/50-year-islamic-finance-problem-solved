import OwnershipLimitTools
import Mathlib.Topology.Sequences

/-!
Connect positive-initial-ownership equilibria to nonnegative initial ownership
through a compact subsequence. Actual global optimality and corner conditions
are retained. No uniqueness of market prices or of a selected sequence is used.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipPositive OwnershipUniform
open OwnershipMarginal OwnershipUnfloored

namespace OwnershipLimit

section Geometry
variable {H J : Type*} [Fintype H] [Fintype J]

abbrev MarketPoint (H J : Type*) := (J → ℝ) × (H → ℝ) × (H → J → ℝ)

def boxBottom {e : H → ℝ} {supply : J → ℝ} (box : UniformBox e supply) :
    MarketPoint H J := (box.L, (fun _ => box.d), (fun _ _ => 0))

def boxTop {e : H → ℝ} {supply : J → ℝ} (box : UniformBox e supply) :
    MarketPoint H J := (box.B, (fun _ => ∑ i, e i), (fun _ j => supply j))

omit [Fintype J] in
theorem within_iff_interval {e : H → ℝ} {supply : J → ℝ}
    (box : UniformBox e supply) (z : MarketPoint H J) :
    Within box z.1 z.2.1 z.2.2 ↔ z ∈ Icc (boxBottom box) (boxTop box) := by
  constructor
  · intro h
    exact ⟨⟨fun j => (h.prices j).1,
      ⟨fun i => (h.consumption i).1, fun i j => (h.holdings i j).1⟩⟩,
      ⟨fun j => (h.prices j).2,
      ⟨fun i => (h.consumption i).2, fun i j => (h.holdings i j).2⟩⟩⟩
  · intro h
    exact ⟨fun j => ⟨h.1.1 j, h.2.1 j⟩,
      fun i => ⟨h.1.2.1 i, h.2.2.1 i⟩,
      fun i j => ⟨h.1.2.2 i j, h.2.2.2 i j⟩⟩

theorem bounded_subsequence {e : H → ℝ} {supply : J → ℝ}
    (box : UniformBox e supply) (z : ℕ → MarketPoint H J)
    (hz : ∀ n, Within box (z n).1 (z n).2.1 (z n).2.2) :
    ∃ z0 : MarketPoint H J, ∃ phi : ℕ → ℕ,
      Within box z0.1 z0.2.1 z0.2.2 ∧ StrictMono phi ∧
      Tendsto (fun n => z (phi n)) atTop (𝓝 z0) := by
  have hcompact : IsCompact (Icc (boxBottom box) (boxTop box)) := isCompact_Icc
  obtain ⟨z0, hz0, phi, hphi, hlim⟩ := hcompact.tendsto_subseq
    (fun n => (within_iff_interval box (z n)).mp (hz n))
  exact ⟨z0, phi, (within_iff_interval box z0).mpr hz0, hphi, hlim⟩

def redistributed (a0 : H → J → ℝ) (supply : J → ℝ)
    (t : ℝ) (i : H) (j : J) : ℝ :=
  (1-t)*a0 i j + t*(supply j / (Fintype.card H : ℝ))

section Nonempty
variable [Nonempty H]

omit [Fintype J] in
theorem redistributed_positive (a0 : H → J → ℝ) (supply : J → ℝ)
    (ha0 : ∀ i j, 0 ≤ a0 i j) (hs : ∀ j, 0 < supply j)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (i : H) (j : J) :
    0 < redistributed a0 supply t i j := by
  have hn : 0 < (Fintype.card H : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_pos.mpr ht1).le (ha0 i j))
    (mul_pos ht (div_pos (hs j) hn))

omit [Fintype J] in
theorem redistributed_clears (a0 : H → J → ℝ) (supply : J → ℝ)
    (hstock : ∀ j, ∑ i, a0 i j = supply j) (t : ℝ) (j : J) :
    ∑ i, redistributed a0 supply t i j = supply j := by
  have hn : (Fintype.card H : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [redistributed, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hstock j]
  field_simp [hn]
  ring

end Nonempty

omit [Fintype J] in
theorem redistributed_tendsto (a0 : H → J → ℝ) (supply : J → ℝ) (i : H) (j : J) :
    Tendsto (fun n => redistributed a0 supply (epsilon n) i j) atTop (𝓝 (a0 i j)) := by
  have ht : Tendsto (fun n => 1-epsilon n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub epsilon_tendsto
  have h1 := ht.mul (tendsto_const_nhds (x := a0 i j))
  have h2 := epsilon_tendsto.mul
    (tendsto_const_nhds (x := supply j / (Fintype.card H : ℝ)))
  simpa only [redistributed, one_mul, zero_mul, add_zero] using h1.add h2

end Geometry

section EconomicLimit
variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]

/-- A convergent sequence of actual equilibria in the accepted common box
remains an actual equilibrium, including at zero initial and final holdings. -/
theorem equilibrium_of_limits
    (D : H → Data J S) (e : H → ℝ) (supply : J → ℝ)
    (a0 : H → J → ℝ) (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (box : UniformBox e supply)
    (a0n an : ℕ → H → J → ℝ) (qn : ℕ → J → ℝ) (cn : ℕ → H → ℝ)
    (q : J → ℝ) (c : H → ℝ) (a : H → J → ℝ)
    (hEq : ∀ n, IsEquilibrium D e (a0n n) supply (qn n) (cn n) (an n))
    (hb : Within box q c a)
    (h0 : ∀ i j, Tendsto (fun n => a0n n i j) atTop (𝓝 (a0 i j)))
    (hq : ∀ j, Tendsto (fun n => qn n j) atTop (𝓝 (q j)))
    (hc : ∀ i, Tendsto (fun n => cn n i) atTop (𝓝 (c i)))
    (ha : ∀ i j, Tendsto (fun n => an n i j) atTop (𝓝 (a i j))) :
    IsEquilibrium D e a0 supply q c a := by
  have hqp : ∀ j, 0 < q j := fun j => (box.L_pos j).trans_le (hb.prices j).1
  have hcp : ∀ i, 0 < c i := fun i => box.d_pos.trans_le (hb.consumption i).1
  have hap : ∀ i j, 0 ≤ a i j := fun i j => (hb.holdings i j).1
  have hwealth : ∀ i, Tendsto (fun n => spending (qn n) (e i) (a0n n i))
      atTop (𝓝 (spending q (e i) (a0 i))) := fun i =>
    spending_tendsto hq tendsto_const_nhds (h0 i)
  have hcost : ∀ i, Tendsto (fun n => spending (qn n) (cn n i) (an n i))
      atTop (𝓝 (spending q (c i) (a i))) := fun i => spending_tendsto hq (hc i) (ha i)
  refine ⟨hqp, hcp, hap, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact le_of_tendsto_of_tendsto' (hcost i) (hwealth i) (fun n => (hEq n).affordable i)
  · intro i
    have hw : 0 < spending q (e i) (a0 i) := by
      exact add_pos_of_pos_of_nonneg (he i) (Finset.sum_nonneg
        (fun j _ => mul_nonneg (hqp j).le (ha0 i j)))
    exact actual_optimality_limit (D i) hw (hcp i) (hap i) hq (hwealth i) (hc i) (ha i)
      (fun n => (hEq n).optimal i)
  · have ht := tendsto_finsetSum Finset.univ (fun i _ => hc i)
    exact tendsto_nhds_unique_of_forall ht tendsto_const_nhds
      (fun n => (hEq n).consumption_clears)
  · intro j
    have ht := tendsto_finsetSum Finset.univ (fun i _ => ha i j)
    exact tendsto_nhds_unique_of_forall ht tendsto_const_nhds
      (fun n => (hEq n).ownership_clears j)
  · intro i j
    have hm := marginal_tendsto (D i) (hap i) (ha i) j
    have hcurrent := (hc i).rpow_const (p := -(D i).gamma) (Or.inl (ne_of_gt (hcp i)))
    have hproduct := (hq j).mul hcurrent
    refine ⟨le_of_tendsto_of_tendsto' hm hproduct
      (fun n => ((hEq n).corner_conditions i j).1), ?_⟩
    have ht := (ha i j).mul (hproduct.sub hm)
    exact tendsto_nhds_unique_of_forall ht tendsto_const_nhds
      (fun n => ((hEq n).corner_conditions i j).2)

section Market
variable [Nonempty H]

/-- Full uncapped household and market existence for nonnegative initial
ownership, positive original current resources and positive aggregate supplies.
No artificial floor, cap, assumed demand or assumed first-order system remains. -/
theorem nonnegative_initial_ownership_equilibrium
    (D : H → Data J S) (e : H → ℝ) (a0 : H → J → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0 < e i) (ha0 : ∀ i j, 0 ≤ a0 i j)
    (hs : ∀ j, 0 < supply j) (hstock : ∀ j, ∑ i, a0 i j = supply j) :
    ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
      IsEquilibrium D e a0 supply q c a := by
  classical
  obtain ⟨box, hfamily⟩ := uniformly_bounded_equilibrium_family D e supply he hs
  have hex : ∀ n : ℕ, ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
      IsEquilibrium D e (redistributed a0 supply (epsilon n)) supply q c a ∧
      Within box q c a := by
    intro n
    obtain ⟨q, c, a, hE, hB, _⟩ := hfamily (redistributed a0 supply (epsilon n))
      (redistributed_positive a0 supply ha0 hs (epsilon n) (epsilon_pos n) (epsilon_lt_one n))
      (redistributed_clears a0 supply hstock (epsilon n))
    exact ⟨q, c, a, hE, hB⟩
  choose qn cn an hE hB using hex
  let z : ℕ → MarketPoint H J := fun n => (qn n, cn n, an n)
  obtain ⟨z0, phi, hz0, hphi, hlim⟩ := bounded_subsequence box z (fun n => hB n)
  have hq : ∀ j, Tendsto (fun n => qn (phi n) j) atTop (𝓝 (z0.1 j)) :=
    fun j => tendsto_pi_nhds.mp hlim.fst_nhds j
  have hc : ∀ i, Tendsto (fun n => cn (phi n) i) atTop (𝓝 (z0.2.1 i)) :=
    fun i => tendsto_pi_nhds.mp hlim.snd_nhds.fst_nhds i
  have ha : ∀ i j, Tendsto (fun n => an (phi n) i j) atTop (𝓝 (z0.2.2 i j)) :=
    fun i j => tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim.snd_nhds.snd_nhds i) j
  refine ⟨z0.1, z0.2.1, z0.2.2, ?_⟩
  exact equilibrium_of_limits D e supply a0 he ha0 box
    (fun n => redistributed a0 supply (epsilon (phi n))) (fun n => an (phi n))
    (fun n => qn (phi n)) (fun n => cn (phi n)) z0.1 z0.2.1 z0.2.2
    (fun n => hE (phi n)) hz0
    (fun i j => (redistributed_tendsto a0 supply i j).comp hphi.tendsto_atTop)
    hq hc ha

end Market
end EconomicLimit

namespace Controls
open ObjectiveControls

def zeroInitialOwnership (i : Fin 2) (_ : Fin 2) : ℝ := if i = 0 then 0 else 1/2

theorem zero_initial_ownership_nonnegative (i j : Fin 2) :
    0 ≤ zeroInitialOwnership i j := by
  fin_cases i <;> norm_num [zeroInitialOwnership]

theorem zero_initial_ownership_clears (j : Fin 2) :
    ∑ i, zeroInitialOwnership i j = (1/2 : ℝ) := by
  norm_num [zeroInitialOwnership, Fin.sum_univ_two]

theorem zero_initial_ownership_is_genuine_boundary :
    (∀ j : Fin 2, zeroInitialOwnership 0 j = 0) ∧
    ¬ (∀ i j : Fin 2, 0 < zeroInitialOwnership i j) := by
  refine ⟨by intro j; norm_num [zeroInitialOwnership], ?_⟩
  intro h
  have hh := h 0 0
  norm_num [zeroInitialOwnership] at hh

theorem zero_initial_risky_overlap_equilibrium :
    ∃ q : Fin 2 → ℝ, ∃ c : Fin 2 → ℝ, ∃ a : Fin 2 → Fin 2 → ℝ,
      IsEquilibrium sampleData (fun i => 1 + (i.val : ℝ)) zeroInitialOwnership
        (fun _ => 1/2) q c a := by
  apply nonnegative_initial_ownership_equilibrium
  · intro i
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    linarith
  · exact zero_initial_ownership_nonnegative
  · intro j
    norm_num
  · exact zero_initial_ownership_clears

end Controls
end OwnershipLimit

#print axioms OwnershipLimit.within_iff_interval
#print axioms OwnershipLimit.bounded_subsequence
#print axioms OwnershipLimit.redistributed_positive
#print axioms OwnershipLimit.redistributed_clears
#print axioms OwnershipLimit.redistributed_tendsto
#print axioms OwnershipLimit.equilibrium_of_limits
#print axioms OwnershipLimit.nonnegative_initial_ownership_equilibrium
#print axioms OwnershipLimit.Controls.zero_initial_ownership_nonnegative
#print axioms OwnershipLimit.Controls.zero_initial_ownership_clears
#print axioms OwnershipLimit.Controls.zero_initial_ownership_is_genuine_boundary
#print axioms OwnershipLimit.Controls.zero_initial_risky_overlap_equilibrium
