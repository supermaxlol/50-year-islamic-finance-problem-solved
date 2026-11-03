import CRRAPositiveOwnershipExistence

/-!
Uniform compact bounds for actual uncapped equilibria. The bounds are chosen
before redistributing a fixed positive aggregate asset supply. No quantitative
lower bound on individual initial ownership is imposed. The zero-initial-share
limiting theorem is not asserted here.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipFloor
open OwnershipFloorChoice OwnershipPositive

namespace OwnershipUniform

variable {H J S : Type*} [Fintype H] [Fintype J] [Fintype S]
variable {D : H → Data J S} {e : H → ℝ} {a0 : H → J → ℝ}
variable {supply q : J → ℝ} {c : H → ℝ} {a : H → J → ℝ}

/-- Actual household optimality leaves no unused current budget. -/
theorem budget_exhausted (hEq : IsEquilibrium D e a0 supply q c a) (i : H) :
    c i + ∑ j, q j * a i j = e i + ∑ j, q j * a0 i j := by
  apply le_antisymm (hEq.affordable i)
  by_contra hn
  have hgap : 0 < (e i + ∑ j, q j * a0 i j) -
      (c i + ∑ j, q j * a i j) := sub_pos.mpr (lt_of_not_ge hn)
  let d := (e i + ∑ j, q j * a0 i j) - (c i + ∑ j, q j * a i j)
  have hd : 0 < d := hgap
  have hc' : 0 < c i + d := add_pos (hEq.consumption_positive i) hd
  have hb : c i + d + ∑ j, q j * a i j ≤ e i + ∑ j, q j * a0 i j := by
    dsimp [d]
    linarith
  have ho := hEq.optimal i (c i + d) hc' (a i) (hEq.holdings_nonneg i) hb
  have hu := utility_strictMonoOn (D i).gamma (hEq.consumption_positive i) hc'
    (lt_add_of_pos_right (c i) hd)
  unfold economicValue at ho
  linarith

theorem owned_asset_euler (hEq : IsEquilibrium D e a0 supply q c a)
    (i : H) (j : J) (hown : 0 < a i j) :
    marginal (D i) (a i) j = q j * (c i)^(-(D i).gamma) := by
  have hz := (hEq.corner_conditions i j).2
  have he := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hown)
  linarith

theorem consumption_le_total (hEq : IsEquilibrium D e a0 supply q c a) (i : H) :
    c i ≤ ∑ k, e k := by
  classical
  calc
    c i ≤ ∑ k, c k := Finset.single_le_sum
      (fun k _ => (hEq.consumption_positive k).le) (Finset.mem_univ i)
    _ = ∑ k, e k := hEq.consumption_clears

theorem holdings_le_supply (hEq : IsEquilibrium D e a0 supply q c a)
    (i : H) (j : J) : a i j ≤ supply j := by
  classical
  calc
    a i j ≤ ∑ k, a k j := Finset.single_le_sum
      (fun k _ => hEq.holdings_nonneg k j) (Finset.mem_univ i)
    _ = supply j := hEq.ownership_clears j

theorem some_positive_owner (hEq : IsEquilibrium D e a0 supply q c a)
    (j : J) (hs : 0 < supply j) : ∃ i, 0 < a i j := by
  by_contra hn
  push Not at hn
  have hz : (∑ i, a i j) ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
  rw [hEq.ownership_clears j] at hz
  linarith

theorem owned_price_upper (hEq : IsEquilibrium D e a0 supply q c a)
    (i : H) (j : J) (hown : 0 < a i j) :
    q j ≤ upper (D i) j * (∑ k, e k)^(D i).gamma := by
  have hu := marginal_le_upper (D i) (hEq.holdings_nonneg i) j
  rw [owned_asset_euler hEq i j hown] at hu
  have hp := scale_negative_power_reverse (hEq.consumption_positive i) hu
  have hpow := Real.rpow_le_rpow (hEq.consumption_positive i).le
    (consumption_le_total hEq i) (D i).gamma_pos.le
  exact hp.trans (mul_le_mul_of_nonneg_left hpow (upper_positive (D i) j).le)

theorem primitive_price_majorant (D : H → Data J S) (e : H → ℝ) :
    ∃ B : J → ℝ, (∀ j, 0 < B j) ∧
      ∀ i j, upper (D i) j * (∑ k, e k)^(D i).gamma < B j := by
  have h : ∀ j, ∃ B : ℝ, 0 < B ∧
      ∀ i, upper (D i) j * (∑ k, e k)^(D i).gamma < B := by
    intro j
    exact finite_positive_majorant (fun i => upper (D i) j * (∑ k, e k)^(D i).gamma)
  choose B hB hbound using h
  exact ⟨B, hB, fun i j => hbound j i⟩

theorem price_below_majorant (hEq : IsEquilibrium D e a0 supply q c a)
    (B : J → ℝ)
    (hB : ∀ i j, upper (D i) j * (∑ k, e k)^(D i).gamma < B j)
    (hs : ∀ j, 0 < supply j) : ∀ j, q j < B j := by
  intro j
  obtain ⟨i, hi⟩ := some_positive_owner hEq j (hs j)
  exact (owned_price_upper hEq i j hi).trans_lt (hB i j)

/-- A household cannot approach zero consumption while these common price
minorants hold, even if its initial shares approach zero. -/
theorem consumption_above_prepared_floor
    (P : Prepared D e supply) (hEq : IsEquilibrium D e a0 supply q c a)
    (ha0 : ∀ i j, 0 ≤ a0 i j) (hL : ∀ j, P.L j ≤ q j) (i : H) :
    P.delta < c i := by
  by_contra hn
  have hcd : c i ≤ P.delta := not_lt.mp hn
  by_cases hown : ∃ j, 0 < a i j
  · obtain ⟨j, hj⟩ := hown
    have hu := marginal_le_upper (D i) (hEq.holdings_nonneg i) j
    rw [owned_asset_euler hEq i j hj] at hu
    have hp := scale_negative_power_reverse (hEq.consumption_positive i) hu
    have hpow := Real.rpow_le_rpow (hEq.consumption_positive i).le hcd
      (D i).gamma_pos.le
    have hq : q j ≤ upper (D i) j * P.delta^(D i).gamma :=
      hp.trans (mul_le_mul_of_nonneg_left hpow (upper_positive (D i) j).le)
    exact (not_lt_of_ge (hL j)) (hq.trans_lt (P.small_floor i j))
  · push Not at hown
    have haz : ∀ j, a i j = 0 := fun j =>
      le_antisymm (hown j) (hEq.holdings_nonneg i j)
    have hb := budget_exhausted hEq i
    have hwealth : 0 ≤ ∑ j, q j * a0 i j := Finset.sum_nonneg
      (fun j _ => mul_nonneg (hEq.prices_positive j).le (ha0 i j))
    simp only [haz, mul_zero, Finset.sum_const_zero, add_zero] at hb
    have he : P.delta < e i := P.delta_lt_m.trans (P.m_lt_endowment i)
    linarith

/- A closed finite-dimensional box; its positive lower bounds exclude a
zero-price or zero-consumption limit. -/
structure UniformBox (e : H → ℝ) (supply : J → ℝ) where
  L : J → ℝ
  B : J → ℝ
  d : ℝ
  L_pos : ∀ j, 0 < L j
  B_pos : ∀ j, 0 < B j
  d_pos : 0 < d

structure Within (box : UniformBox e supply) (q : J → ℝ)
    (c : H → ℝ) (a : H → J → ℝ) : Prop where
  prices : ∀ j, q j ∈ Icc (box.L j) (box.B j)
  consumption : ∀ i, c i ∈ Icc box.d (∑ k, e k)
  holdings : ∀ i j, a i j ∈ Icc 0 (supply j)

section Market
variable [Nonempty H]

/-- Common bounds are selected before every strictly positive ownership
redistribution, with no common positive lower bound on individual shares. -/
theorem uniformly_bounded_equilibrium_family
    (D : H → Data J S) (e : H → ℝ) (supply : J → ℝ)
    (he : ∀ i, 0 < e i) (hs : ∀ j, 0 < supply j) :
    ∃ box : UniformBox e supply,
      ∀ a0 : H → J → ℝ, (∀ i j, 0 < a0 i j) →
        (∀ j, ∑ i, a0 i j = supply j) →
        ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
          IsEquilibrium D e a0 supply q c a ∧ Within box q c a ∧
          (∀ i, box.d < c i) ∧ (∀ j, q j < box.B j) ∧
          (∀ i, c i + ∑ j, q j * a i j = e i + ∑ j, q j * a0 i j) := by
  obtain ⟨P⟩ := prepare_floors D e supply he (fun j => (hs j).le)
  obtain ⟨B, hB, hbound⟩ := primitive_price_majorant D e
  let box : UniformBox e supply := ⟨P.L, B, P.delta, P.L_pos, hB, P.delta_pos⟩
  refine ⟨box, ?_⟩
  intro a0 ha0 hstock
  obtain ⟨q, c, a, hEq, hL⟩ := equilibrium_from_preparation D e supply P a0 ha0 hstock
  have hc : ∀ i, P.delta < c i := consumption_above_prepared_floor P hEq
    (fun i j => (ha0 i j).le) hL
  have hq : ∀ j, q j < B j := price_below_majorant hEq B hbound hs
  refine ⟨q, c, a, hEq, ?_, hc, hq, budget_exhausted hEq⟩
  exact ⟨fun j => ⟨hL j, (hq j).le⟩,
    fun i => ⟨(hc i).le, consumption_le_total hEq i⟩,
    fun i j => ⟨hEq.holdings_nonneg i j, holdings_le_supply hEq i j⟩⟩

end Market

namespace Controls
open ObjectiveControls

def nearZeroOwnership (t : ℝ) (i : Fin 2) (_ : Fin 2) : ℝ :=
  if i = 0 then t else 1/2 - t

theorem near_zero_ownership_positive (t : ℝ) (ht : 0 < t) (hu : t < 1/2)
    (i j : Fin 2) : 0 < nearZeroOwnership t i j := by
  fin_cases i <;> simp only [nearZeroOwnership] <;> norm_num <;> linarith

theorem near_zero_ownership_clears (t : ℝ) (j : Fin 2) :
    ∑ i, nearZeroOwnership t i j = (1/2 : ℝ) := by
  simp [nearZeroOwnership, Fin.sum_univ_two]

theorem uniform_risky_overlap_example :
    ∃ box : UniformBox (fun i : Fin 2 => 1 + (i.val : ℝ)) (fun _ : Fin 2 => 1/2),
      ∀ t : ℝ, 0 < t → t < 1/2 →
        ∃ q : Fin 2 → ℝ, ∃ c : Fin 2 → ℝ, ∃ a : Fin 2 → Fin 2 → ℝ,
          IsEquilibrium sampleData (fun i => 1 + (i.val : ℝ))
            (nearZeroOwnership t) (fun _ => 1/2) q c a ∧ Within box q c a := by
  have he : ∀ i : Fin 2, 0 < 1 + (i.val : ℝ) := by
    intro i
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨box, hfamily⟩ := uniformly_bounded_equilibrium_family sampleData
    (fun i : Fin 2 => 1 + (i.val : ℝ)) (fun _ : Fin 2 => (1/2 : ℝ)) he
    (by intro j; norm_num)
  refine ⟨box, ?_⟩
  intro t ht hu
  obtain ⟨q, c, a, hEq, hb, _⟩ := hfamily (nearZeroOwnership t)
    (near_zero_ownership_positive t ht hu) (near_zero_ownership_clears t)
  exact ⟨q, c, a, hEq, hb⟩

/-- Positive aggregate supply, not just nonnegative supply, is what forces
some household to own each asset. -/
theorem zero_supply_has_no_positive_owner :
    (∀ i : Fin 2, 0 ≤ (fun _ : Fin 2 => (0 : ℝ)) i) ∧
    (∑ i : Fin 2, (fun _ : Fin 2 => (0 : ℝ)) i) = 0 ∧
    ¬ (∃ i : Fin 2, 0 < (fun _ : Fin 2 => (0 : ℝ)) i) := by
  norm_num

end Controls
end OwnershipUniform

#print axioms OwnershipUniform.budget_exhausted
#print axioms OwnershipUniform.owned_asset_euler
#print axioms OwnershipUniform.consumption_le_total
#print axioms OwnershipUniform.holdings_le_supply
#print axioms OwnershipUniform.some_positive_owner
#print axioms OwnershipUniform.owned_price_upper
#print axioms OwnershipUniform.primitive_price_majorant
#print axioms OwnershipUniform.price_below_majorant
#print axioms OwnershipUniform.consumption_above_prepared_floor
#print axioms OwnershipUniform.uniformly_bounded_equilibrium_family
#print axioms OwnershipUniform.Controls.near_zero_ownership_positive
#print axioms OwnershipUniform.Controls.near_zero_ownership_clears
#print axioms OwnershipUniform.Controls.uniform_risky_overlap_example
#print axioms OwnershipUniform.Controls.zero_supply_has_no_positive_owner
