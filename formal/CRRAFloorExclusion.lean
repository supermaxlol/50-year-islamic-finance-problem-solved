import CRRAFeasibleTrades
import CRRAUnflooredDomain
import ObjectiveControls

/-!
Connect the actual trade inequalities to market-level removal of the artificial
floor and caps. Sufficient small-floor inequalities are stated entirely in
primitives, not as assumed price or demand conditions. Selection of such floors
for arbitrary primitive data and zero-initial-ownership limits are later steps.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipBridge OwnershipCRRA OwnershipMarginal OwnershipBounds
open OwnershipTrade OwnershipUnfloored

namespace OwnershipFloor

variable {J S : Type*} [Fintype J] [Fintype S]

theorem scale_negative_power {c gamma m q : ℝ} (hc : 0 < c)
    (h : m ≤ q * c^(-gamma)) : m * c^gamma ≤ q := by
  have hp : 0 < c^gamma := Real.rpow_pos_of_pos hc _
  have hi : c^(-gamma) * c^gamma = 1 := by
    rw [← Real.rpow_add hc]
    simp
  have hh := mul_le_mul_of_nonneg_right h hp.le
  simpa only [mul_assoc, hi, mul_one] using hh

theorem scale_negative_power_reverse {c gamma m q : ℝ} (hc : 0 < c)
    (h : q * c^(-gamma) ≤ m) : q ≤ m * c^gamma := by
  have hp : 0 < c^gamma := Real.rpow_pos_of_pos hc _
  have hi : c^(-gamma) * c^gamma = 1 := by
    rw [← Real.rpow_add hc]
    simp
  have hh := mul_le_mul_of_nonneg_right h hp.le
  simpa only [mul_assoc, hi, mul_one] using hh

theorem actual_trade_complementarity (D : Data J S) (M : ℝ)
    (ω x : Option J → ℝ) (q : J → ℝ) (j : J) (hq : 0 ≤ q j)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hfloor : 0 < x none) :
    marginal D (fun k => x (some k)) j ≤ q j * (x none + D.delta)^(-D.gamma) ∧
    x (some j) * (q j * (x none + D.delta)^(-D.gamma) -
      marginal D (fun k => x (some k)) j) = 0 := by
  refine ⟨buy_inequality D M ω x q j hopt hcap hfloor, ?_⟩
  by_cases hj : 0 < x (some j)
  · rw [owned_asset_euler_equality D M ω x q j hq hopt hcap hfloor hj]
    ring
  · have hz : x (some j) = 0 :=
      le_antisymm (not_lt.mp hj) (hopt.1 (some j)).1
    rw [hz, zero_mul]

theorem price_lower_from_large_consumer (D : Data J S) (M : ℝ)
    (ω x : Option J → ℝ) (q supply : J → ℝ) (j : J) (m L : ℝ)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hm : 0 < m) (hdelta : D.delta < m)
    (hlarge : m ≤ x none + D.delta)
    (hsupply : ∀ k, x (some k) ≤ supply k)
    (hL : L ≤ lower D supply j * m^D.gamma) : L ≤ q j := by
  have hf : 0 < x none := by linarith
  have hc : 0 < x none + D.delta := hm.trans_le hlarge
  have hbuy := buy_inequality D M ω x q j hopt hcap hf
  have hs := scale_negative_power hc hbuy
  have hb := marginal_bounds D (fun k => (hopt.1 (some k)).1) hsupply j
  have hp := Real.rpow_le_rpow hm.le hlarge D.gamma_pos.le
  have hD := mul_le_mul_of_nonneg_left hp hb.1.le
  have hM := mul_le_mul_of_nonneg_right hb.2.1 (Real.rpow_pos_of_pos hc D.gamma).le
  exact hL.trans (hD.trans (hM.trans hs))

theorem floor_household_owns_asset (D : Data J S) (M : ℝ)
    (ω x : Option J → ℝ) (q : J → ℝ)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hq : ∀ j, 0 ≤ q j)
    (hω0 : 0 < ω none) (hω : ∀ j, 0 ≤ ω (some j))
    (hfloor : x none = 0) : ∃ j, 0 < x (some j) := by
  classical
  by_contra hn
  have hz : ∀ j, x (some j) = 0 := fun j =>
    le_antisymm (not_lt.mp (not_exists.mp hn j)) (hopt.1 (some j)).1
  have hM : 0 < M := by simpa [hfloor] using hcap none
  let eps : ℝ := min M (ω none) / 2
  have heps : 0 < eps := div_pos (lt_min hM hω0) (by norm_num)
  have heM : eps ≤ M := by
    have hh := min_le_left M (ω none)
    dsimp [eps]
    linarith
  have heω : eps ≤ ω none := by
    have hh := min_le_right M (ω none)
    dsimp [eps]
    linarith
  let y : Option J → ℝ := fun g => match g with
    | none => eps
    | some _ => 0
  have hy : y ∈ box M := by
    intro g
    cases g with
    | none => exact ⟨heps.le, heM⟩
    | some _ => exact ⟨le_rfl, hM.le⟩
  have hb : cost q y ≤ cost q ω := by
    have hs : 0 ≤ ∑ j, q j * ω (some j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (hω j)
    simp only [cost, y, mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  have hxy : x ≤ y := by
    intro g
    cases g with
    | none => simpa [y, hfloor] using heps.le
    | some j => simp [y, hz j]
  have hne : x ≠ y := by
    intro heq
    have hh := congrFun heq none
    change x none = eps at hh
    rw [hfloor] at hh
    linarith
  have hbetter := objective_increasingOnBox D M x hopt.1 y hy hxy hne
  have hmax := hopt.2.2 y hy hb
  linarith

theorem floor_slack_from_price_lower (D : Data J S) (M : ℝ)
    (ω x : Option J → ℝ) (q L : J → ℝ)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hcap : ∀ g, x g < M) (hq : ∀ j, 0 ≤ q j)
    (hω0 : 0 < ω none) (hω : ∀ j, 0 ≤ ω (some j))
    (hprice : ∀ j, L j ≤ q j)
    (hsmall : ∀ j, upper D j * D.delta^D.gamma < L j) : 0 < x none := by
  by_contra hn
  have hz : x none = 0 := le_antisymm (not_lt.mp hn) (hopt.1 none).1
  obtain ⟨j, hj⟩ := floor_household_owns_asset D M ω x q hopt hcap hq hω0 hω hz
  have hs := sell_inequality D M ω x q j (hq j) hopt hcap hj
  rw [hz, zero_add] at hs
  have hscaled := scale_negative_power_reverse D.delta_pos hs
  have hu := marginal_le_upper D (fun k => (hopt.1 (some k)).1) j
  have hh := mul_le_mul_of_nonneg_right hu (Real.rpow_pos_of_pos D.delta_pos D.gamma).le
  have hqU := hscaled.trans hh
  exact (not_lt_of_ge (hprice j)) (hqU.trans_lt (hsmall j))

section Market
variable {H : Type*} [Fintype H] [Nonempty H]

omit [Fintype S] in
theorem some_consumer_above_mean (D : H → Data J S)
    (ω x : H → Option J → ℝ) (m : ℝ)
    (hclear : ∑ i, x i none = ∑ i, ω i none)
    (hmean : (Fintype.card H : ℝ) * m ≤ ∑ i, (ω i none + (D i).delta)) :
    ∃ i, m ≤ x i none + (D i).delta := by
  classical
  by_contra hn
  have hl : ∀ i, x i none + (D i).delta < m :=
    fun i => lt_of_not_ge (not_exists.mp hn i)
  have hs := Finset.sum_lt_sum
    (fun i (_ : i ∈ (Finset.univ : Finset H)) => (hl i).le)
    ⟨Classical.arbitrary H, Finset.mem_univ _, hl _⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  rw [Finset.sum_add_distrib, hclear] at hs
  rw [Finset.sum_add_distrib] at hmean
  linarith

/- This endpoint is uncapped in its conclusion. All additional sufficient
conditions involve only primitive data and the chosen temporary floors. It
still requires strictly positive individual initial ownership. -/
theorem uncapped_equilibrium_of_small_floors
    (D : H → Data J S) (M m : ℝ) (ω : H → Option J → ℝ) (L : J → ℝ)
    (hM : 0 ≤ M) (hm : 0 < m)
    (hω : ∀ i g, 0 < ω i g)
    (hcap : ∀ g, ∑ i, ω i g < M)
    (hmean : (Fintype.card H : ℝ) * m ≤ ∑ i, (ω i none + (D i).delta))
    (hdelta : ∀ i, (D i).delta < m)
    (hL : ∀ i j, L j ≤ lower (D i) (fun k => ∑ l, ω l (some k)) j * m^(D i).gamma)
    (hsmall : ∀ i j, upper (D i) j * (D i).delta^(D i).gamma < L j) :
    ∃ q : J → ℝ, ∃ c : H → ℝ, ∃ a : H → J → ℝ,
      (∀ j, 0 < q j) ∧ (∀ i, 0 < c i) ∧ (∀ i j, 0 ≤ a i j) ∧
      (∀ i, c i + ∑ j, q j * a i j ≤ (ω i none + (D i).delta) +
        ∑ j, q j * ω i (some j)) ∧
      (∀ i c', 0 < c' → ∀ a' : J → ℝ, (∀ j, 0 ≤ a' j) →
        c' + ∑ j, q j * a' j ≤ (ω i none + (D i).delta) +
          ∑ j, q j * ω i (some j) →
        economicValue (D i) c' a' ≤ economicValue (D i) (c i) (a i)) ∧
      (∑ i, c i = ∑ i, (ω i none + (D i).delta)) ∧
      (∀ j, ∑ i, a i j = ∑ i, ω i (some j)) ∧
      (∀ i j, marginal (D i) (a i) j ≤ q j * (c i)^(-(D i).gamma) ∧
        a i j * (q j * (c i)^(-(D i).gamma) - marginal (D i) (a i) j) = 0) ∧
      (∀ j, L j ≤ q j) := by
  classical
  obtain ⟨q, x, hq, hopt, hcurrent, hassets⟩ :=
    bounded_CRRA_ownership_equilibrium D M hM ω hω hcap
  have hc : ∀ g, ∑ i, x i g ≤ ∑ i, ω i g := by
    intro g
    cases g with
    | none => exact hcurrent.le
    | some j => exact (hassets j).le
  have hxcap := allocation_lt_cap M x ω (fun i => (hopt i).1) hc hcap
  have has : ∀ i j, x i (some j) ≤ ∑ l, ω l (some j) := by
    intro i j
    have hs := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset H)) => ((hopt k).1 (some j)).1)
      (Finset.mem_univ i)
    exact hs.trans (hc (some j))
  obtain ⟨k, hk⟩ := some_consumer_above_mean D ω x m hcurrent hmean
  have hprice : ∀ j, L j ≤ q j := fun j =>
    price_lower_from_large_consumer (D k) M (ω k) (x k) q
      (fun j => ∑ l, ω l (some j)) j m (L j) (hopt k) (hxcap k)
      hm (hdelta k) hk (has k) (hL k j)
  have hfloor : ∀ i, 0 < x i none := fun i =>
    floor_slack_from_price_lower (D i) M (ω i) (x i) q L (hopt i) (hxcap i)
      (fun j => (hq j).le) (hω i none) (fun j => (hω i (some j)).le) hprice (hsmall i)
  refine ⟨q, (fun i => x i none + (D i).delta), (fun i j => x i (some j)),
    hq, (fun i => add_pos (hfloor i) (D i).delta_pos),
    (fun i j => ((hopt i).1 (some j)).1), ?_, ?_, ?_, hassets, ?_, hprice⟩
  · intro i
    have hb := (hopt i).2.1
    linarith
  · intro i
    exact actual_budget_optimality_from_slack (D i) M (ω i) (x i) q
      (hopt i) (hfloor i) (hxcap i)
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcurrent]
  · intro i j
    exact actual_trade_complementarity (D i) M (ω i) (x i) q j (hq j).le
      (hopt i) (hxcap i) (hfloor i)

end Market

namespace Controls
open ObjectiveControls

/- Exact nonvacuity checks using the accepted risky, overlapping matrix.
Current resources are larger here than in Stage 184's separate capped example. -/
theorem sample_lower_condition (i j : Fin 2) :
    (1/100 : ℝ) ≤ lower (sampleData i) (fun _ => 1/2) j * (1 : ℝ)^(sampleData i).gamma := by
  fin_cases i <;> fin_cases j <;>
    norm_num [lower, marginal, consumption, sampleData, BridgeControls.riskyPayoff,
      Fin.sum_univ_two, Fin.sum_univ_three, Real.rpow_neg, Real.rpow_natCast]

theorem sample_small_floor (i j : Fin 2) :
    upper (sampleData i) j * (sampleData i).delta^(sampleData i).gamma < (1/100 : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [upper, sampleData, BridgeControls.riskyPayoff,
      Fin.sum_univ_three, Real.rpow_neg, Real.rpow_natCast]

theorem sample_uncapped_equilibrium :
    ∃ q : Fin 2 → ℝ, ∃ c : Fin 2 → ℝ, ∃ a : Fin 2 → Fin 2 → ℝ,
      (∀ j, 0 < q j) ∧ (∀ i, 0 < c i) ∧ (∀ i j, 0 ≤ a i j) ∧
      (∀ i, c i + ∑ j, q j * a i j ≤ (9/8 : ℝ) + ∑ j, q j * (1/4)) ∧
      (∀ i c', 0 < c' → ∀ a' : Fin 2 → ℝ, (∀ j, 0 ≤ a' j) →
        c' + ∑ j, q j * a' j ≤ (9/8 : ℝ) + ∑ j, q j * (1/4) →
        economicValue (sampleData i) c' a' ≤ economicValue (sampleData i) (c i) (a i)) ∧
      (∑ i, c i = (9/4 : ℝ)) ∧ (∀ j, ∑ i, a i j = (1/2 : ℝ)) ∧
      (∀ j, (1/100 : ℝ) ≤ q j) := by
  let ω : Fin 2 → Option (Fin 2) → ℝ := fun _ g => match g with
    | none => 1
    | some _ => 1/4
  have hL : ∀ i j, (1/100 : ℝ) ≤
      lower (sampleData i) (fun k => ∑ l, ω l (some k)) j * (1 : ℝ)^(sampleData i).gamma := by
    intro i j
    convert! sample_lower_condition i j using 1
    norm_num [ω, Fin.sum_univ_two]
  obtain ⟨q, c, a, hq, hc, ha, hbud, hopt, hcurrent, hassets, _, hprice⟩ :=
    uncapped_equilibrium_of_small_floors sampleData 4 1 ω (fun _ => (1/100 : ℝ))
      (by norm_num) (by norm_num)
      (by intro i g; cases g <;> norm_num [ω])
      (by intro g; cases g <;> norm_num [ω, Fin.sum_univ_two])
      (by norm_num [ω, sampleData, Fin.sum_univ_two])
      (by intro i; norm_num [sampleData]) hL sample_small_floor
  refine ⟨q, c, a, hq, hc, ha, ?_, ?_, ?_, ?_, hprice⟩
  · intro i
    convert! hbud i using 1
    norm_num [ω, sampleData]
  · intro i
    convert! hopt i using 1
    norm_num [ω, sampleData]
  · convert! hcurrent using 1
    norm_num [ω, sampleData, Fin.sum_univ_two]
  · intro j
    convert! hassets j using 1
    norm_num [ω, Fin.sum_univ_two]

end Controls
end OwnershipFloor

#print axioms OwnershipFloor.scale_negative_power
#print axioms OwnershipFloor.scale_negative_power_reverse
#print axioms OwnershipFloor.actual_trade_complementarity
#print axioms OwnershipFloor.price_lower_from_large_consumer
#print axioms OwnershipFloor.floor_household_owns_asset
#print axioms OwnershipFloor.floor_slack_from_price_lower
#print axioms OwnershipFloor.some_consumer_above_mean
#print axioms OwnershipFloor.uncapped_equilibrium_of_small_floors
#print axioms OwnershipFloor.Controls.sample_lower_condition
#print axioms OwnershipFloor.Controls.sample_small_floor
#print axioms OwnershipFloor.Controls.sample_uncapped_equilibrium
