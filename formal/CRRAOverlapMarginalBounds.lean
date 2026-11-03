import CRRAOwnershipObjective

/-!
Primitive positive marginal-value bounds for genuinely overlapping productive
payoffs. These are computed from the actual utility primitives, not assumed
equilibrium prices or assumed first-order conditions. No cap on CRRA curvature.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipCRRA

namespace OwnershipMarginal

variable {J S : Type*} [Fintype J] [Fintype S]

def consumption (D : Data J S) (a : J → ℝ) (s : S) : ℝ :=
  D.income s + ∑ j, D.payoff s j * a j

def marginal (D : Data J S) (a : J → ℝ) (j : J) : ℝ :=
  ∑ s, D.weight s * D.payoff s j * (consumption D a s) ^ (-D.eta s)

def upper (D : Data J S) (j : J) : ℝ :=
  ∑ s, D.weight s * D.payoff s j * (D.income s) ^ (-D.eta s)

def lower (D : Data J S) (supply : J → ℝ) (j : J) : ℝ :=
  marginal D supply j

omit [Fintype S] in
theorem income_le_consumption (D : Data J S) {a : J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (s : S) : D.income s ≤ consumption D a s := by
  have hs : 0 ≤ ∑ j, D.payoff s j * a j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (D.payoff_nonneg s j) (ha j)
  dsimp [consumption]
  linarith

omit [Fintype S] in
theorem consumption_positive (D : Data J S) {a : J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (s : S) : 0 < consumption D a s :=
  lt_of_lt_of_le (D.income_pos s) (income_le_consumption D ha s)

omit [Fintype S] in
theorem consumption_monotone (D : Data J S) : Monotone (consumption D) := by
  intro a b hab s
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (hab j) (D.payoff_nonneg s j))
  dsimp [consumption]
  linarith

omit [Fintype S] in
theorem positive_payoff_in_each_column (D : Data J S) (j : J) :
    ∃ s, 0 < D.payoff s j := by
  classical
  by_contra hn
  have hz : ∀ s, D.payoff s j = 0 := fun s =>
    le_antisymm (not_lt.mp (not_exists.mp hn s)) (D.payoff_nonneg s j)
  let e : J → ℝ := Function.update (fun _ => 0) j 1
  have hmap : (fun s => ∑ k, D.payoff s k * e k) =
      (fun s => ∑ k, D.payoff s k * (0 : J → ℝ) k) := by
    funext s
    dsimp [e]
    rw [OwnershipBridge.cost_update]
    simp [hz s]
  have he := D.payoff_injective hmap
  have hj := congrFun he j
  norm_num [e] at hj

theorem marginal_positive (D : Data J S) {a : J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (j : J) : 0 < marginal D a j := by
  classical
  obtain ⟨s, hs⟩ := positive_payoff_in_each_column D j
  apply Finset.sum_pos'
  · intro r _
    exact mul_nonneg (mul_nonneg (D.weight_pos r).le (D.payoff_nonneg r j))
      (Real.rpow_pos_of_pos (consumption_positive D ha r) _).le
  · exact ⟨s, Finset.mem_univ s,
      mul_pos (mul_pos (D.weight_pos s) hs)
        (Real.rpow_pos_of_pos (consumption_positive D ha s) _)⟩

theorem upper_positive (D : Data J S) (j : J) : 0 < upper D j := by
  classical
  obtain ⟨s, hs⟩ := positive_payoff_in_each_column D j
  apply Finset.sum_pos'
  · intro r _
    exact mul_nonneg (mul_nonneg (D.weight_pos r).le (D.payoff_nonneg r j))
      (Real.rpow_pos_of_pos (D.income_pos r) _).le
  · exact ⟨s, Finset.mem_univ s,
      mul_pos (mul_pos (D.weight_pos s) hs) (Real.rpow_pos_of_pos (D.income_pos s) _)⟩

theorem marginal_le_upper (D : Data J S) {a : J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (j : J) : marginal D a j ≤ upper D j := by
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (D.income_pos s) (income_le_consumption D ha s)
      (neg_nonpos.mpr (D.eta_pos s).le))
    (mul_nonneg (D.weight_pos s).le (D.payoff_nonneg s j))

theorem marginal_antitone (D : Data J S) {a b : J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hab : a ≤ b) (j : J) : marginal D b j ≤ marginal D a j := by
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (consumption_positive D ha s)
      (consumption_monotone D hab s) (neg_nonpos.mpr (D.eta_pos s).le))
    (mul_nonneg (D.weight_pos s).le (D.payoff_nonneg s j))

theorem marginal_bounds (D : Data J S) {a supply : J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (has : a ≤ supply) (j : J) :
    0 < lower D supply j ∧ lower D supply j ≤ marginal D a j ∧
      marginal D a j ≤ upper D j := by
  have hs : ∀ k, 0 ≤ supply k := fun k => (ha k).trans (has k)
  exact ⟨marginal_positive D hs j, marginal_antitone D ha has j,
    marginal_le_upper D ha j⟩

end OwnershipMarginal

#print axioms OwnershipMarginal.income_le_consumption
#print axioms OwnershipMarginal.consumption_positive
#print axioms OwnershipMarginal.consumption_monotone
#print axioms OwnershipMarginal.positive_payoff_in_each_column
#print axioms OwnershipMarginal.marginal_positive
#print axioms OwnershipMarginal.upper_positive
#print axioms OwnershipMarginal.marginal_le_upper
#print axioms OwnershipMarginal.marginal_antitone
#print axioms OwnershipMarginal.marginal_bounds
