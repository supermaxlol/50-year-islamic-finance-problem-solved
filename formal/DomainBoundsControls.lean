import CRRAUnflooredDomain
import CRRAOverlapMarginalBounds
import ObjectiveControls

noncomputable section
open scoped BigOperators
open Set OwnershipCRRA OwnershipUnfloored OwnershipMarginal OwnershipBridge

namespace DomainBoundsControls

variable {J S : Type*} [Fintype J] [Fintype S]

/- The new domain genuinely extends below the artificial current floor. -/
omit [Fintype S] in
theorem below_floor_is_economic_not_box (D : Data J S) :
    ∃ x : Option J → ℝ, x ∈ economicDomain D ∧ x none < 0 ∧
      ∀ M : ℝ, x ∉ box M := by
  let x := shiftedChoice D.delta (D.delta/2) (fun _ : J => 0)
  have hneg : x none < 0 := by
    dsimp [x, shiftedChoice]
    linarith [D.delta_pos]
  refine ⟨x, shiftedChoice_mem_domain D _ _
    (div_pos D.delta_pos (by norm_num)) (fun _ => le_rfl), hneg, ?_⟩
  intro M hx
  exact not_lt_of_ge ((hx none).1) hneg

/- Natural positivity of consumption is not removed with the artificial floor. -/
omit [Fintype S] in
theorem zero_consumption_not_economic (D : Data J S) (a : J → ℝ) :
    shiftedChoice D.delta 0 a ∉ economicDomain D := by
  intro h
  have hc := h.1
  norm_num [shiftedChoice] at hc

theorem zero_holdings_marginal_eq_upper (D : Data J S) (j : J) :
    marginal D (fun _ => 0) j = upper D j := by
  simp [marginal, upper, consumption]

/-- Positive ownership strictly lowers that asset's marginal future receipt
value below its zero-holdings upper bound. This is not an equilibrium price
ordering theorem. -/
theorem positive_ownership_strict_upper (D : Data J S) {a : J → ℝ}
    (ha : ∀ k, 0 ≤ a k) (j : J) (haj : 0 < a j) :
    marginal D a j < upper D j := by
  classical
  obtain ⟨s, hs⟩ := positive_payoff_in_each_column D j
  have hcons : D.income s < consumption D a s := by
    have hle := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => mul_nonneg (D.payoff_nonneg s k) (ha k)) (Finset.mem_univ j)
    have hp := mul_pos hs haj
    dsimp [consumption]
    linarith
  have hweak : ∀ r,
      D.weight r * D.payoff r j * (consumption D a r)^(-D.eta r) ≤
      D.weight r * D.payoff r j * (D.income r)^(-D.eta r) := by
    intro r
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (D.income_pos r) (income_le_consumption D ha r)
        (neg_nonpos.mpr (D.eta_pos r).le))
      (mul_nonneg (D.weight_pos r).le (D.payoff_nonneg r j))
  have hstrict : D.weight s * D.payoff s j * (consumption D a s)^(-D.eta s) <
      D.weight s * D.payoff s j * (D.income s)^(-D.eta s) :=
    mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow_of_neg (D.income_pos s) hcons (neg_neg_of_pos (D.eta_pos s)))
      (mul_pos (D.weight_pos s) hs)
  exact Finset.sum_lt_sum (fun r (_ : r ∈ (Finset.univ : Finset S)) => hweak r)
    ⟨s, Finset.mem_univ s, hstrict⟩

/-- Uses the already accepted common risky-overlap matrix and heterogeneous
curvatures above one; no matrix or equilibrium source is rebuilt. -/
theorem sample_primitive_bounds (i : Fin 2) (j : Fin 2) :
    0 < lower (ObjectiveControls.sampleData i) (fun _ => 1/2) j ∧
      lower (ObjectiveControls.sampleData i) (fun _ => 1/2) j ≤
        marginal (ObjectiveControls.sampleData i) (fun _ => 1/4) j ∧
      marginal (ObjectiveControls.sampleData i) (fun _ => 1/4) j <
        upper (ObjectiveControls.sampleData i) j := by
  have hb := marginal_bounds (ObjectiveControls.sampleData i)
    (a := fun _ => (1/4 : ℝ)) (supply := fun _ => (1/2 : ℝ))
    (by intro k; norm_num) (by intro k; norm_num) j
  exact ⟨hb.1, hb.2.1, positive_ownership_strict_upper
    (ObjectiveControls.sampleData i) (by intro k; norm_num) j (by norm_num)⟩

end DomainBoundsControls

#print axioms DomainBoundsControls.below_floor_is_economic_not_box
#print axioms DomainBoundsControls.zero_consumption_not_economic
#print axioms DomainBoundsControls.zero_holdings_marginal_eq_upper
#print axioms DomainBoundsControls.positive_ownership_strict_upper
#print axioms DomainBoundsControls.sample_primitive_bounds
