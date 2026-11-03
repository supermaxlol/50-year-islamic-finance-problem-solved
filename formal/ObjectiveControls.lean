import CRRAOwnershipObjective
import BridgeControls

noncomputable section
open scoped BigOperators
open Set OwnershipBridge OwnershipCRRA

namespace ObjectiveControls

/-- Two heterogeneous households; every current/future curvature exceeds one.
The same genuinely risky, overlapping matrix is used by both households. -/
def sampleData (i : Fin 2) : OwnershipCRRA.Data (Fin 2) (Fin 3) where
  delta := 1/8
  gamma := 2 + (i.val : ℝ)
  eta := fun _ => 3 + (i.val : ℝ)
  income := fun s => 2 + (s.val : ℝ) + (i.val : ℝ)
  weight := fun _ => 1 + (i.val : ℝ)
  payoff := BridgeControls.riskyPayoff
  delta_pos := by norm_num
  gamma_pos := by have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _; linarith
  eta_pos := by intro s; have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _; linarith
  income_pos := by
    intro s
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hs : 0 ≤ (s.val : ℝ) := Nat.cast_nonneg _
    linarith
  weight_pos := by intro s; have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _; linarith
  payoff_nonneg := by
    intro s j
    fin_cases s <;> fin_cases j <;> norm_num [BridgeControls.riskyPayoff]
  payoff_injective := by
    intro x y h
    exact BridgeControls.risky_full_column_rank x y (fun s => congrFun h s)

theorem risky_CRRA_two_household_equilibrium :
    ∃ q : Fin 2 → ℝ, ∃ x : Fin 2 → Option (Fin 2) → ℝ,
      (∀ j, 0 < q j) ∧
      (∀ i, IsNumeraireOptimal 2 (fun _ => 1/4)
        (objective (sampleData i)) q (x i)) ∧
      (∑ i, x i none = (1/2 : ℝ)) ∧
      (∀ j, ∑ i, x i (some j) = (1/2 : ℝ)) := by
  obtain ⟨q, x, hq, hopt, hc, ha⟩ := bounded_CRRA_ownership_equilibrium
    sampleData 2 (by norm_num) (fun _ : Fin 2 => fun _ => (1/4 : ℝ))
    (by intros; norm_num) (by intro g; norm_num [Fin.sum_univ_two])
  refine ⟨q, x, hq, hopt, ?_, fun j => ?_⟩
  · calc
      (∑ i, x i none) = ∑ _ : Fin 2, (1/4 : ℝ) := hc
      _ = (1/2 : ℝ) := by norm_num [Fin.sum_univ_two]
  · calc
      (∑ i, x i (some j)) = ∑ _ : Fin 2, (1/4 : ℝ) := ha j
      _ = (1/2 : ℝ) := by norm_num [Fin.sum_univ_two]

theorem sample_no_nonzero_certain_receipt (i : Fin 2) (a : Fin 2 → ℝ) (k : ℝ)
    (h : ∀ s, ∑ j, (sampleData i).payoff s j * a j = k) : a = 0 ∧ k = 0 :=
  BridgeControls.risky_no_nonzero_certain_receipt a k h

/-- Clipping is a continuity extension, not globally concave preferences. -/
theorem clipped_log_not_concave :
    ¬ ConcaveOn ℝ univ (fun x : ℝ => utility 1 (max x 1)) := by
  intro h
  have hm := h.2 (show (0 : ℝ) ∈ (univ : Set ℝ) from mem_univ _)
    (show (2 : ℝ) ∈ (univ : Set ℝ) from mem_univ _)
    (show 0 ≤ (1/2 : ℝ) by norm_num) (show 0 ≤ (1/2 : ℝ) by norm_num) (by norm_num)
  norm_num [utility, smul_eq_mul] at hm
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem zero_curvature_not_strictConcave :
    ¬ StrictConcaveOn ℝ (Ioi 0) (utility 0) := by
  intro h
  have hm := h.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (3 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ≠ 3 by norm_num)
    (show 0 < (1/2 : ℝ) by norm_num) (show 0 < (1/2 : ℝ) by norm_num) (by norm_num)
  norm_num [utility, smul_eq_mul] at hm

end ObjectiveControls

#print axioms ObjectiveControls.risky_CRRA_two_household_equilibrium
#print axioms ObjectiveControls.sample_no_nonzero_certain_receipt
#print axioms ObjectiveControls.clipped_log_not_concave
#print axioms ObjectiveControls.zero_curvature_not_strictConcave
