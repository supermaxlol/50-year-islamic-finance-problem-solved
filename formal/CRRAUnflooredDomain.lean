import CRRAOwnershipObjective
import SlackBoundTransfer

/-!
The actual positive-consumption ownership domain, not the old temporary box.
Current consumption may lie strictly below the temporary floor. Concavity is
derived on this whole domain and the accepted optimizer-lifting theorem is
connected to the household's actual consumption/portfolio budget. Slackness of
the old floor remains an explicit condition; it is not asserted proved here.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipBridge OwnershipBounds OwnershipCRRA

namespace OwnershipUnfloored

variable {J S : Type*} [Fintype J] [Fintype S]

def economicDomain (D : Data J S) : Set (Option J → ℝ) :=
  {x | 0 < x none + D.delta ∧ ∀ j, 0 ≤ x (some j)}

omit [Fintype S] in
theorem box_subset_economicDomain (D : Data J S) (M : ℝ) :
    (box M : Set (Option J → ℝ)) ⊆ economicDomain D := by
  intro x hx
  exact ⟨by have hp := D.delta_pos; have hn := (hx none).1; linarith,
    fun j => (hx (some j)).1⟩

omit [Fintype S] in
theorem economicDomain_convex (D : Data J S) : Convex ℝ (economicDomain D) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun j => ?_⟩
  · change 0 < receipts D (a • x + b • y) none
    rw [receipts_combo D x y a b hab none]
    exact (convex_Ioi (0 : ℝ)) hx.1 hy.1 ha hb hab
  · change 0 ≤ a * x (some j) + b * y (some j)
    exact add_nonneg (mul_nonneg ha (hx.2 j)) (mul_nonneg hb (hy.2 j))

omit [Fintype S] in
theorem domain_receipts_positive (D : Data J S) {x : Option J → ℝ}
    (hx : x ∈ economicDomain D) (r : Option S) : 0 < receipts D x r := by
  cases r with
  | none => exact hx.1
  | some s =>
    have hs : 0 ≤ ∑ j, D.payoff s j * x (some j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (D.payoff_nonneg s j) (hx.2 j)
    change 0 < D.income s + ∑ j, D.payoff s j * x (some j)
    linarith [D.income_pos s]

theorem objective_concaveOn_economicDomain (D : Data J S) :
    ConcaveOn ℝ (economicDomain D) (objective D) := by
  refine ⟨economicDomain_convex D, ?_⟩
  intro x hx y hy a b ha hb hab
  have hweak : ∀ r,
      mass D r * (a * utility (curvature D r) (receipts D x r) +
        b * utility (curvature D r) (receipts D y r)) ≤
      mass D r * utility (curvature D r) (receipts D (a • x + b • y) r) := by
    intro r
    rw [receipts_combo D x y a b hab r]
    exact mul_le_mul_of_nonneg_left
      ((utility_strictConcaveOn (curvature_pos D r)).concaveOn.2
        (domain_receipts_positive D hx r) (domain_receipts_positive D hy r) ha hb hab)
      (mass_pos D r).le
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hweak r)
  have hsplit : (∑ r, mass D r * (a * utility (curvature D r) (receipts D x r) +
        b * utility (curvature D r) (receipts D y r))) =
      a * objective D x + b * objective D y := by
    dsimp [objective]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hsplit] at hs
  exact hs

/-- Utility in physical current consumption and productive holdings. -/
def economicValue (D : Data J S) (c : ℝ) (a : J → ℝ) : ℝ :=
  utility D.gamma c + ∑ s, D.weight s * utility (D.eta s)
    (D.income s + ∑ j, D.payoff s j * a j)

omit [Fintype J] [Fintype S] in
def shiftedChoice (delta c : ℝ) (a : J → ℝ) : Option J → ℝ
  | none => c - delta
  | some j => a j

omit [Fintype S] in
theorem shiftedChoice_mem_domain (D : Data J S) (c : ℝ) (a : J → ℝ)
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) :
    shiftedChoice D.delta c a ∈ economicDomain D := by
  exact ⟨by simpa [shiftedChoice] using hc, ha⟩

theorem objective_eq_economicValue (D : Data J S) (x : Option J → ℝ) :
    objective D x = economicValue D (x none + D.delta) (fun j => x (some j)) := by
  simp [objective, economicValue, Fintype.sum_option, mass, curvature, receipts]

theorem shiftedChoice_objective (D : Data J S) (c : ℝ) (a : J → ℝ) :
    objective D (shiftedChoice D.delta c a) = economicValue D c a := by
  rw [objective_eq_economicValue]
  simp [shiftedChoice]

omit [Fintype S] in
theorem shiftedChoice_cost (D : Data J S) (q a : J → ℝ) (c : ℝ) :
    cost q (shiftedChoice D.delta c a) = c - D.delta + ∑ j, q j * a j := rfl

/-- No cap on competitors and no inherited consumption floor. The old optimum
must itself have strictly slack artificial bounds. No demand or Euler system
is substituted for the actual household optimization certificate. -/
theorem actual_budget_optimality_from_slack (D : Data J S) (M : ℝ)
    (ω x : Option J → ℝ) (q : J → ℝ)
    (hopt : IsNumeraireOptimal M ω (objective D) q x)
    (hfloor : 0 < x none) (hcap : ∀ g, x g < M) :
    ∀ c : ℝ, 0 < c → ∀ a : J → ℝ, (∀ j, 0 ≤ a j) →
      c + ∑ j, q j * a j ≤ (ω none + D.delta) + ∑ j, q j * ω (some j) →
      economicValue D c a ≤ economicValue D (x none + D.delta)
        (fun j => x (some j)) := by
  intro c hc a ha hbudget
  have hm := slack_optimum_transfers M ω (objective D) q x (economicDomain D)
    hopt hfloor hcap (objective_concaveOn_economicDomain D)
    (box_subset_economicDomain D M hopt.1) (fun _ hz j => hz.2 j)
    (shiftedChoice D.delta c a) (shiftedChoice_mem_domain D c a hc ha)
  have hcost : cost q (shiftedChoice D.delta c a) ≤ cost q ω := by
    rw [shiftedChoice_cost]
    dsimp [cost]
    linarith
  have h := hm hcost
  rwa [shiftedChoice_objective, objective_eq_economicValue] at h

end OwnershipUnfloored

#print axioms OwnershipUnfloored.box_subset_economicDomain
#print axioms OwnershipUnfloored.economicDomain_convex
#print axioms OwnershipUnfloored.domain_receipts_positive
#print axioms OwnershipUnfloored.objective_concaveOn_economicDomain
#print axioms OwnershipUnfloored.shiftedChoice_mem_domain
#print axioms OwnershipUnfloored.objective_eq_economicValue
#print axioms OwnershipUnfloored.shiftedChoice_objective
#print axioms OwnershipUnfloored.shiftedChoice_cost
#print axioms OwnershipUnfloored.actual_budget_optimality_from_slack
