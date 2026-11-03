import CRRAUniformEquilibriumBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Continuity and actual-optimizer limit tools. Competitors are scaled to become
strictly affordable; no assumed Euler system replaces household optimization.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored

namespace OwnershipLimit

def epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by
  unfold epsilon
  positivity

theorem epsilon_lt_one (n : ℕ) : epsilon n < 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  unfold epsilon
  rw [div_lt_one (by positivity : 0 < (n : ℝ) + 2)]
  linarith

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have he : (fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)+1)) = epsilon := by
    funext n
    simp only [epsilon, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  change Tendsto (fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)+1)) atTop (𝓝 0) at h
  rw [he] at h
  exact h

section Spending
variable {J : Type*} [Fintype J]

def spending (q : J → ℝ) (c : ℝ) (a : J → ℝ) : ℝ := c + ∑ j, q j * a j

theorem spending_scale (q : J → ℝ) (c : ℝ) (a : J → ℝ) (t : ℝ) :
    spending q (t*c) (fun j => t*a j) = t * spending q c a := by
  unfold spending
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spending_tendsto {X : Type*} {l : Filter X}
    {qn an : X → J → ℝ} {cn : X → ℝ} {q a : J → ℝ} {c : ℝ}
    (hq : ∀ j, Tendsto (fun n => qn n j) l (𝓝 (q j)))
    (hc : Tendsto cn l (𝓝 c))
    (ha : ∀ j, Tendsto (fun n => an n j) l (𝓝 (a j))) :
    Tendsto (fun n => spending (qn n) (cn n) (an n)) l (𝓝 (spending q c a)) := by
  exact hc.add (tendsto_finsetSum _ (fun j _ => (hq j).mul (ha j)))

end Spending

section Utility
variable {J S : Type*} [Fintype J] [Fintype S]

omit [Fintype S] in
theorem future_consumption_tendsto (D : Data J S)
    {X : Type*} {l : Filter X} {an : X → J → ℝ} {a : J → ℝ}
    (ha : ∀ j, Tendsto (fun n => an n j) l (𝓝 (a j))) (s : S) :
    Tendsto (fun n => consumption D (an n) s) l (𝓝 (consumption D a s)) := by
  exact tendsto_const_nhds.add (tendsto_finsetSum _
    (fun j _ => tendsto_const_nhds.mul (ha j)))

theorem economicValue_tendsto (D : Data J S)
    {X : Type*} {l : Filter X} {cn : X → ℝ} {an : X → J → ℝ}
    {c : ℝ} {a : J → ℝ} (hc : 0 < c) (ha : ∀ j, 0 ≤ a j)
    (hcn : Tendsto cn l (𝓝 c))
    (han : ∀ j, Tendsto (fun n => an n j) l (𝓝 (a j))) :
    Tendsto (fun n => economicValue D (cn n) (an n)) l
      (𝓝 (economicValue D c a)) := by
  apply Tendsto.add
  · exact (utility_hasDerivAt (g := D.gamma) hc).continuousAt.tendsto.comp hcn
  · apply tendsto_finsetSum
    intro s _
    apply tendsto_const_nhds.mul
    exact (utility_hasDerivAt (g := D.eta s) (consumption_positive D ha s)).continuousAt.tendsto.comp
      (future_consumption_tendsto D han s)

theorem marginal_tendsto (D : Data J S)
    {X : Type*} {l : Filter X} {an : X → J → ℝ} {a : J → ℝ}
    (ha : ∀ j, 0 ≤ a j)
    (han : ∀ j, Tendsto (fun n => an n j) l (𝓝 (a j))) (j : J) :
    Tendsto (fun n => marginal D (an n) j) l (𝓝 (marginal D a j)) := by
  apply tendsto_finsetSum
  intro s _
  exact tendsto_const_nhds.mul ((future_consumption_tendsto D han s).rpow_const
    (Or.inl (ne_of_gt (consumption_positive D ha s))))

/-- Actual optimality is closed under converging prices, positive limiting
wealth and choices in the positive-current/nonnegative-ownership domain. -/
theorem actual_optimality_limit (D : Data J S)
    {qn an : ℕ → J → ℝ} {wn cn : ℕ → ℝ} {q a : J → ℝ} {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (ha : ∀ j, 0 ≤ a j)
    (hq : ∀ j, Tendsto (fun n => qn n j) atTop (𝓝 (q j)))
    (hwn : Tendsto wn atTop (𝓝 w)) (hcn : Tendsto cn atTop (𝓝 c))
    (han : ∀ j, Tendsto (fun n => an n j) atTop (𝓝 (a j)))
    (hopt : ∀ n c', 0 < c' → ∀ a' : J → ℝ, (∀ j, 0 ≤ a' j) →
      spending (qn n) c' a' ≤ wn n →
      economicValue D c' a' ≤ economicValue D (cn n) (an n)) :
    ∀ c', 0 < c' → ∀ a' : J → ℝ, (∀ j, 0 ≤ a' j) →
      spending q c' a' ≤ w → economicValue D c' a' ≤ economicValue D c a := by
  intro c' hc' a' ha' hb
  have hv := economicValue_tendsto D hc ha hcn han
  have hscaled : ∀ t : ℝ, 0 < t → t < 1 →
      economicValue D (t*c') (fun j => t*a' j) ≤ economicValue D c a := by
    intro t ht ht1
    have hcb : spending q (t*c') (fun j => t*a' j) < w := by
      rw [spending_scale]
      have hle := mul_le_mul_of_nonneg_left hb ht.le
      have hlt : t*w < w := by nlinarith
      exact hle.trans_lt hlt
    have hcost := spending_tendsto hq
      (tendsto_const_nhds (x := t*c'))
      (fun j => tendsto_const_nhds (x := t*a' j))
    have hev := hcost.eventually_lt hwn hcb
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hv
    filter_upwards [hev] with n hn
    exact hopt n (t*c') (mul_pos ht hc') (fun j => t*a' j)
      (fun j => mul_nonneg ht.le (ha' j)) hn.le
  have ht : Tendsto (fun n => 1 - epsilon n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub epsilon_tendsto
  have hleft : Tendsto (fun n => economicValue D ((1-epsilon n)*c')
      (fun j => (1-epsilon n)*a' j)) atTop (𝓝 (economicValue D c' a')) := by
    have hcc : Tendsto (fun n => (1-epsilon n)*c') atTop (𝓝 c') := by
      simpa using ht.mul (tendsto_const_nhds (x := c'))
    have haa : ∀ j, Tendsto (fun n => (1-epsilon n)*a' j) atTop (𝓝 (a' j)) := by
      intro j
      simpa using ht.mul (tendsto_const_nhds (x := a' j))
    exact economicValue_tendsto D hc' ha' hcc haa
  apply le_of_tendsto' hleft
  intro n
  exact hscaled (1-epsilon n) (sub_pos.mpr (epsilon_lt_one n))
    (by linarith [epsilon_pos n])

end Utility
end OwnershipLimit

#print axioms OwnershipLimit.epsilon_pos
#print axioms OwnershipLimit.epsilon_lt_one
#print axioms OwnershipLimit.epsilon_tendsto
#print axioms OwnershipLimit.spending_scale
#print axioms OwnershipLimit.spending_tendsto
#print axioms OwnershipLimit.future_consumption_tendsto
#print axioms OwnershipLimit.economicValue_tendsto
#print axioms OwnershipLimit.marginal_tendsto
#print axioms OwnershipLimit.actual_optimality_limit
