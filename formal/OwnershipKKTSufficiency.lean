import CRRAPositiveOwnershipExistence

/-!
The converse direction needed to certify a candidate market as an actual
equilibrium: CRRA concavity and the corner inequalities imply global household
optimality on the original uncapped positive-consumption budget set.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored

namespace OwnershipSufficiency

theorem utility_tangent_le {g x y : ℝ} (hg : 0 < g) (hx : 0 < x) (hy : 0 < y) :
    utility g y ≤ utility g x + x ^ (-g) * (y - x) := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have h := (utility_strictConcaveOn hg).concaveOn.slope_le_of_hasDerivAt
      hx hy hxy (utility_hasDerivAt hx)
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · subst y
    simp
  · have h := (utility_strictConcaveOn hg).concaveOn.le_slope_of_hasDerivAt
      hy hx hyx (utility_hasDerivAt hx)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

variable {J S : Type*} [Fintype J] [Fintype S]

theorem future_tangent_pairing (D : Data J S) (a b : J → ℝ) :
    (∑ s, D.weight s * (consumption D a s) ^ (-D.eta s) *
      (consumption D b s - consumption D a s)) =
    ∑ j, marginal D a j * (b j - a j) := by
  have hd : ∀ s, consumption D b s - consumption D a s =
      ∑ j, D.payoff s j * (b j - a j) := by
    intro s
    simp only [consumption, mul_sub, Finset.sum_sub_distrib]
    ring
  simp_rw [hd, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [marginal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem economic_tangent_le (D : Data J S) (c d : ℝ) (a b : J → ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    economicValue D d b ≤ economicValue D c a + c ^ (-D.gamma) * (d-c) +
      ∑ j, marginal D a j * (b j-a j) := by
  have hfuture := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    mul_le_mul_of_nonneg_left
      (utility_tangent_le (D.eta_pos s) (consumption_positive D ha s)
        (consumption_positive D hb s)) (D.weight_pos s).le)
  have hs : (∑ s, D.weight s *
      (utility (D.eta s) (consumption D a s) +
        (consumption D a s)^(-D.eta s) *
          (consumption D b s-consumption D a s))) =
      (∑ s, D.weight s * utility (D.eta s) (consumption D a s)) +
        ∑ j, marginal D a j*(b j-a j) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← future_tangent_pairing D a b]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hs] at hfuture
  have hcurrent := utility_tangent_le D.gamma_pos hc hd
  change utility D.gamma d +
      (∑ s, D.weight s * utility (D.eta s) (consumption D b s)) ≤
    utility D.gamma c +
      (∑ s, D.weight s * utility (D.eta s) (consumption D a s)) +
        c^(-D.gamma)*(d-c) + ∑ j, marginal D a j*(b j-a j)
  linarith

theorem global_optimality_of_corner_conditions (D : Data J S)
    (q a : J → ℝ) (c wealth : ℝ)
    (hc : 0 < c) (ha : ∀ j, 0 ≤ a j)
    (hbudget : c + ∑ j, q j*a j = wealth)
    (hkkt : ∀ j, marginal D a j ≤ q j*c^(-D.gamma) ∧
      a j*(q j*c^(-D.gamma)-marginal D a j)=0) :
    ∀ d : ℝ, 0 < d → ∀ b : J → ℝ, (∀ j, 0 ≤ b j) →
      d + ∑ j, q j*b j ≤ wealth → economicValue D d b ≤ economicValue D c a := by
  intro d hd b hb hbud
  have ht := economic_tangent_le D c d a b hc hd ha hb
  have hpair := Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
      marginal D a j*(b j-a j) ≤ (q j*c^(-D.gamma))*(b j-a j) from by
        have hj := hkkt j
        have hn := mul_nonneg (sub_nonneg.mpr hj.1) (hb j)
        nlinarith [hj.2])
  have halgebra : (∑ j, (q j*c^(-D.gamma))*(b j-a j)) =
      c^(-D.gamma)*((∑ j, q j*b j)-(∑ j, q j*a j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [halgebra] at hpair
  have hsum : (d-c)+((∑ j, q j*b j)-(∑ j, q j*a j)) ≤ 0 := by
    linarith
  have hsign := mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_pos_of_pos hc (-D.gamma)).le hsum
  nlinarith

end OwnershipSufficiency

#print axioms OwnershipSufficiency.utility_tangent_le
#print axioms OwnershipSufficiency.future_tangent_pairing
#print axioms OwnershipSufficiency.economic_tangent_le
#print axioms OwnershipSufficiency.global_optimality_of_corner_conditions
