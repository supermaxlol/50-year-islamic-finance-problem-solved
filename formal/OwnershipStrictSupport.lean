import OwnershipKKTSufficiency

/-!
Strict supporting-price inequalities on the actual uncapped ownership domain.
Unlike market-price uniqueness, this is a household-level consequence of
positive CRRA curvature and injective physical payoff maps.
-/

noncomputable section
open scoped BigOperators
open Set OwnershipCRRA OwnershipMarginal OwnershipUnfloored OwnershipSufficiency

namespace OwnershipStrictSupport

theorem utility_tangent_lt {g x y : ℝ} (hg : 0 < g) (hx : 0 < x) (hy : 0 < y)
    (hne : x ≠ y) : utility g y < utility g x + x^(-g)*(y-x) := by
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have h := (utility_strictConcaveOn hg).slope_lt_of_hasDerivAt
      hx hy hxy (utility_hasDerivAt hx)
    rw [slope_def_field] at h
    have hh := (div_lt_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · have h := (utility_strictConcaveOn hg).lt_slope_of_hasDerivAt
      hy hx hyx (utility_hasDerivAt hx)
    rw [slope_def_field] at h
    have hh := (lt_div_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

variable {J S : Type*} [Fintype J] [Fintype S]

theorem future_tangent_decomposition (D : Data J S) (a b : J → ℝ) :
    (∑ s, D.weight s * (utility (D.eta s) (consumption D a s) +
      (consumption D a s)^(-D.eta s)*(consumption D b s-consumption D a s))) =
    (∑ s, D.weight s * utility (D.eta s) (consumption D a s)) +
      ∑ j, marginal D a j*(b j-a j) := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← future_tangent_pairing D a b]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem economic_tangent_lt (D : Data J S) (c d : ℝ) (a b : J → ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hne : c ≠ d ∨ a ≠ b) :
    economicValue D d b < economicValue D c a + c^(-D.gamma)*(d-c) +
      ∑ j, marginal D a j*(b j-a j) := by
  have hweak : ∀ s,
      D.weight s*utility (D.eta s) (consumption D b s) ≤
      D.weight s*(utility (D.eta s) (consumption D a s) +
        (consumption D a s)^(-D.eta s)*(consumption D b s-consumption D a s)) := by
    intro s
    exact mul_le_mul_of_nonneg_left
      (utility_tangent_le (D.eta_pos s) (consumption_positive D ha s)
        (consumption_positive D hb s)) (D.weight_pos s).le
  rcases hne with hcd | hab
  · have hfuture := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hweak s)
    rw [future_tangent_decomposition D a b] at hfuture
    have hcurrent := utility_tangent_lt D.gamma_pos hc hd hcd
    change utility D.gamma d +
        (∑ s, D.weight s*utility (D.eta s) (consumption D b s)) <
      utility D.gamma c +
        (∑ s, D.weight s*utility (D.eta s) (consumption D a s)) +
          c^(-D.gamma)*(d-c) + ∑ j, marginal D a j*(b j-a j)
    linarith
  · have hex : ∃ s, consumption D a s ≠ consumption D b s := by
      by_contra hn
      apply hab
      apply D.payoff_injective
      funext s
      have hh := not_not.mp (not_exists.mp hn s)
      dsimp [consumption] at hh
      linarith
    obtain ⟨s, hs⟩ := hex
    have hstrict := mul_lt_mul_of_pos_left
      (utility_tangent_lt (D.eta_pos s) (consumption_positive D ha s)
        (consumption_positive D hb s) hs) (D.weight_pos s)
    have hfuture := Finset.sum_lt_sum
      (fun s (_ : s ∈ (Finset.univ : Finset S)) => hweak s)
      ⟨s, Finset.mem_univ s, hstrict⟩
    rw [future_tangent_decomposition D a b] at hfuture
    have hcurrent := utility_tangent_le D.gamma_pos hc hd
    change utility D.gamma d +
        (∑ s, D.weight s*utility (D.eta s) (consumption D b s)) <
      utility D.gamma c +
        (∑ s, D.weight s*utility (D.eta s) (consumption D a s)) +
          c^(-D.gamma)*(d-c) + ∑ j, marginal D a j*(b j-a j)
    linarith

theorem corner_pairing_le (D : Data J S) (q a b : J → ℝ) (c : ℝ)
    (hb : ∀ j, 0 ≤ b j)
    (hkkt : ∀ j, marginal D a j ≤ q j*c^(-D.gamma) ∧
      a j*(q j*c^(-D.gamma)-marginal D a j)=0) :
    (∑ j, marginal D a j*(b j-a j)) ≤
      c^(-D.gamma)*((∑ j, q j*b j)-(∑ j, q j*a j)) := by
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
      marginal D a j*(b j-a j) ≤ (q j*c^(-D.gamma))*(b j-a j) from by
        have hj := hkkt j
        have hn := mul_nonneg (sub_nonneg.mpr hj.1) (hb j)
        nlinarith [hj.2])
  have he : (∑ j, (q j*c^(-D.gamma))*(b j-a j)) =
      c^(-D.gamma)*((∑ j, q j*b j)-(∑ j, q j*a j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [he] at hp

theorem economic_support_le (D : Data J S) (q a b : J → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hkkt : ∀ j, marginal D a j ≤ q j*c^(-D.gamma) ∧
      a j*(q j*c^(-D.gamma)-marginal D a j)=0) :
    economicValue D d b ≤ economicValue D c a +
      c^(-D.gamma)*((d+∑ j, q j*b j)-(c+∑ j, q j*a j)) := by
  have ht := economic_tangent_le D c d a b hc hd ha hb
  have hp := corner_pairing_le D q a b c hb hkkt
  nlinarith

theorem economic_support_lt (D : Data J S) (q a b : J → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hkkt : ∀ j, marginal D a j ≤ q j*c^(-D.gamma) ∧
      a j*(q j*c^(-D.gamma)-marginal D a j)=0)
    (hne : c ≠ d ∨ a ≠ b) :
    economicValue D d b < economicValue D c a +
      c^(-D.gamma)*((d+∑ j, q j*b j)-(c+∑ j, q j*a j)) := by
  have ht := economic_tangent_lt D c d a b hc hd ha hb hne
  have hp := corner_pairing_le D q a b c hb hkkt
  nlinarith

theorem bundle_equal_of_not_worse_and_cost_le (D : Data J S)
    (q a b : J → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hkkt : ∀ j, marginal D a j ≤ q j*c^(-D.gamma) ∧
      a j*(q j*c^(-D.gamma)-marginal D a j)=0)
    (hbetter : economicValue D c a ≤ economicValue D d b)
    (hcost : d+∑ j, q j*b j ≤ c+∑ j, q j*a j) : d=c ∧ b=a := by
  by_contra hn
  have hdiff : c ≠ d ∨ a ≠ b := by
    by_cases hcd : c=d
    · right
      intro hab
      exact hn ⟨hcd.symm, hab.symm⟩
    · exact Or.inl hcd
  have hs := economic_support_lt D q a b c d hc hd ha hb hkkt hdiff
  have hnpos := mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_pos_of_pos hc (-D.gamma)).le (sub_nonpos.mpr hcost)
  linarith

end OwnershipStrictSupport

#print axioms OwnershipStrictSupport.utility_tangent_lt
#print axioms OwnershipStrictSupport.future_tangent_decomposition
#print axioms OwnershipStrictSupport.economic_tangent_lt
#print axioms OwnershipStrictSupport.corner_pairing_le
#print axioms OwnershipStrictSupport.economic_support_le
#print axioms OwnershipStrictSupport.economic_support_lt
#print axioms OwnershipStrictSupport.bundle_equal_of_not_worse_and_cost_le
