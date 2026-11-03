import CRRAScalar
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! One fresh productive issue. No initial ownership, borrowing or alignment of
independent future income with productive receipts. Curvatures are positive,
without an upper bound; state payoffs and effective weights may be zero. -/
noncomputable section
open scoped BigOperators
open Set Function

namespace PrimaryCRRA

structure Household (S : Type*) where
  cash : ℝ
  gamma : ℝ
  income : S → ℝ
  eta : S → ℝ
  weight : S → ℝ
  output : S → ℝ
  cash_pos : 0 < cash
  gamma_pos : 0 < gamma
  income_pos : ∀ s, 0 < income s
  eta_pos : ∀ s, 0 < eta s
  weight_nonneg : ∀ s, 0 ≤ weight s
  output_nonneg : ∀ s, 0 ≤ output s

variable {S : Type*}

def current (H : Household S) (q a : ℝ) : ℝ := H.cash-q*a
def future (H : Household S) (s : S) (a : ℝ) : ℝ := H.income s+a*H.output s
def Feasible (H : Household S) (q a : ℝ) : Prop := 0 ≤ a ∧ 0 < current H q a

theorem future_pos (H : Household S) {a : ℝ} (ha : 0 ≤ a) (s : S) :
    0 < future H s a := by
  exact add_pos_of_pos_of_nonneg (H.income_pos s) (mul_nonneg ha (H.output_nonneg s))

theorem scalar_tangent_strict {g x z : ℝ} (hg : 0 < g) (hx : 0 < x)
    (hz : 0 < z) (hne : x ≠ z) :
    OwnershipCRRA.utility g x-OwnershipCRRA.utility g z < (x-z)*z^(-g) := by
  have hc := OwnershipCRRA.utility_strictConcaveOn hg
  rcases lt_or_gt_of_ne hne with h | h
  · have hs := hc.lt_slope_of_hasDerivAt hx hz h (OwnershipCRRA.utility_hasDerivAt hz)
    simp only [slope_def_field] at hs
    have hh := (lt_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · have hs := hc.slope_lt_of_hasDerivAt hz hx h (OwnershipCRRA.utility_hasDerivAt hz)
    simp only [slope_def_field] at hs
    have hh := (div_lt_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

theorem scalar_tangent {g x z : ℝ} (hg : 0 < g) (hx : 0 < x) (hz : 0 < z) :
    OwnershipCRRA.utility g x-OwnershipCRRA.utility g z ≤ (x-z)*z^(-g) := by
  by_cases h : x = z
  · simp [h]
  · exact (scalar_tangent_strict hg hx hz h).le

variable [Fintype S]

def marginal (H : Household S) (a : ℝ) : ℝ :=
  ∑ s, H.weight s*H.output s*(future H s a)^(-H.eta s)
def score (H : Household S) (q a : ℝ) : ℝ :=
  marginal H a-q*(current H q a)^(-H.gamma)
def value (H : Household S) (q a : ℝ) : ℝ :=
  OwnershipCRRA.utility H.gamma (current H q a)+
    ∑ s, H.weight s*OwnershipCRRA.utility (H.eta s) (future H s a)
def KKT (H : Household S) (q a : ℝ) : Prop :=
  Feasible H q a ∧ score H q a ≤ 0 ∧ a*score H q a = 0

theorem marginal_nonnegative (H : Household S) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ marginal H a := by
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg (mul_nonneg (H.weight_nonneg s) (H.output_nonneg s))
    (Real.rpow_pos_of_pos (future_pos H ha s) _).le

theorem marginal_antitone (H : Household S) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    marginal H b ≤ marginal H a := by
  apply Finset.sum_le_sum
  intro s _
  have hfuture : future H s a ≤ future H s b := by
    unfold future
    nlinarith [H.output_nonneg s]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (future_pos H ha s) hfuture (by linarith [H.eta_pos s]))
    (mul_nonneg (H.weight_nonneg s) (H.output_nonneg s))

theorem score_strictAnti (H : Household S) {q a b : ℝ} (hq : 0 < q)
    (ha : Feasible H q a) (hb : Feasible H q b) (hab : a < b) :
    score H q b < score H q a := by
  have hc : current H q b < current H q a := by unfold current; nlinarith
  have hm := Real.rpow_lt_rpow_of_neg hb.2 hc (neg_neg_of_pos H.gamma_pos)
  have hp := mul_lt_mul_of_pos_left hm hq
  have hf := marginal_antitone H ha.1 hab.le
  unfold score
  linarith

omit [Fintype S] in
theorem lower_price_feasible (H : Household S) {p q a : ℝ}
    (hpq : p ≤ q) (ha : Feasible H q a) : Feasible H p a := by
  refine ⟨ha.1,?_⟩
  have hc := ha.2
  unfold current at hc ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) ha.1]

theorem score_price_strictAnti (H : Household S) {p q a : ℝ}
    (hp : 0 < p) (hpq : p < q) (ha : Feasible H q a) :
    score H q a < score H p a := by
  have hc := lower_price_feasible H hpq.le ha
  have hcons : current H q a ≤ current H p a := by
    unfold current
    nlinarith [ha.1]
  have hm := Real.rpow_le_rpow_of_nonpos ha.2 hcons
    (show -H.gamma ≤ 0 by linarith [H.gamma_pos])
  have hpos := Real.rpow_pos_of_pos ha.2 (-H.gamma)
  have hcost : p*(current H p a)^(-H.gamma) < q*(current H q a)^(-H.gamma) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hm hp.le)
      (mul_lt_mul_of_pos_right hpq hpos)
  unfold score
  linarith

theorem future_gain_bound (H : Household S) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ s, H.weight s*(OwnershipCRRA.utility (H.eta s) (future H s b)-
      OwnershipCRRA.utility (H.eta s) (future H s a))) ≤ (b-a)*marginal H a := by
  calc
    _ ≤ ∑ s, H.weight s*((future H s b-future H s a)*(future H s a)^(-H.eta s)) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (scalar_tangent (H.eta_pos s) (future_pos H hb s) (future_pos H ha s))
        (H.weight_nonneg s)
    _ = _ := by
      unfold marginal
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      unfold future
      ring

theorem value_difference (H : Household S) (q a b : ℝ) :
    value H q b-value H q a =
      (OwnershipCRRA.utility H.gamma (current H q b)-OwnershipCRRA.utility H.gamma (current H q a))+
      ∑ s, H.weight s*(OwnershipCRRA.utility (H.eta s) (future H s b)-
        OwnershipCRRA.utility (H.eta s) (future H s a)) := by
  unfold value
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

theorem gain_bound (H : Household S) {q a b : ℝ}
    (ha : Feasible H q a) (hb : Feasible H q b) :
    value H q b-value H q a ≤ (b-a)*score H q a := by
  rw [value_difference]
  have hc := scalar_tangent H.gamma_pos hb.2 ha.2
  have hf := future_gain_bound H ha.1 hb.1
  calc
    _ ≤ (current H q b-current H q a)*(current H q a)^(-H.gamma)+(b-a)*marginal H a :=
      add_le_add hc hf
    _ = _ := by unfold score current; ring

theorem gain_strict (H : Household S) {q a b : ℝ} (hq : 0 < q)
    (ha : Feasible H q a) (hb : Feasible H q b) (hne : b ≠ a) :
    value H q b-value H q a < (b-a)*score H q a := by
  have hn : current H q b ≠ current H q a := by
    intro he
    apply hne
    unfold current at he
    nlinarith
  rw [value_difference]
  have hc := scalar_tangent_strict H.gamma_pos hb.2 ha.2 hn
  have hf := future_gain_bound H ha.1 hb.1
  calc
    _ < (current H q b-current H q a)*(current H q a)^(-H.gamma)+(b-a)*marginal H a :=
      add_lt_add_of_lt_of_le hc hf
    _ = _ := by unfold score current; ring

theorem kkt_globally_optimal (H : Household S) {q a b : ℝ}
    (ha : KKT H q a) (hb : Feasible H q b) : value H q b ≤ value H q a := by
  have h := gain_bound H ha.1 hb
  have hn := mul_nonpos_of_nonneg_of_nonpos hb.1 ha.2.1
  nlinarith [ha.2.2]

theorem kkt_unique_optimum (H : Household S) {q a b : ℝ} (hq : 0 < q)
    (ha : KKT H q a) (hb : Feasible H q b) (hne : b ≠ a) :
    value H q b < value H q a := by
  have h := gain_strict H hq ha.1 hb hne
  have hn := mul_nonpos_of_nonneg_of_nonpos hb.1 ha.2.1
  nlinarith [ha.2.2]

end PrimaryCRRA

#print axioms PrimaryCRRA.future_pos
#print axioms PrimaryCRRA.scalar_tangent_strict
#print axioms PrimaryCRRA.scalar_tangent
#print axioms PrimaryCRRA.marginal_nonnegative
#print axioms PrimaryCRRA.marginal_antitone
#print axioms PrimaryCRRA.score_strictAnti
#print axioms PrimaryCRRA.lower_price_feasible
#print axioms PrimaryCRRA.score_price_strictAnti
#print axioms PrimaryCRRA.future_gain_bound
#print axioms PrimaryCRRA.value_difference
#print axioms PrimaryCRRA.gain_bound
#print axioms PrimaryCRRA.gain_strict
#print axioms PrimaryCRRA.kkt_globally_optimal
#print axioms PrimaryCRRA.kkt_unique_optimum
