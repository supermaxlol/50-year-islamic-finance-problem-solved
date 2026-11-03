import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual new-issue buyers, with the zero-subscription outside option.
Future background resources are aligned with a strictly positive project payoff.
This is a separate bounded formation class, not a replacement of the broad CRRA market. -/
noncomputable section
open scoped BigOperators
open Set

namespace PrimaryLogDemand

structure Household where
  cash : ℝ
  background : ℝ
  weight : ℝ
  cash_pos : 0 < cash
  background_pos : 0 < background
  weight_pos : 0 < weight

def alpha (H : Household) : ℝ := H.weight * H.cash / (1 + H.weight)
def eta (H : Household) : ℝ := H.background / (1 + H.weight)
def raw (H : Household) (q : ℝ) : ℝ := alpha H / q - eta H
def demand (H : Household) (q : ℝ) : ℝ := max 0 (raw H q)
def current (H : Household) (q a : ℝ) : ℝ := H.cash - q*a
def feasible (H : Household) (q a : ℝ) : Prop := 0 ≤ a ∧ 0 < current H q a
def utility (H : Household) (q a : ℝ) : ℝ :=
  Real.log (current H q a) + H.weight * Real.log (H.background+a)
def score (H : Household) (q a : ℝ) : ℝ :=
  H.weight / (H.background+a) - q / current H q a

theorem alpha_pos (H : Household) : 0 < alpha H := by
  exact div_pos (mul_pos H.weight_pos H.cash_pos) (by linarith [H.weight_pos])

theorem eta_pos (H : Household) : 0 < eta H := by
  exact div_pos H.background_pos (by linarith [H.weight_pos])

theorem raw_identity (H : Household) (q : ℝ) (hq : 0 < q) :
    q*(1+H.weight)*raw H q = H.weight*H.cash-q*H.background := by
  have hb : 1+H.weight ≠ 0 := ne_of_gt (by linarith [H.weight_pos])
  unfold raw alpha eta
  field_simp [hq.ne', hb]

theorem demand_nonnegative (H : Household) (q : ℝ) : 0 ≤ demand H q := le_max_left _ _

theorem demand_feasible (H : Household) (q : ℝ) (hq : 0 < q) :
    feasible H q (demand H q) := by
  refine ⟨demand_nonnegative H q, ?_⟩
  by_cases hr : raw H q ≤ 0
  · simpa [current, demand, max_eq_left hr] using H.cash_pos
  · have hp : 0 < raw H q := lt_of_not_ge hr
    have hi := raw_identity H q hq
    have hm : 0 < q*(H.background+raw H q) :=
      mul_pos hq (add_pos H.background_pos hp)
    change 0 < H.cash-q*demand H q
    rw [demand, max_eq_right hp.le]
    have hbalance : H.weight*(H.cash-q*raw H q) = q*(H.background+raw H q) := by
      nlinarith [hi]
    have hmul : 0 < H.weight*(H.cash-q*raw H q) := by rw [hbalance]; exact hm
    by_contra hn
    have hnon := mul_nonpos_of_nonneg_of_nonpos H.weight_pos.le (le_of_not_gt hn)
    linarith

theorem demand_budget_strict (H : Household) (q : ℝ) (hq : 0 < q) :
    q*demand H q < H.cash := by
  have h := (demand_feasible H q hq).2
  unfold current at h
  linarith

theorem demand_upper (H : Household) (q : ℝ) (hq : 0 < q) :
    demand H q ≤ H.cash/q := by
  apply (le_div_iff₀ hq).mpr
  nlinarith [demand_budget_strict H q hq]

theorem demand_euler (H : Household) (q : ℝ) (hq : 0 < q) :
    score H q (demand H q) ≤ 0 ∧ demand H q * score H q (demand H q) = 0 := by
  by_cases hr : raw H q ≤ 0
  · have hi := raw_identity H q hq
    have hm : q*(1+H.weight)*raw H q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hq.le (by linarith [H.weight_pos])) hr
    have hb : H.weight/H.background ≤ q/H.cash := by
      apply (div_le_div_iff₀ H.background_pos H.cash_pos).mpr
      linarith
    simpa [score, current, demand, max_eq_left hr, sub_nonpos] using hb
  · have hp : 0 < raw H q := lt_of_not_ge hr
    have hi := raw_identity H q hq
    have hc := (demand_feasible H q hq).2
    have hd : 0 < H.background+demand H q :=
      add_pos_of_pos_of_nonneg H.background_pos (demand_nonnegative H q)
    have he : H.weight * current H q (demand H q) = q*(H.background+demand H q) := by
      unfold current
      rw [demand, max_eq_right hp.le]
      nlinarith
    have hz : score H q (demand H q) = 0 := by
      unfold score
      exact sub_eq_zero.mpr ((div_eq_div_iff hd.ne' hc.ne').mpr he)
    simp [hz]

theorem log_tangent (x z : ℝ) (hx : 0 < x) (hz : 0 < z) :
    Real.log x-Real.log z ≤ (x-z)/z := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hz)
  rw [Real.log_div hx.ne' hz.ne'] at h
  simpa [sub_div, hz.ne'] using h

theorem log_tangent_strict (x z : ℝ) (hx : 0 < x) (hz : 0 < z) (hne : x ≠ z) :
    Real.log x-Real.log z < (x-z)/z := by
  have hratio : x/z ≠ 1 := by
    intro h
    have he := (div_eq_iff hz.ne').mp h
    simp only [one_mul] at he
    exact hne he
  have h := Real.log_lt_sub_one_of_pos (div_pos hx hz) hratio
  rw [Real.log_div hx.ne' hz.ne'] at h
  simpa [sub_div, hz.ne'] using h

theorem gain_bound (H : Household) (q a : ℝ) (hq : 0 < q) (ha : feasible H q a) :
    utility H q a-utility H q (demand H q) ≤
      (a-demand H q)*score H q (demand H q) := by
  have hd := demand_feasible H q hq
  have ha' : 0 < H.background+a := add_pos_of_pos_of_nonneg H.background_pos ha.1
  have hd' : 0 < H.background+demand H q :=
    add_pos_of_pos_of_nonneg H.background_pos hd.1
  have hc := log_tangent _ _ ha.2 hd.2
  have hf := mul_le_mul_of_nonneg_left (log_tangent _ _ ha' hd') H.weight_pos.le
  calc
    utility H q a-utility H q (demand H q) =
        (Real.log (current H q a)-Real.log (current H q (demand H q))) +
        H.weight*(Real.log (H.background+a)-Real.log (H.background+demand H q)) := by
          unfold utility; ring
    _ ≤ (current H q a-current H q (demand H q))/current H q (demand H q) +
        H.weight*((H.background+a)-(H.background+demand H q))/(H.background+demand H q) := by
          simpa [mul_div_assoc] using add_le_add hc hf
    _ = (a-demand H q)*score H q (demand H q) := by unfold score current; ring

theorem gain_strict (H : Household) (q a : ℝ) (hq : 0 < q)
    (ha : feasible H q a) (hne : a ≠ demand H q) :
    utility H q a-utility H q (demand H q) <
      (a-demand H q)*score H q (demand H q) := by
  have hd := demand_feasible H q hq
  have hcur : current H q a ≠ current H q (demand H q) := by
    intro he
    apply hne
    unfold current at he
    nlinarith
  have hc := log_tangent_strict _ _ ha.2 hd.2 hcur
  have hf := mul_le_mul_of_nonneg_left
    (log_tangent (H.background+a) (H.background+demand H q)
      (add_pos_of_pos_of_nonneg H.background_pos ha.1)
      (add_pos_of_pos_of_nonneg H.background_pos hd.1)) H.weight_pos.le
  calc
    utility H q a-utility H q (demand H q) =
        (Real.log (current H q a)-Real.log (current H q (demand H q))) +
        H.weight*(Real.log (H.background+a)-Real.log (H.background+demand H q)) := by
          unfold utility; ring
    _ < (current H q a-current H q (demand H q))/current H q (demand H q) +
        H.weight*((H.background+a)-(H.background+demand H q))/(H.background+demand H q) := by
          simpa [mul_div_assoc] using add_lt_add_of_lt_of_le hc hf
    _ = (a-demand H q)*score H q (demand H q) := by unfold score current; ring

theorem demand_globally_optimal (H : Household) (q a : ℝ) (hq : 0 < q)
    (ha : feasible H q a) : utility H q a ≤ utility H q (demand H q) := by
  have hb := gain_bound H q a hq ha
  have he := demand_euler H q hq
  have hn := mul_nonpos_of_nonneg_of_nonpos ha.1 he.1
  nlinarith

theorem demand_unique_optimum (H : Household) (q a : ℝ) (hq : 0 < q)
    (ha : feasible H q a) (hne : a ≠ demand H q) :
    utility H q a < utility H q (demand H q) := by
  have hb := gain_strict H q a hq ha hne
  have he := demand_euler H q hq
  have hn := mul_nonpos_of_nonneg_of_nonpos ha.1 he.1
  nlinarith

theorem voluntary_participation (H : Household) (q : ℝ) (hq : 0 < q) :
    utility H q 0 ≤ utility H q (demand H q) := by
  apply demand_globally_optimal H q 0 hq
  exact ⟨le_refl 0, by simpa [current] using H.cash_pos⟩

theorem positive_subscription_strictly_preferred (H : Household) (q : ℝ)
    (hq : 0 < q) (hd : 0 < demand H q) :
    utility H q 0 < utility H q (demand H q) := by
  apply demand_unique_optimum H q 0 hq
  · exact ⟨le_refl 0, by simpa [current] using H.cash_pos⟩
  · exact hd.ne

theorem demand_continuousOn (H : Household) : ContinuousOn (demand H) (Ioi 0) := by
  have hh : ContinuousOn (raw H) (Ioi 0) :=
    (continuousOn_const.div continuousOn_id (fun _ hq => hq.ne')).sub continuousOn_const
  intro q hq
  exact Filter.Tendsto.max continuousWithinAt_const (hh q hq)

theorem demand_antitone (H : Household) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) : demand H q ≤ demand H p := by
  have hd : alpha H/q ≤ alpha H/p := by
    apply (div_le_div_iff₀ hq hp).mpr
    exact mul_le_mul_of_nonneg_left hpq (alpha_pos H).le
  exact max_le_max_left 0 (sub_le_sub_right hd _)

theorem demand_strict_on_active (H : Household) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p < q) (hd : 0 < demand H q) : demand H q < demand H p := by
  have hrq : 0 < raw H q := by
    simpa only [demand, lt_max_iff, lt_self_iff_false, false_or] using hd
  have hx : alpha H/q < alpha H/p := by
    apply (div_lt_div_iff₀ hq hp).mpr
    exact mul_lt_mul_of_pos_left hpq (alpha_pos H)
  have hrp : 0 < raw H p := by unfold raw at *; linarith
  change max 0 (raw H q) < max 0 (raw H p)
  rw [max_eq_right hrq.le, max_eq_right hrp.le]
  exact sub_lt_sub_right hx (eta H)

end PrimaryLogDemand

#print axioms PrimaryLogDemand.alpha_pos
#print axioms PrimaryLogDemand.eta_pos
#print axioms PrimaryLogDemand.raw_identity
#print axioms PrimaryLogDemand.demand_nonnegative
#print axioms PrimaryLogDemand.demand_feasible
#print axioms PrimaryLogDemand.demand_budget_strict
#print axioms PrimaryLogDemand.demand_upper
#print axioms PrimaryLogDemand.demand_euler
#print axioms PrimaryLogDemand.log_tangent
#print axioms PrimaryLogDemand.log_tangent_strict
#print axioms PrimaryLogDemand.gain_bound
#print axioms PrimaryLogDemand.gain_strict
#print axioms PrimaryLogDemand.demand_globally_optimal
#print axioms PrimaryLogDemand.demand_unique_optimum
#print axioms PrimaryLogDemand.voluntary_participation
#print axioms PrimaryLogDemand.positive_subscription_strictly_preferred
#print axioms PrimaryLogDemand.demand_continuousOn
#print axioms PrimaryLogDemand.demand_antitone
#print axioms PrimaryLogDemand.demand_strict_on_active
