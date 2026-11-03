import PrimaryCRRAObjective
import Mathlib.Topology.Order.IntermediateValue

/-! Demand is constructed from primitives and proved actually optimal.
There is no assumed demand regularity, root or risk-free lending benchmark. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace PrimaryCRRA
variable {S : Type*} [Fintype S]

def rootCash (H : Household S) (q : ℝ) : ℝ :=
  (q/(marginal H 0+q))^(1/H.gamma)
def cutCash (H : Household S) (q : ℝ) : ℝ := min (H.cash/2) (rootCash H q)
def upperChoice (H : Household S) (q : ℝ) : ℝ := (H.cash-cutCash H q)/q

theorem rootCash_positive (H : Household S) {q : ℝ} (hq : 0 < q) : 0 < rootCash H q := by
  exact Real.rpow_pos_of_pos (div_pos hq (add_pos_of_nonneg_of_pos
    (marginal_nonnegative H (le_refl 0)) hq)) _

theorem rootCash_identity (H : Household S) {q : ℝ} (hq : 0 < q) :
    q*(rootCash H q)^(-H.gamma) = marginal H 0+q := by
  have hden : 0 < marginal H 0+q := add_pos_of_nonneg_of_pos
    (marginal_nonnegative H (le_refl 0)) hq
  have hbase : 0 < q/(marginal H 0+q) := div_pos hq hden
  have hexp : (1/H.gamma)*(-H.gamma) = -1 := by field_simp [H.gamma_pos.ne']
  unfold rootCash
  rw [← Real.rpow_mul hbase.le,hexp,Real.rpow_neg_one]
  field_simp [hq.ne',hden.ne']

theorem upperChoice_feasible (H : Household S) {q : ℝ} (hq : 0 < q) :
    Feasible H q (upperChoice H q) ∧ current H q (upperChoice H q) = cutCash H q := by
  have hc : 0 < cutCash H q := lt_min (div_pos H.cash_pos (by norm_num)) (rootCash_positive H hq)
  have hle : cutCash H q ≤ H.cash/2 := min_le_left _ _
  have ha : 0 ≤ upperChoice H q := by
    apply div_nonneg _ hq.le
    linarith [H.cash_pos]
  have hid : current H q (upperChoice H q) = cutCash H q := by
    unfold current upperChoice
    field_simp [hq.ne']
    ring
  exact ⟨⟨ha,by rw [hid]; exact hc⟩,hid⟩

theorem upperChoice_score_negative (H : Household S) {q : ℝ} (hq : 0 < q) :
    score H q (upperChoice H q) < 0 := by
  have hf := upperChoice_feasible H hq
  have hm := marginal_antitone H (le_refl 0) hf.1.1
  have hcut : 0 < cutCash H q := by rw [← hf.2]; exact hf.1.2
  have hpow := Real.rpow_le_rpow_of_nonpos hcut (min_le_right (H.cash/2) (rootCash H q))
    (show -H.gamma ≤ 0 by linarith [H.gamma_pos])
  have hcost := mul_le_mul_of_nonneg_left hpow hq.le
  rw [rootCash_identity H hq] at hcost
  unfold score
  rw [hf.2]
  linarith

theorem marginal_continuousOn (H : Household S) : ContinuousOn (marginal H) (Ici 0) := by
  apply continuousOn_finsetSum
  intro s _
  have hc : ContinuousOn (future H s) (Ici 0) :=
    continuousOn_const.add (continuousOn_id.mul_const (H.output s))
  exact continuousOn_const.mul (hc.rpow_const (fun a ha => Or.inl (future_pos H ha s).ne'))

omit [Fintype S] in
theorem current_price_continuous (H : Household S) (q a : ℝ) :
    ContinuousAt (fun p => current H p a) q :=
  continuousAt_const.sub (continuousAt_id.mul_const a)

theorem score_price_continuous (H : Household S) {q a : ℝ} (hc : 0 < current H q a) :
    ContinuousAt (fun p => score H p a) q :=
  continuousAt_const.sub (continuousAt_id.mul
    ((current_price_continuous H q a).rpow_const (Or.inl hc.ne')))

omit [Fintype S] in
theorem interval_feasible (H : Household S) {q b x : ℝ} (hq : 0 < q)
    (hb : Feasible H q b) (hx : x ∈ Icc 0 b) : Feasible H q x := by
  refine ⟨hx.1,?_⟩
  have hc := hb.2
  unfold current at hc ⊢
  nlinarith [hx.2]

theorem score_continuousOn_interval (H : Household S) {q b : ℝ} (hq : 0 < q)
    (hb : Feasible H q b) : ContinuousOn (score H q) (Icc 0 b) := by
  have hm : ContinuousOn (marginal H) (Icc 0 b) :=
    (marginal_continuousOn H).mono (fun _ hx => hx.1)
  have hc : ContinuousOn (current H q) (Icc 0 b) :=
    continuousOn_const.sub (continuousOn_const.mul continuousOn_id)
  exact hm.sub (continuousOn_const.mul (hc.rpow_const (fun x hx =>
    Or.inl (interval_feasible H hq hb hx).2.ne')))

theorem kkt_exists (H : Household S) {q : ℝ} (hq : 0 < q) : ∃ a, KKT H q a := by
  by_cases hzero : score H q 0 ≤ 0
  · exact ⟨0,⟨le_refl 0,by simpa [current] using H.cash_pos⟩,hzero,by simp⟩
  · have hb := (upperChoice_feasible H hq).1
    have hc := score_continuousOn_interval H hq hb
    obtain ⟨a,ha,he⟩ := intermediate_value_Icc' hb.1 hc
      (show 0 ∈ Icc (score H q (upperChoice H q)) (score H q 0) from
        ⟨(upperChoice_score_negative H hq).le,(lt_of_not_ge hzero).le⟩)
    exact ⟨a,interval_feasible H hq hb ha,he.le,by rw [he,mul_zero]⟩

def demand (H : Household S) (q : ℝ) : ℝ :=
  if hq : 0 < q then (kkt_exists H hq).choose else 0

theorem demand_kkt (H : Household S) {q : ℝ} (hq : 0 < q) : KKT H q (demand H q) := by
  simpa only [demand,dite_eq_left hq] using (kkt_exists H hq).choose_spec

theorem demand_nonnegative (H : Household S) (q : ℝ) : 0 ≤ demand H q := by
  by_cases hq : 0 < q
  · exact (demand_kkt H hq).1.1
  · simp [demand,hq]

theorem demand_budget_strict (H : Household S) {q : ℝ} (hq : 0 < q) :
    q*demand H q < H.cash := by
  have h := (demand_kkt H hq).1.2
  unfold current at h
  linarith

theorem demand_upper (H : Household S) {q : ℝ} (hq : 0 < q) : demand H q < H.cash/q := by
  apply (lt_div_iff₀ hq).mpr
  nlinarith [demand_budget_strict H hq]

theorem actual_global_optimum (H : Household S) {q a : ℝ} (hq : 0 < q)
    (ha : Feasible H q a) : value H q a ≤ value H q (demand H q) :=
  kkt_globally_optimal H (demand_kkt H hq) ha

theorem actual_unique_optimum (H : Household S) {q a : ℝ} (hq : 0 < q)
    (ha : Feasible H q a) (hne : a ≠ demand H q) : value H q a < value H q (demand H q) :=
  kkt_unique_optimum H hq (demand_kkt H hq) ha hne

theorem voluntary_participation (H : Household S) {q : ℝ} (hq : 0 < q) :
    value H q 0 ≤ value H q (demand H q) :=
  actual_global_optimum H hq ⟨le_refl 0,by simpa [current] using H.cash_pos⟩

theorem owned_score_zero (H : Household S) {q : ℝ} (hq : 0 < q) (hd : 0 < demand H q) :
    score H q (demand H q) = 0 :=
  (mul_eq_zero.mp (demand_kkt H hq).2.2).resolve_left hd.ne'

theorem positive_score_below (H : Household S) {q x : ℝ} (hq : 0 < q)
    (hx : Feasible H q x) (hf : 0 < score H q x) : x < demand H q := by
  by_contra hn
  rcases lt_or_eq_of_le (le_of_not_gt hn) with h | h
  · have hs := score_strictAnti H hq (demand_kkt H hq).1 hx h
    linarith [(demand_kkt H hq).2.1]
  · rw [← h] at hf
    linarith [(demand_kkt H hq).2.1]

theorem negative_score_above (H : Household S) {q x : ℝ} (hq : 0 < q)
    (hx : Feasible H q x) (hp : 0 < x) (hf : score H q x < 0) : demand H q < x := by
  by_contra hn
  have hd : 0 < demand H q := lt_of_lt_of_le hp (le_of_not_gt hn)
  have hz := owned_score_zero H hq hd
  rcases lt_or_eq_of_le (le_of_not_gt hn) with h | h
  · have hs := score_strictAnti H hq hx (demand_kkt H hq).1 h
    linarith
  · rw [h] at hf
    linarith

theorem demand_strict_on_positive (H : Household S) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hd : 0 < demand H q) :
    demand H q < demand H p := by
  have hz := owned_score_zero H hq hd
  have hs := score_price_strictAnti H hp hpq (demand_kkt H hq).1
  apply positive_score_below H hp (lower_price_feasible H hpq.le (demand_kkt H hq).1)
  linarith

theorem demand_antitone (H : Household S) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) : demand H q ≤ demand H p := by
  rcases lt_or_eq_of_le hpq with h | h
  · by_cases hd : 0 < demand H q
    · exact (demand_strict_on_positive H hp hq h hd).le
    · have hz : demand H q = 0 := le_antisymm (le_of_not_gt hd) (demand_nonnegative H q)
      rw [hz]
      exact demand_nonnegative H p
  · rw [h]

theorem demand_continuousAt (H : Household S) {q : ℝ} (hq : 0 < q) :
    ContinuousAt (demand H) q := by
  apply tendsto_order.2
  constructor
  · intro l hl
    by_cases hn : l < 0
    · exact Filter.Eventually.of_forall (fun p => lt_of_lt_of_le hn (demand_nonnegative H p))
    · have hl0 : 0 ≤ l := le_of_not_gt hn
      have hf : Feasible H q l := by
        refine ⟨hl0,?_⟩
        have hd := (demand_kkt H hq).1.2
        unfold current at hd ⊢
        nlinarith
      have hdpos : 0 < demand H q := lt_of_le_of_lt hl0 hl
      have hs : 0 < score H q l := by
        have h := score_strictAnti H hq hf (demand_kkt H hq).1 hl
        rw [owned_score_zero H hq hdpos] at h
        exact h
      have hec := (current_price_continuous H q l).eventually (eventually_gt_nhds hf.2)
      have hes := (score_price_continuous H hf.2).eventually (eventually_gt_nhds hs)
      filter_upwards [eventually_gt_nhds hq,hec,hes] with p hp hc hs
      exact positive_score_below H hp ⟨hl0,hc⟩ hs
  · intro u hu
    obtain ⟨b,hb0,hb⟩ := exists_between (lt_min hu (demand_upper H hq))
    have hbpos : 0 < b := lt_of_le_of_lt (demand_nonnegative H q) hb0
    have hbu : b < u := lt_of_lt_of_le hb (min_le_left _ _)
    have hbe : b < H.cash/q := lt_of_lt_of_le hb (min_le_right _ _)
    have hf : Feasible H q b := by
      refine ⟨hbpos.le,?_⟩
      have h := (lt_div_iff₀ hq).mp hbe
      unfold current
      nlinarith
    have hs : score H q b < 0 := by
      have h := score_strictAnti H hq (demand_kkt H hq).1 hf hb0
      exact lt_of_lt_of_le h (demand_kkt H hq).2.1
    have hec := (current_price_continuous H q b).eventually (eventually_gt_nhds hf.2)
    have hes := (score_price_continuous H hf.2).eventually (eventually_lt_nhds hs)
    filter_upwards [eventually_gt_nhds hq,hec,hes] with p hp hc hs
    exact lt_trans (negative_score_above H hp ⟨hbpos.le,hc⟩ hbpos hs) hbu

theorem demand_continuousOn (H : Household S) : ContinuousOn (demand H) (Ioi 0) :=
  fun _ hq => (demand_continuousAt H hq).continuousWithinAt

end PrimaryCRRA

#print axioms PrimaryCRRA.rootCash_positive
#print axioms PrimaryCRRA.rootCash_identity
#print axioms PrimaryCRRA.upperChoice_feasible
#print axioms PrimaryCRRA.upperChoice_score_negative
#print axioms PrimaryCRRA.marginal_continuousOn
#print axioms PrimaryCRRA.current_price_continuous
#print axioms PrimaryCRRA.score_price_continuous
#print axioms PrimaryCRRA.interval_feasible
#print axioms PrimaryCRRA.score_continuousOn_interval
#print axioms PrimaryCRRA.kkt_exists
#print axioms PrimaryCRRA.demand_kkt
#print axioms PrimaryCRRA.demand_nonnegative
#print axioms PrimaryCRRA.demand_budget_strict
#print axioms PrimaryCRRA.demand_upper
#print axioms PrimaryCRRA.actual_global_optimum
#print axioms PrimaryCRRA.actual_unique_optimum
#print axioms PrimaryCRRA.voluntary_participation
#print axioms PrimaryCRRA.owned_score_zero
#print axioms PrimaryCRRA.positive_score_below
#print axioms PrimaryCRRA.negative_score_above
#print axioms PrimaryCRRA.demand_strict_on_positive
#print axioms PrimaryCRRA.demand_antitone
#print axioms PrimaryCRRA.demand_continuousAt
#print axioms PrimaryCRRA.demand_continuousOn
