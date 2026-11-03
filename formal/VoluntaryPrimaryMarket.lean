import PrimaryLogDemand
import Mathlib.Topology.Order.IntermediateValue

/-! Price-taking, fixed-scale formation. The issuer is the construction supplier.
It receives q*N-B, pays physical cost K, and compares the remainder with outside R.
The residual operating cash is exactly B: excess issue proceeds are not lost or
silently counted as fixed future receipts. No voluntary demand regularity is assumed. -/
noncomputable section
open scoped BigOperators
open Set

namespace VoluntaryPrimaryMarket
open PrimaryLogDemand

structure Plan where
  cap : ℕ
  physicalCost : ℝ
  buffer : ℝ
  outside : ℝ
  cap_pos : 0 < cap
  physicalCost_nonneg : 0 ≤ physicalCost
  buffer_nonneg : 0 ≤ buffer
  outside_nonneg : 0 ≤ outside
  total_pos : 0 < physicalCost+buffer+outside

def supply (P : Plan) : ℝ := (P.cap : ℝ)
def floorPrice (P : Plan) : ℝ := (P.physicalCost+P.buffer+P.outside)/supply P
def constructionQuote (P : Plan) (q : ℝ) : ℝ := q*supply P-P.buffer
def issuerUtility (P : Plan) (q : ℝ) (enter : Bool) : ℝ :=
  if enter then constructionQuote P q-P.physicalCost else P.outside

theorem supply_pos (P : Plan) : 0 < supply P := by
  change (0 : ℝ) < (P.cap : ℝ)
  exact_mod_cast P.cap_pos

theorem floor_pos (P : Plan) : 0 < floorPrice P := div_pos P.total_pos (supply_pos P)

theorem funding_iff_floor (P : Plan) (q : ℝ) :
    P.physicalCost+P.buffer+P.outside ≤ q*supply P ↔ floorPrice P ≤ q := by
  exact (div_le_iff₀ (supply_pos P)).symm

theorem issuer_entry_iff_funding (P : Plan) (q : ℝ) :
    (∀ enter, issuerUtility P q enter ≤ issuerUtility P q true) ↔ floorPrice P ≤ q := by
  rw [← funding_iff_floor]
  constructor
  · intro h
    have hh := h false
    simp [issuerUtility, constructionQuote] at hh
    linarith
  · intro h enter
    cases enter with
    | false =>
      change P.outside ≤ q*supply P-P.buffer-P.physicalCost
      linarith
    | true => exact le_rfl

theorem quote_covers_cost_and_outside (P : Plan) (q : ℝ) (hq : floorPrice P ≤ q) :
    P.physicalCost+P.outside ≤ constructionQuote P q := by
  have h := (funding_iff_floor P q).mpr hq
  unfold constructionQuote
  linarith

theorem issue_budget_exact (P : Plan) (q : ℝ) :
    constructionQuote P q+P.buffer = q*supply P := by unfold constructionQuote; ring

section Buyers
variable {I : Type*} [Fintype I]

def aggregate (H : I → Household) (q : ℝ) : ℝ := ∑ i, demand (H i) q

theorem aggregate_nonnegative (H : I → Household) (q : ℝ) : 0 ≤ aggregate H q :=
  Finset.sum_nonneg (fun i _ => demand_nonnegative (H i) q)

theorem aggregate_continuousOn (H : I → Household) :
    ContinuousOn (aggregate H) (Ioi 0) := by
  exact continuousOn_finsetSum _ (fun i _ => demand_continuousOn (H i))

theorem aggregate_upper (H : I → Household) (q : ℝ) (hq : 0 < q) :
    aggregate H q ≤ (∑ i, (H i).cash)/q := by
  unfold aggregate
  calc
    (∑ i, demand (H i) q) ≤ ∑ i, (H i).cash/q :=
      Finset.sum_le_sum (fun i _ => demand_upper (H i) q hq)
    _ = (∑ i, (H i).cash)/q := by simp only [div_eq_mul_inv,Finset.sum_mul]

theorem aggregate_antitone (H : I → Household) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) : aggregate H q ≤ aggregate H p :=
  Finset.sum_le_sum (fun i _ => demand_antitone (H i) hp hq hpq)

theorem aggregate_strict_on_positive (H : I → Household) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hd : 0 < aggregate H q) :
    aggregate H q < aggregate H p := by
  classical
  have hex : ∃ i, 0 < demand (H i) q := by
    by_contra hn
    have hh : ∀ i, demand (H i) q ≤ 0 := fun i => le_of_not_gt (fun h => hn ⟨i,h⟩)
    have hs : aggregate H q ≤ 0 := Finset.sum_nonpos (fun i _ => hh i)
    linarith
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_lt_sum (fun j _ => demand_antitone (H j) hp hq hpq.le)
    ⟨i,Finset.mem_univ i,demand_strict_on_active (H i) hp hq hpq hi⟩

def highPrice (P : Plan) (H : I → Household) : ℝ :=
  floorPrice P+(∑ i, (H i).cash)/supply P+1

theorem high_price_bounds (P : Plan) (H : I → Household) :
    floorPrice P ≤ highPrice P H ∧ 0 < highPrice P H ∧
      aggregate H (highPrice P H) < supply P := by
  have he : 0 ≤ ∑ i, (H i).cash := Finset.sum_nonneg (fun i _ => (H i).cash_pos.le)
  have hdiv : 0 ≤ (∑ i, (H i).cash)/supply P := div_nonneg he (supply_pos P).le
  have hfloor := floor_pos P
  have hge : floorPrice P ≤ highPrice P H := by unfold highPrice; linarith
  have hp : 0 < highPrice P H := lt_of_lt_of_le hfloor hge
  have hx : (∑ i, (H i).cash) < highPrice P H*supply P := by
    have hid : highPrice P H*supply P =
        floorPrice P*supply P+(∑ i, (H i).cash)+supply P := by
      unfold highPrice
      field_simp [(supply_pos P).ne']
    rw [hid]
    nlinarith [supply_pos P,mul_pos hfloor (supply_pos P)]
  have hsmall : (∑ i, (H i).cash)/highPrice P H < supply P := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  exact ⟨hge,hp,lt_of_le_of_lt (aggregate_upper H _ hp) hsmall⟩

theorem cost_covering_price_exists (P : Plan) (H : I → Household)
    (hc : supply P ≤ aggregate H (floorPrice P)) :
    ∃ q, 0 < q ∧ floorPrice P ≤ q ∧ aggregate H q = supply P := by
  have hh := high_price_bounds P H
  have hcont : ContinuousOn (aggregate H) (Icc (floorPrice P) (highPrice P H)) :=
    (aggregate_continuousOn H).mono (fun _ hq => lt_of_lt_of_le (floor_pos P) hq.1)
  have hr := intermediate_value_Icc' hh.1 hcont
    (show supply P ∈ Icc (aggregate H (highPrice P H)) (aggregate H (floorPrice P))
      from ⟨hh.2.2.le,hc⟩)
  obtain ⟨q,hq,heq⟩ := hr
  exact ⟨q,lt_of_lt_of_le (floor_pos P) hq.1,hq.1,heq⟩

theorem clearing_price_unique (P : Plan) (H : I → Household) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpc : aggregate H p = supply P)
    (hqc : aggregate H q = supply P) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · have hh := aggregate_strict_on_positive H hp hq h (by rw [hqc]; exact supply_pos P)
    rw [hpc,hqc] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh := aggregate_strict_on_positive H hq hp h (by rw [hpc]; exact supply_pos P)
    rw [hpc,hqc] at hh
    exact False.elim (lt_irrefl _ hh)

omit [Fintype I] in
theorem actual_optimizer_identified (H : I → Household) (q : ℝ) (a : I → ℝ)
    (hq : 0 < q) (hf : ∀ i, feasible (H i) q (a i))
    (ho : ∀ i x, feasible (H i) q x → utility (H i) q x ≤ utility (H i) q (a i)) :
    ∀ i, a i = demand (H i) q := by
  intro i
  by_contra hn
  have hs := demand_unique_optimum (H i) q (a i) hq (hf i) hn
  have hr := ho i (demand (H i) q) (demand_feasible (H i) q hq)
  linarith

structure Equilibrium (P : Plan) (H : I → Household) (q : ℝ) (a : I → ℝ) : Prop where
  price_pos : 0 < q
  feasible : ∀ i, PrimaryLogDemand.feasible (H i) q (a i)
  optimal : ∀ i x, PrimaryLogDemand.feasible (H i) q x → utility (H i) q x ≤ utility (H i) q (a i)
  clearing : (∑ i, a i) = supply P
  funded : P.physicalCost+P.buffer+P.outside ≤ q*supply P
  issuer_optimal : ∀ enter, issuerUtility P q enter ≤ issuerUtility P q true

theorem voluntary_formation_exists (P : Plan) (H : I → Household)
    (hc : supply P ≤ aggregate H (floorPrice P)) :
    ∃ q a, Equilibrium P H q a := by
  obtain ⟨q,hq,hfloor,hclear⟩ := cost_covering_price_exists P H hc
  refine ⟨q,fun i => demand (H i) q,?_,?_,?_,?_,?_,?_⟩
  · exact hq
  · exact fun i => demand_feasible (H i) q hq
  · exact fun i x hx => demand_globally_optimal (H i) q x hq hx
  · exact hclear
  · exact (funding_iff_floor P q).mpr hfloor
  · exact (issuer_entry_iff_funding P q).mpr hfloor

theorem formation_iff_cost_demand (P : Plan) (H : I → Household) :
    (∃ q a, Equilibrium P H q a) ↔ supply P ≤ aggregate H (floorPrice P) := by
  constructor
  · rintro ⟨q,a,he⟩
    have hid := actual_optimizer_identified H q a he.price_pos he.feasible he.optimal
    have hq : floorPrice P ≤ q := (funding_iff_floor P q).mp he.funded
    have hm := aggregate_antitone H (floor_pos P) he.price_pos hq
    have hs : aggregate H q = supply P := by
      unfold aggregate
      simpa only [← hid] using he.clearing
    rw [hs] at hm
    exact hm
  · exact voluntary_formation_exists P H

theorem actual_formation_unique (P : Plan) (H : I → Household) {p q : ℝ}
    {a b : I → ℝ} (ha : Equilibrium P H p a) (hb : Equilibrium P H q b) :
    p = q ∧ a = b := by
  have hid := actual_optimizer_identified H p a ha.price_pos ha.feasible ha.optimal
  have hbd := actual_optimizer_identified H q b hb.price_pos hb.feasible hb.optimal
  have hpa : aggregate H p = supply P := by
    unfold aggregate; simpa only [← hid] using ha.clearing
  have hqb : aggregate H q = supply P := by
    unfold aggregate; simpa only [← hbd] using hb.clearing
  have heq := clearing_price_unique P H ha.price_pos hb.price_pos hpa hqb
  refine ⟨heq,?_⟩
  funext i
  rw [hid i,hbd i,heq]

theorem actual_subscriber_participation (P : Plan) (H : I → Household)
    (q : ℝ) (a : I → ℝ) (he : Equilibrium P H q a) :
    ∀ i, utility (H i) q 0 ≤ utility (H i) q (a i) := by
  intro i
  exact he.optimal i 0 ⟨le_refl 0,by simpa [current] using (H i).cash_pos⟩

theorem no_formation_below_cost_demand (P : Plan) (H : I → Household)
    (hc : aggregate H (floorPrice P) < supply P) : ¬ ∃ q a, Equilibrium P H q a := by
  intro h
  have hh := (formation_iff_cost_demand P H).mp h
  linarith

end Buyers
end VoluntaryPrimaryMarket

#print axioms VoluntaryPrimaryMarket.supply_pos
#print axioms VoluntaryPrimaryMarket.floor_pos
#print axioms VoluntaryPrimaryMarket.funding_iff_floor
#print axioms VoluntaryPrimaryMarket.issuer_entry_iff_funding
#print axioms VoluntaryPrimaryMarket.quote_covers_cost_and_outside
#print axioms VoluntaryPrimaryMarket.issue_budget_exact
#print axioms VoluntaryPrimaryMarket.aggregate_nonnegative
#print axioms VoluntaryPrimaryMarket.aggregate_continuousOn
#print axioms VoluntaryPrimaryMarket.aggregate_upper
#print axioms VoluntaryPrimaryMarket.aggregate_antitone
#print axioms VoluntaryPrimaryMarket.aggregate_strict_on_positive
#print axioms VoluntaryPrimaryMarket.high_price_bounds
#print axioms VoluntaryPrimaryMarket.cost_covering_price_exists
#print axioms VoluntaryPrimaryMarket.clearing_price_unique
#print axioms VoluntaryPrimaryMarket.actual_optimizer_identified
#print axioms VoluntaryPrimaryMarket.voluntary_formation_exists
#print axioms VoluntaryPrimaryMarket.formation_iff_cost_demand
#print axioms VoluntaryPrimaryMarket.actual_formation_unique
#print axioms VoluntaryPrimaryMarket.actual_subscriber_participation
#print axioms VoluntaryPrimaryMarket.no_formation_below_cost_demand
