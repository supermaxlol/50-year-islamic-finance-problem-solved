import PrimaryCRRADemand
import VoluntaryPrimaryMarket

/-! Conditional voluntary primary formation for independent-income CRRA buyers.
The common productive payoff is explicit; household resources are not aligned
with it. Plan, supplier remuneration and outside option reuse Stage 211. -/
noncomputable section
open scoped BigOperators
open Set

namespace PrimaryCRRAFormation
open PrimaryCRRA VoluntaryPrimaryMarket

structure Economy (I S : Type*) where
  buyers : I → PrimaryCRRA.Household S
  output : S → ℝ
  output_nonneg : ∀ s, 0 ≤ output s
  commonOutput : ∀ i s, (buyers i).output s = output s

theorem common_asset_future {I S : Type*} (E : Economy I S) (i : I) (s : S) (a : ℝ) :
    future (E.buyers i) s a = (E.buyers i).income s+a*E.output s := by
  unfold future
  rw [E.commonOutput]

variable {I S : Type*} [Fintype I] [Fintype S]

def aggregate (E : Economy I S) (q : ℝ) : ℝ := ∑ i, demand (E.buyers i) q

theorem aggregate_continuousOn (E : Economy I S) : ContinuousOn (aggregate E) (Ioi 0) :=
  continuousOn_finsetSum _ (fun i _ => demand_continuousOn (E.buyers i))

theorem aggregate_antitone (E : Economy I S) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) : aggregate E q ≤ aggregate E p :=
  Finset.sum_le_sum (fun i _ => demand_antitone (E.buyers i) hp hq hpq)

theorem aggregate_strict_on_positive (E : Economy I S) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hd : 0 < aggregate E q) :
    aggregate E q < aggregate E p := by
  classical
  have hex : ∃ i, 0 < demand (E.buyers i) q := by
    by_contra hn
    have hh : ∀ i, demand (E.buyers i) q ≤ 0 := fun i => le_of_not_gt (fun h => hn ⟨i,h⟩)
    have hs : aggregate E q ≤ 0 := Finset.sum_nonpos (fun i _ => hh i)
    linarith
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_lt_sum (fun j _ => demand_antitone (E.buyers j) hp hq hpq.le)
    ⟨i,Finset.mem_univ i,demand_strict_on_positive (E.buyers i) hp hq hpq hi⟩

theorem aggregate_upper (E : Economy I S) {q : ℝ} (hq : 0 < q) :
    aggregate E q ≤ (∑ i, (E.buyers i).cash)/q := by
  calc
    _ ≤ ∑ i, (E.buyers i).cash/q :=
      Finset.sum_le_sum (fun i _ => (demand_upper (E.buyers i) hq).le)
    _ = _ := by simp only [div_eq_mul_inv,Finset.sum_mul]

def highPrice (P : Plan) (E : Economy I S) : ℝ :=
  floorPrice P+(∑ i, (E.buyers i).cash)/supply P+1

theorem high_price_bounds (P : Plan) (E : Economy I S) :
    floorPrice P ≤ highPrice P E ∧ 0 < highPrice P E ∧
      aggregate E (highPrice P E) < supply P := by
  have he : 0 ≤ ∑ i, (E.buyers i).cash :=
    Finset.sum_nonneg (fun i _ => (E.buyers i).cash_pos.le)
  have hdiv : 0 ≤ (∑ i, (E.buyers i).cash)/supply P := div_nonneg he (supply_pos P).le
  have hfloor := floor_pos P
  have hge : floorPrice P ≤ highPrice P E := by unfold highPrice; linarith
  have hp : 0 < highPrice P E := lt_of_lt_of_le hfloor hge
  have hx : (∑ i, (E.buyers i).cash) < highPrice P E*supply P := by
    have hid : highPrice P E*supply P =
        floorPrice P*supply P+(∑ i, (E.buyers i).cash)+supply P := by
      unfold highPrice
      field_simp [(supply_pos P).ne']
    rw [hid]
    nlinarith [supply_pos P,mul_pos hfloor (supply_pos P)]
  have hsmall : (∑ i, (E.buyers i).cash)/highPrice P E < supply P := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  exact ⟨hge,hp,lt_of_le_of_lt (aggregate_upper E hp) hsmall⟩

theorem cost_covering_price_exists (P : Plan) (E : Economy I S)
    (hc : supply P ≤ aggregate E (floorPrice P)) :
    ∃ q, 0 < q ∧ floorPrice P ≤ q ∧ aggregate E q = supply P := by
  have hh := high_price_bounds P E
  have hcont : ContinuousOn (aggregate E) (Icc (floorPrice P) (highPrice P E)) :=
    (aggregate_continuousOn E).mono (fun _ hq => lt_of_lt_of_le (floor_pos P) hq.1)
  obtain ⟨q,hq,heq⟩ := intermediate_value_Icc' hh.1 hcont
    (show supply P ∈ Icc (aggregate E (highPrice P E)) (aggregate E (floorPrice P))
      from ⟨hh.2.2.le,hc⟩)
  exact ⟨q,lt_of_lt_of_le (floor_pos P) hq.1,hq.1,heq⟩

theorem clearing_price_unique (P : Plan) (E : Economy I S) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpc : aggregate E p = supply P)
    (hqc : aggregate E q = supply P) : p = q := by
  rcases lt_trichotomy p q with h | h | h
  · have hh := aggregate_strict_on_positive E hp hq h (by rw [hqc]; exact supply_pos P)
    rw [hpc,hqc] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh := aggregate_strict_on_positive E hq hp h (by rw [hpc]; exact supply_pos P)
    rw [hpc,hqc] at hh
    exact False.elim (lt_irrefl _ hh)

structure Equilibrium (P : Plan) (E : Economy I S) (q : ℝ) (a : I → ℝ) : Prop where
  price_pos : 0 < q
  feasible : ∀ i, Feasible (E.buyers i) q (a i)
  optimal : ∀ i x, Feasible (E.buyers i) q x → value (E.buyers i) q x ≤ value (E.buyers i) q (a i)
  clearing : (∑ i, a i) = supply P
  funded : P.physicalCost+P.buffer+P.outside ≤ q*supply P
  issuer_optimal : ∀ enter, issuerUtility P q enter ≤ issuerUtility P q true

theorem voluntary_formation_exists (P : Plan) (E : Economy I S)
    (hc : supply P ≤ aggregate E (floorPrice P)) : ∃ q a, Equilibrium P E q a := by
  obtain ⟨q,hq,hfloor,hclear⟩ := cost_covering_price_exists P E hc
  refine ⟨q,fun i => demand (E.buyers i) q,hq,?_,?_,hclear,?_,?_⟩
  · exact fun i => (demand_kkt (E.buyers i) hq).1
  · exact fun i x hx => actual_global_optimum (E.buyers i) hq hx
  · exact (funding_iff_floor P q).mpr hfloor
  · exact (issuer_entry_iff_funding P q).mpr hfloor

theorem actual_optimizer_identified (P : Plan) (E : Economy I S) {q : ℝ} {a : I → ℝ}
    (he : Equilibrium P E q a) : ∀ i, a i = demand (E.buyers i) q := by
  intro i
  by_contra hn
  have hs := actual_unique_optimum (E.buyers i) he.price_pos (he.feasible i) hn
  have hr := he.optimal i (demand (E.buyers i) q) (demand_kkt (E.buyers i) he.price_pos).1
  linarith

theorem formation_iff_cost_demand (P : Plan) (E : Economy I S) :
    (∃ q a, Equilibrium P E q a) ↔ supply P ≤ aggregate E (floorPrice P) := by
  constructor
  · rintro ⟨q,a,he⟩
    have hid := actual_optimizer_identified P E he
    have hq : floorPrice P ≤ q := (funding_iff_floor P q).mp he.funded
    have hm := aggregate_antitone E (floor_pos P) he.price_pos hq
    have hs : aggregate E q = supply P := by
      unfold aggregate
      simpa only [← hid] using he.clearing
    rw [hs] at hm
    exact hm
  · exact voluntary_formation_exists P E

theorem actual_formation_unique (P : Plan) (E : Economy I S) {p q : ℝ}
    {a b : I → ℝ} (ha : Equilibrium P E p a) (hb : Equilibrium P E q b) : p = q ∧ a = b := by
  have hid := actual_optimizer_identified P E ha
  have hbd := actual_optimizer_identified P E hb
  have hpa : aggregate E p = supply P := by unfold aggregate; simpa only [← hid] using ha.clearing
  have hqb : aggregate E q = supply P := by unfold aggregate; simpa only [← hbd] using hb.clearing
  have heq := clearing_price_unique P E ha.price_pos hb.price_pos hpa hqb
  refine ⟨heq,?_⟩
  funext i
  rw [hid i,hbd i,heq]

theorem actual_subscriber_participation (P : Plan) (E : Economy I S) {q : ℝ}
    {a : I → ℝ} (he : Equilibrium P E q a) : ∀ i, value (E.buyers i) q 0 ≤ value (E.buyers i) q (a i) := by
  intro i
  exact he.optimal i 0 ⟨le_refl 0,by simpa [current] using (E.buyers i).cash_pos⟩

theorem no_funded_formation (P : Plan) (E : Economy I S)
    (hc : aggregate E (floorPrice P) < supply P) : ¬ ∃ q a, Equilibrium P E q a := by
  intro h
  have hh := (formation_iff_cost_demand P E).mp h
  linarith

end PrimaryCRRAFormation

#print axioms PrimaryCRRAFormation.common_asset_future
#print axioms PrimaryCRRAFormation.aggregate_continuousOn
#print axioms PrimaryCRRAFormation.aggregate_antitone
#print axioms PrimaryCRRAFormation.aggregate_strict_on_positive
#print axioms PrimaryCRRAFormation.aggregate_upper
#print axioms PrimaryCRRAFormation.high_price_bounds
#print axioms PrimaryCRRAFormation.cost_covering_price_exists
#print axioms PrimaryCRRAFormation.clearing_price_unique
#print axioms PrimaryCRRAFormation.voluntary_formation_exists
#print axioms PrimaryCRRAFormation.actual_optimizer_identified
#print axioms PrimaryCRRAFormation.formation_iff_cost_demand
#print axioms PrimaryCRRAFormation.actual_formation_unique
#print axioms PrimaryCRRAFormation.actual_subscriber_participation
#print axioms PrimaryCRRAFormation.no_funded_formation
