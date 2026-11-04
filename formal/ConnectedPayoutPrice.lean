import StrictPrimaryParticipation
import Mathlib.Data.List.Forall2

/-! Three bounded connections; no change to accepted sources or protocols. -/
open scoped BigOperators

namespace StrictExecutedFormation
open ConnectedEnterpriseDemo StrictPrimaryParticipation

theorem actual_strict_formation :
    PrimaryCRRAFormation.Equilibrium profitablePlan economy 2 (fun _ => 3) ∧
    StrictIssuer profitablePlan 2 := by
  refine ⟨strict_fixture.1,?_⟩
  rw [issuer_strict_iff_cost]
  norm_num [profitablePlan,VoluntaryPrimaryMarket.supply]

theorem recorded_supplier_strict :
    (completed.current.state.funds.builderPaid : ℝ)-profitablePlan.physicalCost=1 ∧
    profitablePlan.outside <
      (completed.current.state.funds.builderPaid : ℝ)-profitablePlan.physicalCost := by
  have h := final_numbers.2.2.2.2.2.2.2.2.2
  norm_num [h,profitablePlan]

theorem recorded_buyer_strict (i : Fin 2) :
    PrimaryCRRA.value (buyer i) 2 0 < ledgerValue i := by
  rw [ledger_value_matches]
  exact strict_fixture.2.2.2 i

theorem same_terms :
    (terms.price : ℝ)=2 ∧ (terms.cap : ℝ)=VoluntaryPrimaryMarket.supply profitablePlan ∧
    (terms.reserve : ℝ)=profitablePlan.buffer ∧
    (terms.construction : ℝ)=VoluntaryPrimaryMarket.constructionQuote profitablePlan 2 := by
  norm_num [terms,profitablePlan,VoluntaryPrimaryMarket.supply,
    VoluntaryPrimaryMarket.constructionQuote]

theorem recovered_strict_example :
    PersistentWire.recover genesis yes yes (PersistentWire.storeWire completed)=some completed ∧
    (profitablePlan.outside <
      (completed.current.state.funds.builderPaid : ℝ)-profitablePlan.physicalCost) ∧
    (∀ i : Fin 2, PrimaryCRRA.value (buyer i) 2 0 < ledgerValue i) ∧
    (∀ s : Fin 2, FormationLedgerCore.CashSafe
      (completed.current.state.funds.operating : ℝ) (flows s)) ∧
    (∀ s : Fin 2, FormationLedgerCore.cashAfter
      (completed.current.state.funds.operating : ℝ) (flows s)=6*output s) :=
  ⟨complete_history_recovers,recorded_supplier_strict.2,recorded_buyer_strict,
    operating_affordable,terminal_receipts_match⟩

end StrictExecutedFormation

namespace IntegerPayouts

/-! Ordered cumulative quotas, not the older largest-remainder Python rule.
The account order is a supplied part of this distribution constitution. -/
def quota (amount total offset : ℕ) : ℕ := amount*offset/total
def step (amount total offset weight : ℕ) : ℕ :=
  quota amount total (offset+weight)-quota amount total offset
def allocateAux (amount total : ℕ) : ℕ → List ℕ → List ℕ
  | _,[] => []
  | offset,w::ws => step amount total offset w :: allocateAux amount total (offset+w) ws
def allocate (amount : ℕ) (weights : List ℕ) : List ℕ :=
  allocateAux amount weights.sum 0 weights
def fee (gross bps : ℕ) : ℕ := gross*bps/10000
def settle (gross bps : ℕ) (weights : List ℕ) : ℕ × List ℕ :=
  let f:=fee gross bps
  (f,allocate (gross-f) weights)

theorem quota_mono (amount total : ℕ) {a b : ℕ} (h : a ≤ b) :
    quota amount total a ≤ quota amount total b :=
  Nat.div_le_div_right (Nat.mul_le_mul_left amount h)

theorem step_identity (amount total offset weight : ℕ) :
    step amount total offset weight+quota amount total offset=
      quota amount total (offset+weight) := by
  exact Nat.sub_add_cancel (quota_mono amount total (Nat.le_add_right offset weight))

theorem allocate_sum_aux (amount total offset : ℕ) (ws : List ℕ) :
    (allocateAux amount total offset ws).sum+quota amount total offset=
      quota amount total (offset+ws.sum) := by
  induction ws generalizing offset with
  | nil => simp [allocateAux]
  | cons w ws ih =>
    have hs := step_identity amount total offset w
    have ht := ih (offset+w)
    simp only [allocateAux,List.sum_cons] at ht ⊢
    have he : offset+(w+ws.sum)=(offset+w)+ws.sum := by omega
    rw [he]
    omega

theorem allocate_sum (amount : ℕ) (ws : List ℕ) (hw : 0 < ws.sum) :
    (allocate amount ws).sum=amount := by
  have h := allocate_sum_aux amount ws.sum 0 ws
  simpa [allocate,quota,Nat.mul_div_left _ hw] using h

theorem allocate_length (amount total offset : ℕ) (ws : List ℕ) :
    (allocateAux amount total offset ws).length=ws.length := by
  induction ws generalizing offset with
  | nil => rfl
  | cons w ws ih => simp [allocateAux,ih]

theorem step_zero (amount total offset : ℕ) : step amount total offset 0=0 := by
  simp [step]

theorem step_error (amount total offset weight : ℕ) (ht : 0 < total) :
    step amount total offset weight*total < amount*weight+total ∧
    amount*weight < step amount total offset weight*total+total := by
  have hs := step_identity amount total offset weight
  have hs' := congrArg (fun n => n*total) hs
  simp only [Nat.add_mul,quota] at hs'
  have ha := Nat.div_add_mod' (amount*offset) total
  have hb := Nat.div_add_mod' (amount*(offset+weight)) total
  have hb' := hb.trans (Nat.mul_add amount offset weight)
  have hra := Nat.mod_lt (amount*offset) ht
  have hrb := Nat.mod_lt (amount*(offset+weight)) ht
  have hm : step amount total offset weight*total+(amount*(offset+weight))%total=
      amount*weight+(amount*offset)%total := by omega
  constructor <;> omega

theorem allocate_quotas (amount total offset : ℕ) (ws : List ℕ) (ht : 0 < total) :
    List.Forall₂ (fun w p =>
      p*total < amount*w+total ∧ amount*w < p*total+total ∧ (w=0 → p=0))
      ws (allocateAux amount total offset ws) := by
  induction ws generalizing offset with
  | nil => exact .nil
  | cons w ws ih =>
    refine .cons ⟨(step_error amount total offset w ht).1,
      (step_error amount total offset w ht).2,?_⟩ (ih (offset+w))
    intro hz
    rw [hz,step_zero]

theorem quota_error_real {amount total weight paid : ℕ} (ht : 0 < total)
    (hlo : paid*total < amount*weight+total)
    (hhi : amount*weight < paid*total+total) :
    |(paid : ℝ)-(amount : ℝ)*(weight : ℝ)/(total : ℝ)| < 1 := by
  have ht' : (0 : ℝ) < total := by exact_mod_cast ht
  have hl : (paid : ℝ)*total < (amount : ℝ)*weight+total := by exact_mod_cast hlo
  have hh : (amount : ℝ)*weight < (paid : ℝ)*total+total := by exact_mod_cast hhi
  apply abs_lt.mpr
  constructor
  · have h : (amount : ℝ)*weight/(total : ℝ) < (paid : ℝ)+1 :=
      (div_lt_iff₀ ht').mpr (by nlinarith)
    linarith
  · have h : (paid : ℝ)-1 < (amount : ℝ)*weight/(total : ℝ) :=
      (lt_div_iff₀ ht').mpr (by nlinarith)
    linarith

theorem fee_bound (gross bps : ℕ) (hb : bps ≤ 10000) : fee gross bps ≤ gross := by
  calc
    fee gross bps ≤ gross*10000/10000 := Nat.div_le_div_right (Nat.mul_le_mul_left gross hb)
    _ = gross := Nat.mul_div_left _ (by decide)

theorem settlement_budget (gross bps : ℕ) (ws : List ℕ)
    (hb : bps ≤ 10000) (hw : 0 < ws.sum) :
    (settle gross bps ws).1+(settle gross bps ws).2.sum=gross := by
  change fee gross bps+(allocate (gross-fee gross bps) ws).sum=gross
  rw [allocate_sum _ ws hw]
  have hf := fee_bound gross bps hb
  omega

theorem decoded_budget (delta : ℝ) (gross bps : ℕ) (ws : List ℕ)
    (hb : bps ≤ 10000) (hw : 0 < ws.sum) :
    delta*((settle gross bps ws).1 : ℝ)+
      delta*((settle gross bps ws).2.sum : ℝ)=delta*(gross : ℝ) := by
  have h : ((settle gross bps ws).1 : ℝ)+((settle gross bps ws).2.sum : ℝ)=gross :=
    by exact_mod_cast settlement_budget gross bps ws hb hw
  rw [← mul_add,h]

theorem zero_sum_aux (total offset : ℕ) (ws : List ℕ) :
    (allocateAux 0 total offset ws).sum=0 := by
  induction ws generalizing offset with
  | nil => rfl
  | cons w ws ih => simp [allocateAux,step,quota,ih]

theorem admissible_budget (gross bps : ℕ) (ws : List ℕ)
    (hb : bps ≤ 10000) (hw : 0 < ws.sum ∨ gross-fee gross bps=0) :
    (settle gross bps ws).1+(settle gross bps ws).2.sum=gross := by
  rcases hw with hw | hz
  · exact settlement_budget gross bps ws hb hw
  · have hf := fee_bound gross bps hb
    change fee gross bps+(allocate (gross-fee gross bps) ws).sum=gross
    rw [hz]
    change fee gross bps+(allocateAux 0 ws.sum 0 ws).sum=gross
    rw [zero_sum_aux]
    omega

theorem complete_certificate (gross bps : ℕ) (ws : List ℕ)
    (hb : bps ≤ 10000) (hw : 0 < ws.sum) :
    (settle gross bps ws).1+(settle gross bps ws).2.sum=gross ∧
    (settle gross bps ws).2.length=ws.length ∧
    List.Forall₂ (fun w p =>
      p*ws.sum < (gross-fee gross bps)*w+ws.sum ∧
      (gross-fee gross bps)*w < p*ws.sum+ws.sum ∧ (w=0 → p=0))
      ws (settle gross bps ws).2 :=
  ⟨settlement_budget gross bps ws hb hw,
    allocate_length (gross-fee gross bps) ws.sum 0 ws,
    allocate_quotas (gross-fee gross bps) ws.sum 0 ws hw⟩

theorem exact_examples :
    settle 101 250 [1,2,0,3]=(2,[16,33,0,50]) ∧
    settle 10 10000 [3,3]=(10,[0,0]) ∧
    settle 0 0 [0,0]=(0,[0,0]) := by decide

end IntegerPayouts

noncomputable section
namespace PrimaryPriceCertificates
open PrimaryCRRA PrimaryCRRAFormation VoluntaryPrimaryMarket
variable {I S : Type*} [Fintype I] [Fintype S]

theorem lower_from_score (H : Household S) {q x : ℝ} (hq : 0 < q)
    (hx : Feasible H q x) (hf : 0 ≤ score H q x) : x ≤ demand H q := by
  by_contra hn
  have hs := score_strictAnti H hq (demand_kkt H hq).1 hx (lt_of_not_ge hn)
  linarith [(demand_kkt H hq).2.1]

theorem upper_from_score (H : Household S) {q x : ℝ} (hq : 0 < q)
    (hx : Feasible H q x) (hf : score H q x ≤ 0) : demand H q ≤ x := by
  by_contra hn
  have hd : x < demand H q := lt_of_not_ge hn
  have hz := owned_score_zero H hq (lt_of_le_of_lt hx.1 hd)
  have hs := score_strictAnti H hq hx (demand_kkt H hq).1 hd
  linarith

theorem price_enclosure (P : Plan) (E : Economy I S) {q : ℝ} {a : I → ℝ}
    (he : Equilibrium P E q a) {lo hi : ℝ} (hl : 0 < lo) (hh : 0 < hi)
    (hlo : supply P ≤ aggregate E lo) (hhi : aggregate E hi ≤ supply P) :
    lo ≤ q ∧ q ≤ hi := by
  have hid := actual_optimizer_identified P E he
  have hc : aggregate E q=supply P := by
    unfold PrimaryCRRAFormation.aggregate
    simpa only [← hid] using he.clearing
  constructor
  · by_contra hn
    have hs := aggregate_strict_on_positive E he.price_pos hl (lt_of_not_ge hn)
      (lt_of_lt_of_le (supply_pos P) hlo)
    rw [hc] at hs
    linarith
  · by_contra hn
    have hs := aggregate_strict_on_positive E hh he.price_pos (lt_of_not_ge hn)
      (by rw [hc]; exact supply_pos P)
    rw [hc] at hs
    linarith

theorem midpoint_error {lo hi q : ℝ} (h : lo ≤ q ∧ q ≤ hi) :
    |(lo+hi)/2-q| ≤ (hi-lo)/2 := by
  exact abs_le.mpr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem certified_formation (P : Plan) (E : Economy I S) {lo hi : ℝ}
    (hl : floorPrice P ≤ lo) (hh : lo ≤ hi) (lower upper : I → ℝ)
    (hlo : ∀ i, Feasible (E.buyers i) lo (lower i) ∧ 0 ≤ score (E.buyers i) lo (lower i))
    (hhi : ∀ i, Feasible (E.buyers i) hi (upper i) ∧ score (E.buyers i) hi (upper i) ≤ 0)
    (lsum : supply P ≤ ∑ i, lower i) (usum : (∑ i, upper i) ≤ supply P) :
    ∃ q a, Equilibrium P E q a ∧ lo ≤ q ∧ q ≤ hi ∧
      |(lo+hi)/2-q| ≤ (hi-lo)/2 := by
  have hp : 0 < lo := lt_of_lt_of_le (floor_pos P) hl
  have ht : 0 < hi := lt_of_lt_of_le hp hh
  have hdlo : supply P ≤ aggregate E lo :=
    lsum.trans (Finset.sum_le_sum (fun i _ => lower_from_score (E.buyers i) hp (hlo i).1 (hlo i).2))
  have hdhi : aggregate E hi ≤ supply P :=
    (Finset.sum_le_sum (fun i _ => upper_from_score (E.buyers i) ht (hhi i).1 (hhi i).2)).trans usum
  obtain ⟨q,a,he⟩ := voluntary_formation_exists P E
    (hdlo.trans (aggregate_antitone E (floor_pos P) hp hl))
  have hq := price_enclosure P E he hp ht hdlo hdhi
  exact ⟨q,a,he,hq.1,hq.2,midpoint_error hq⟩

theorem enclosure_strict (P : Plan) {lo q : ℝ}
    (hl : floorPrice P < lo) (hq : lo ≤ q) : StrictPrimaryParticipation.StrictIssuer P q :=
  (StrictPrimaryParticipation.issuer_strict_iff_price P q).mpr (lt_of_lt_of_le hl hq)

theorem midpoint_split_width (lo hi : ℝ) :
    (lo+hi)/2-lo=(hi-lo)/2 ∧ hi-(lo+hi)/2=(hi-lo)/2 := by constructor <;> ring

theorem exact_fixture_score_certificates (i : Fin 2) :
    Feasible (ConnectedEnterpriseDemo.buyer i) (199/100) 3 ∧
    0 ≤ score (ConnectedEnterpriseDemo.buyer i) (199/100) 3 ∧
    Feasible (ConnectedEnterpriseDemo.buyer i) (201/100) 3 ∧
    score (ConnectedEnterpriseDemo.buyer i) (201/100) 3 ≤ 0 := by
  fin_cases i <;>
    norm_num [Feasible,score,current,marginal,future,ConnectedEnterpriseDemo.buyer,
      ConnectedEnterpriseDemo.output,ConnectedEnterpriseDemo.beta,Fin.sum_univ_two,Real.rpow_neg_one]

theorem certified_fixture :
    ∃ q a, Equilibrium StrictPrimaryParticipation.profitablePlan ConnectedEnterpriseDemo.economy q a ∧
      199/100 ≤ q ∧ q ≤ 201/100 ∧ |2-q| ≤ 1/100 := by
  have h := certified_formation StrictPrimaryParticipation.profitablePlan ConnectedEnterpriseDemo.economy
    (lo:=199/100) (hi:=201/100)
    (by norm_num [floorPrice,supply,StrictPrimaryParticipation.profitablePlan]) (by norm_num)
    (fun _ => 3) (fun _ => 3)
    (fun i => ⟨(exact_fixture_score_certificates i).1,(exact_fixture_score_certificates i).2.1⟩)
    (fun i => (exact_fixture_score_certificates i).2.2)
    (by norm_num [supply,StrictPrimaryParticipation.profitablePlan,Fin.sum_univ_two])
    (by norm_num [supply,StrictPrimaryParticipation.profitablePlan,Fin.sum_univ_two])
  norm_num at h ⊢
  exact h

end PrimaryPriceCertificates

#print axioms StrictExecutedFormation.actual_strict_formation
#print axioms StrictExecutedFormation.recorded_supplier_strict
#print axioms StrictExecutedFormation.recorded_buyer_strict
#print axioms StrictExecutedFormation.same_terms
#print axioms StrictExecutedFormation.recovered_strict_example
#print axioms IntegerPayouts.allocate_sum
#print axioms IntegerPayouts.allocate_length
#print axioms IntegerPayouts.step_zero
#print axioms IntegerPayouts.step_error
#print axioms IntegerPayouts.allocate_quotas
#print axioms IntegerPayouts.quota_error_real
#print axioms IntegerPayouts.fee_bound
#print axioms IntegerPayouts.settlement_budget
#print axioms IntegerPayouts.decoded_budget
#print axioms IntegerPayouts.zero_sum_aux
#print axioms IntegerPayouts.admissible_budget
#print axioms IntegerPayouts.complete_certificate
#print axioms IntegerPayouts.exact_examples
#print axioms PrimaryPriceCertificates.lower_from_score
#print axioms PrimaryPriceCertificates.upper_from_score
#print axioms PrimaryPriceCertificates.price_enclosure
#print axioms PrimaryPriceCertificates.midpoint_error
#print axioms PrimaryPriceCertificates.certified_formation
#print axioms PrimaryPriceCertificates.enclosure_strict
#print axioms PrimaryPriceCertificates.midpoint_split_width
#print axioms PrimaryPriceCertificates.exact_fixture_score_certificates
#print axioms PrimaryPriceCertificates.certified_fixture
