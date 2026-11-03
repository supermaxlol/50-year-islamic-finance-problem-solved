import VoluntaryPrimaryMarket
import EscrowFundingBridge
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Option

/-! Physical receipts, explicit issuer construction remuneration, and a bounded
escrow connection. General real allocations are not silently rounded to integer lots. -/
noncomputable section
open scoped BigOperators

namespace FormationEscrowConnection
open PrimaryLogDemand VoluntaryPrimaryMarket

structure Future (S : Type*) where
  weights : S → ℝ
  payoff : S → ℝ
  weights_nonnegative : ∀ s, 0 ≤ weights s
  payoff_pos : ∀ s, 0 < payoff s

def physicalUtility {S : Type*} [Fintype S] (H : Household) (F : Future S)
    (q a : ℝ) : ℝ := Real.log (current H q a) +
      ∑ s, F.weights s * Real.log ((H.background+a)*F.payoff s)

theorem physical_normalization {S : Type*} [Fintype S] (H : Household) (F : Future S)
    (hw : (∑ s, F.weights s) = H.weight) (q a : ℝ) (ha : 0 ≤ a) :
    physicalUtility H F q a = utility H q a + ∑ s, F.weights s*Real.log (F.payoff s) := by
  have hp : 0 < H.background+a := add_pos_of_pos_of_nonneg H.background_pos ha
  have he : (∑ s, F.weights s*Real.log ((H.background+a)*F.payoff s)) =
      (∑ s, F.weights s)*Real.log (H.background+a) +
        ∑ s, F.weights s*Real.log (F.payoff s) := by
    calc
      (∑ s, F.weights s*Real.log ((H.background+a)*F.payoff s)) =
          ∑ s, (F.weights s*Real.log (H.background+a)+F.weights s*Real.log (F.payoff s)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Real.log_mul hp.ne' (F.payoff_pos s).ne',mul_add]
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_mul]
  unfold physicalUtility utility
  rw [he,hw]
  ring

theorem actual_physical_optimizer {S : Type*} [Fintype S] (H : Household) (F : Future S)
    (hw : (∑ s, F.weights s) = H.weight) (q a : ℝ) (hq : 0 < q)
    (ha : feasible H q a) : physicalUtility H F q a ≤ physicalUtility H F q (demand H q) := by
  rw [physical_normalization H F hw q a ha.1,
    physical_normalization H F hw q (demand H q) (demand_nonnegative H q)]
  linarith [demand_globally_optimal H q a hq ha]

theorem actual_physical_participation {S : Type*} [Fintype S] (H : Household) (F : Future S)
    (hw : (∑ s, F.weights s) = H.weight) (q : ℝ) (hq : 0 < q) :
    physicalUtility H F q 0 ≤ physicalUtility H F q (demand H q) := by
  apply actual_physical_optimizer H F hw q 0 hq
  exact ⟨le_refl 0,by simpa [current] using H.cash_pos⟩

def escrowTerms {A : Type*} (P : Plan) (q : ℝ) (hq : 0 < q) (hf : floorPrice P ≤ q)
    (issuer custodian verifier resolver : A) : PrimaryEscrow.Terms A where
  price := q
  price_pos := hq
  cap := P.cap
  cap_pos := P.cap_pos
  construction := constructionQuote P q
  construction_nonneg := le_trans (add_nonneg P.physicalCost_nonneg P.outside_nonneg)
    (quote_covers_cost_and_outside P q hf)
  reserve := P.buffer
  reserve_nonneg := P.buffer_nonneg
  subscribeDeadline := 10
  releaseDeadline := 20
  deadline_order := by decide
  issuer := issuer
  custodian := custodian
  verifier := verifier
  resolver := resolver

theorem released_reserve_exact {A : Type*} [Fintype A] (P : Plan) (q : ℝ)
    (hq : 0 < q) (hf : floorPrice P ≤ q) (issuer custodian verifier resolver : A)
    (cash : A → ℝ) (s : PrimaryEscrow.State A)
    (hv : PrimaryEscrow.Valid (escrowTerms P q hq hf issuer custodian verifier resolver) cash s)
    (hp : s.phase = .released) : s.funds.operating = P.buffer := by
  have hh := hv.2
  simp only [PrimaryEscrow.PhaseSound,hp] at hh
  have he := hh.2.2.2.1
  change s.funds.operating = q*(P.cap : ℝ)-constructionQuote P q at he
  unfold constructionQuote supply at he
  linarith

theorem released_issuer_participation {A : Type*} [Fintype A] (P : Plan) (q : ℝ)
    (hq : 0 < q) (hf : floorPrice P ≤ q) (issuer custodian verifier resolver : A)
    (cash : A → ℝ) (s : PrimaryEscrow.State A)
    (hv : PrimaryEscrow.Valid (escrowTerms P q hq hf issuer custodian verifier resolver) cash s)
    (hp : s.phase = .released) : P.outside ≤ s.funds.builderPaid-P.physicalCost := by
  have hh := (PrimaryEscrow.released_construction_and_buffer _ cash s hv hp).1
  change s.funds.builderPaid = constructionQuote P q at hh
  have h := quote_covers_cost_and_outside P q hf
  linarith

theorem released_all_paths_and_receipts {A S : Type*} [Fintype A] (P : Plan) (q : ℝ)
    (hq : 0 < q) (hf : floorPrice P ≤ q) (issuer custodian verifier resolver : A)
    (cash : A → ℝ) (s : PrimaryEscrow.State A)
    (hv : PrimaryEscrow.Valid (escrowTerms P q hq hf issuer custodian verifier resolver) cash s)
    (hp : s.phase = .released) (flows : S → List ℝ)
    (hb : ∀ state, FormationLedgerCore.bufferNeeded (flows state) ≤ P.buffer) :
    ∀ state, FormationLedgerCore.CashSafe s.funds.operating (flows state) ∧
      FormationLedgerCore.cashAfter s.funds.operating (flows state) = P.buffer+(flows state).sum := by
  have he := released_reserve_exact P q hq hf issuer custodian verifier resolver cash s hv hp
  have hs := PrimaryEscrow.released_all_paths_affordable _ cash s hv hp flows hb
  intro state
  exact ⟨hs state,by rw [FormationLedgerCore.cash_after_identity,he]⟩

theorem actual_issue_proceeds {I : Type*} [Fintype I] (P : Plan) (H : I → Household)
    (q : ℝ) (a : I → ℝ) (he : Equilibrium P H q a) :
    (∑ i, q*a i) = constructionQuote P q+P.buffer := by
  rw [← Finset.mul_sum,he.clearing,issue_budget_exact]

theorem actual_receipt_allocation {I : Type*} [Fintype I] (P : Plan) (H : I → Household)
    (q : ℝ) (a : I → ℝ) (he : Equilibrium P H q a) (terminalCash : ℝ) :
    (∑ i, a i*(terminalCash/supply P)) = terminalCash := by
  rw [← Finset.sum_mul,he.clearing]
  field_simp [(supply_pos P).ne']

/-! Exact nonvacuity witness: one buyer optimally buys two integer units;
the supplier is the issuer, and settlement/consent are trusted predicates. -/
def exampleHousehold : Household := ⟨30,1,1,by norm_num,by norm_num,by norm_num⟩
def examplePlan : Plan := ⟨2,4,2,1,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem example_demand : demand exampleHousehold 6 = 2 := by
  norm_num [demand,raw,alpha,eta,exampleHousehold]

theorem example_actual_formation :
    Equilibrium examplePlan (fun _ : Unit => exampleHousehold) 6 (fun _ => 2) := by
  constructor
  · norm_num
  · intro i; norm_num [feasible,current,exampleHousehold]
  · intro i x hx
    simpa only [example_demand] using demand_globally_optimal exampleHousehold 6 x (by norm_num) hx
  · simp [supply,examplePlan]
  · norm_num [supply,examplePlan]
  · apply (issuer_entry_iff_funding examplePlan 6).mpr
    norm_num [floorPrice,supply,examplePlan]

def exampleCash : Option Unit → ℝ | none => 0 | some _ => 30
def exampleTerms : PrimaryEscrow.Terms (Option Unit) :=
  escrowTerms examplePlan 6 (by norm_num)
    (by norm_num [floorPrice,supply,examplePlan]) none none none none
def exampleConsent : Option Unit → ℕ → ℕ → Prop := fun a n r => a=some () ∧ n=2 ∧ r=0
def exampleSubscribed : PrimaryEscrow.State (Option Unit) :=
  PrimaryEscrow.settle exampleTerms (PrimaryEscrow.initial exampleCash) (some ()) 2 0
def exampleFunded : PrimaryEscrow.State (Option Unit) := PrimaryEscrow.fund exampleSubscribed
def exampleApproved : PrimaryEscrow.State (Option Unit) := PrimaryEscrow.attest exampleFunded Finset.univ
def exampleReleased : PrimaryEscrow.State (Option Unit) := PrimaryEscrow.release exampleTerms exampleApproved

theorem example_reachable :
    PrimaryEscrow.Reachable exampleTerms exampleConsent exampleConsent exampleCash exampleReleased := by
  have h1 : PrimaryEscrow.Reachable exampleTerms exampleConsent exampleConsent exampleCash exampleSubscribed := by
    apply PrimaryEscrow.Reachable.next PrimaryEscrow.Reachable.start
    apply PrimaryEscrow.Step.subscribe (PrimaryEscrow.initial exampleCash) none (some ()) 2 0
    all_goals norm_num [exampleTerms,escrowTerms,examplePlan,exampleCash,exampleConsent,
      PrimaryEscrow.initial,PrimaryEscrow.totalUnits]
  have h2 : PrimaryEscrow.Reachable exampleTerms exampleConsent exampleConsent exampleCash exampleFunded := by
    apply PrimaryEscrow.Reachable.next h1
    apply PrimaryEscrow.Step.close exampleSubscribed none
    all_goals norm_num [exampleSubscribed,exampleTerms,escrowTerms,examplePlan,supply,constructionQuote,
      PrimaryEscrow.initial,PrimaryEscrow.settle,PrimaryEscrow.totalUnits,FormationLedgerCore.natCredit,
      univ_option]
  have h3 : PrimaryEscrow.Reachable exampleTerms exampleConsent exampleConsent exampleCash exampleApproved :=
    PrimaryEscrow.Reachable.next h2 (PrimaryEscrow.Step.approve exampleFunded none Finset.univ rfl)
  apply PrimaryEscrow.Reachable.next h3
  apply PrimaryEscrow.Step.payConstruction exampleApproved none
  all_goals simp [exampleApproved,exampleFunded,exampleSubscribed,exampleTerms,escrowTerms,
    PrimaryEscrow.attest,PrimaryEscrow.fund,PrimaryEscrow.settle,PrimaryEscrow.initial]

theorem example_verified_lifecycle :
    PrimaryEscrow.Valid exampleTerms exampleCash exampleReleased ∧
      exampleReleased.phase = .released ∧ exampleReleased.funds.builderPaid = 10 ∧
      exampleReleased.funds.operating = 2 ∧ PrimaryEscrow.activeUnits exampleReleased (some ()) = 2 := by
  refine ⟨PrimaryEscrow.reachable_valid exampleTerms exampleConsent exampleConsent exampleCash
    (by intro a; cases a <;> norm_num [exampleCash]) exampleReleased example_reachable,?_,?_,?_,?_⟩
  all_goals norm_num [exampleReleased,exampleApproved,exampleFunded,exampleSubscribed,exampleTerms,
    escrowTerms,examplePlan,supply,constructionQuote,PrimaryEscrow.release,PrimaryEscrow.attest,
    PrimaryEscrow.fund,PrimaryEscrow.settle,PrimaryEscrow.initial,PrimaryEscrow.activeUnits,
    FormationLedgerCore.natCredit]

end FormationEscrowConnection

#print axioms FormationEscrowConnection.physical_normalization
#print axioms FormationEscrowConnection.actual_physical_optimizer
#print axioms FormationEscrowConnection.actual_physical_participation
#print axioms FormationEscrowConnection.released_reserve_exact
#print axioms FormationEscrowConnection.released_issuer_participation
#print axioms FormationEscrowConnection.released_all_paths_and_receipts
#print axioms FormationEscrowConnection.actual_issue_proceeds
#print axioms FormationEscrowConnection.actual_receipt_allocation
#print axioms FormationEscrowConnection.example_demand
#print axioms FormationEscrowConnection.example_actual_formation
#print axioms FormationEscrowConnection.example_reachable
#print axioms FormationEscrowConnection.example_verified_lifecycle
