import ManyBuyerEscrow
import FormationEscrowConnection

/-! Actual optimal natural-lot allocations execute through the guarded escrow.
Four administrative accounts are separate from every household account. -/
noncomputable section
open scoped BigOperators

namespace OptimalLotsExecution
open PrimaryLogDemand VoluntaryPrimaryMarket FormationEscrowConnection PrimaryEscrow

abbrev Actors (I : Type*) := I ⊕ Fin 4

def initialCash {I : Type*} (H : I → Household) : Actors I → ℝ
  | .inl i => (H i).cash
  | .inr _ => 0

def issuedLots {I : Type*} (n : I → ℕ) : Actors I → ℕ
  | .inl i => n i
  | .inr _ => 0

def executionTerms {I : Type*} (P : Plan) (q : ℝ) (hq : 0 < q) (hf : floorPrice P ≤ q) :
    Terms (Actors I) :=
  escrowTerms P q hq hf (.inr 0) (.inr 1) (.inr 2) (.inr 3)

theorem initial_cash_nonnegative {I : Type*} (H : I → Household) :
    ∀ a, 0 ≤ initialCash H a := by
  intro a
  cases a with
  | inl i => exact (H i).cash_pos.le
  | inr _ => exact le_refl 0

theorem administrative_roles_distinct {I : Type*} (P : Plan) (q : ℝ)
    (hq : 0 < q) (hf : floorPrice P ≤ q) :
    (executionTerms (I := I) P q hq hf).issuer ≠ (executionTerms P q hq hf).custodian ∧
    (executionTerms (I := I) P q hq hf).issuer ≠ (executionTerms P q hq hf).verifier ∧
    (executionTerms (I := I) P q hq hf).issuer ≠ (executionTerms P q hq hf).resolver ∧
    (executionTerms (I := I) P q hq hf).custodian ≠ (executionTerms P q hq hf).verifier ∧
    (executionTerms (I := I) P q hq hf).custodian ≠ (executionTerms P q hq hf).resolver ∧
    (executionTerms (I := I) P q hq hf).verifier ≠ (executionTerms P q hq hf).resolver := by
  norm_num [executionTerms,escrowTerms]

variable {I : Type*} [Fintype I] [DecidableEq I]

def termsFor (P : Plan) (H : I → Household) (q : ℝ) (a : I → ℝ)
    (he : Equilibrium P H q a) : Terms (Actors I) :=
  executionTerms P q he.price_pos ((funding_iff_floor P q).mp he.funded)

omit [DecidableEq I] in
theorem lot_total (P : Plan) (H : I → Household) (q : ℝ) (a : I → ℝ)
    (he : Equilibrium P H q a) (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ)) :
    (∑ actor, issuedLots n actor) = P.cap := by
  have hreal : ((∑ i, n i) : ℝ) = (P.cap : ℝ) := by
    simpa only [hn,supply] using he.clearing
  have hnat : (∑ i, n i) = P.cap := by exact_mod_cast hreal
  simpa [Fintype.sum_sum_type,issuedLots] using hnat

omit [DecidableEq I] in
theorem lots_affordable (P : Plan) (H : I → Household) (q : ℝ) (a : I → ℝ)
    (he : Equilibrium P H q a) (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ)) :
    ∀ actor, q*(issuedLots n actor : ℝ) ≤ initialCash H actor := by
  intro actor
  cases actor with
  | inl i =>
    have h := (he.feasible i).2
    unfold current at h
    rw [hn i] at h
    change q*(n i : ℝ) ≤ (H i).cash
    linarith
  | inr _ => simp [issuedLots,initialCash]

theorem actual_commensurate_execution (P : Plan) (H : I → Household)
    (q : ℝ) (a : I → ℝ) (he : Equilibrium P H q a)
    (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ))
    (consent settled : Actors I → ℕ → ℕ → Prop)
    (hevidence : ∀ i, 0 < n i →
      consent (.inl i) (n i) (ManyBuyerEscrow.receiptId (Sum.inl i : Actors I)) ∧
      settled (.inl i) (n i) (ManyBuyerEscrow.receiptId (Sum.inl i : Actors I))) :
    ∃ s, Reachable (termsFor P H q a he) consent settled (initialCash H) s ∧
      Valid (termsFor P H q a he) (initialCash H) s ∧ s.phase = .released ∧
      (∀ i, (activeUnits s (.inl i) : ℝ) = a i) ∧
      (∀ j, activeUnits s (.inr j) = 0) ∧
      (∀ i, s.funds.wallet (.inl i) = current (H i) q (a i)) ∧
      s.funds.operating = P.buffer ∧
      P.outside ≤ s.funds.builderPaid-P.physicalCost := by
  let T := termsFor P H q a he
  have hcap : (∑ actor, issuedLots n actor) = T.cap := lot_total P H q a he n hn
  have hcash : ∀ actor, T.price*(issuedLots n actor : ℝ) ≤ initialCash H actor :=
    lots_affordable P H q a he n hn
  have hbudget : T.construction+T.reserve ≤ T.price*(T.cap : ℝ) :=
    (issue_budget_exact P q).le
  have hev : ∀ actor, 0 < issuedLots n actor →
      consent actor (issuedLots n actor) (ManyBuyerEscrow.receiptId actor) ∧
      settled actor (issuedLots n actor) (ManyBuyerEscrow.receiptId actor) := by
    intro actor hp
    cases actor with
    | inl i => exact hevidence i hp
    | inr _ => exact False.elim ((Nat.lt_irrefl 0) hp)
  obtain ⟨s,hr,hv,hp,hunits,hbuilder,hoper,_⟩ :=
    ManyBuyerEscrow.release_many T (initialCash H) (issuedLots n) ManyBuyerEscrow.receiptId
      consent settled (initial_cash_nonnegative H) hcash hcap
      ManyBuyerEscrow.receiptId_injective hev hbudget
  refine ⟨s,hr,hv,hp,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hunits (.inl i)]
    exact (hn i).symm
  · intro j
    exact hunits (.inr j)
  · intro i
    have hu : s.funds.units (.inl i) = n i := by
      simpa [activeUnits,hp,issuedLots] using hunits (.inl i)
    have hw := hv.1.subscriber_identity (.inl i)
    change s.funds.wallet (.inl i)+q*(s.funds.units (.inl i) : ℝ) = (H i).cash at hw
    rw [hu,← hn i] at hw
    unfold current
    linarith
  · change s.funds.operating = q*(P.cap : ℝ)-constructionQuote P q at hoper
    unfold constructionQuote supply at hoper
    linarith
  · change s.funds.builderPaid = constructionQuote P q at hbuilder
    have h := quote_covers_cost_and_outside P q ((funding_iff_floor P q).mp he.funded)
    linarith

theorem reached_operating_paths {S : Type*} (P : Plan) (H : I → Household)
    (q : ℝ) (a : I → ℝ) (he : Equilibrium P H q a)
    (consent settled : Actors I → ℕ → ℕ → Prop) (s : State (Actors I))
    (hr : Reachable (termsFor P H q a he) consent settled (initialCash H) s)
    (hp : s.phase = .released) (flows : S → List ℝ)
    (hb : ∀ state, FormationLedgerCore.bufferNeeded (flows state) ≤ P.buffer) :
    ∀ state, FormationLedgerCore.CashSafe s.funds.operating (flows state) ∧
      FormationLedgerCore.cashAfter s.funds.operating (flows state) = P.buffer+(flows state).sum := by
  have hv := reachable_valid (termsFor P H q a he) consent settled (initialCash H)
    (initial_cash_nonnegative H) s hr
  exact released_all_paths_and_receipts (A := Actors I) P q he.price_pos
    ((funding_iff_floor P q).mp he.funded)
    (.inr 0) (.inr 1) (.inr 2) (.inr 3) (initialCash H) s hv hp flows hb

end OptimalLotsExecution

#print axioms OptimalLotsExecution.initial_cash_nonnegative
#print axioms OptimalLotsExecution.administrative_roles_distinct
#print axioms OptimalLotsExecution.lot_total
#print axioms OptimalLotsExecution.lots_affordable
#print axioms OptimalLotsExecution.actual_commensurate_execution
#print axioms OptimalLotsExecution.reached_operating_paths
