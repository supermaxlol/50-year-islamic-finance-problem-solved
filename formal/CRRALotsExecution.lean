import PrimaryCRRAFormation
import OptimalLotsExecution

/-! Actual independent-income CRRA optima, not arbitrary ledger allocations.
Reuse the accepted finite-buyer history and the four separate administrative
accounts. Exact natural-lot compatibility is explicit; nothing is rounded. -/
noncomputable section
open scoped BigOperators

namespace CRRALotsExecution
open PrimaryCRRA VoluntaryPrimaryMarket FormationEscrowConnection PrimaryEscrow

abbrev Actors (I : Type*) := OptimalLotsExecution.Actors I
abbrev issuedLots {I : Type*} := OptimalLotsExecution.issuedLots (I := I)

def initialCash {I S : Type*} (E : PrimaryCRRAFormation.Economy I S) : Actors I → ℝ
  | .inl i => (E.buyers i).cash
  | .inr _ => 0

theorem initial_cash_nonnegative {I S : Type*} (E : PrimaryCRRAFormation.Economy I S) :
    ∀ actor, 0 ≤ initialCash E actor := by
  intro actor
  cases actor with
  | inl i => exact (E.buyers i).cash_pos.le
  | inr _ => exact le_refl 0

variable {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I]

def termsFor (P : Plan) (E : PrimaryCRRAFormation.Economy I S) (q : ℝ) (a : I → ℝ)
    (he : PrimaryCRRAFormation.Equilibrium P E q a) : Terms (Actors I) :=
  OptimalLotsExecution.executionTerms P q he.price_pos ((funding_iff_floor P q).mp he.funded)

omit [DecidableEq I] in
theorem roles_separate (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a) :
    (termsFor P E q a he).issuer ≠ (termsFor P E q a he).custodian ∧
      (termsFor P E q a he).issuer ≠ (termsFor P E q a he).verifier ∧
      (termsFor P E q a he).issuer ≠ (termsFor P E q a he).resolver ∧
      (termsFor P E q a he).custodian ≠ (termsFor P E q a he).verifier ∧
      (termsFor P E q a he).custodian ≠ (termsFor P E q a he).resolver ∧
      (termsFor P E q a he).verifier ≠ (termsFor P E q a he).resolver :=
  OptimalLotsExecution.administrative_roles_distinct P q he.price_pos
    ((funding_iff_floor P q).mp he.funded)

omit [DecidableEq I] in
theorem lot_total (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ)) :
    (∑ actor, issuedLots n actor) = P.cap := by
  have hreal : ((∑ i, n i) : ℝ) = (P.cap : ℝ) := by
    simpa only [hn,supply] using he.clearing
  have hnat : (∑ i, n i) = P.cap := by exact_mod_cast hreal
  simpa [Fintype.sum_sum_type,issuedLots,OptimalLotsExecution.issuedLots] using hnat

omit [DecidableEq I] in
theorem lots_affordable (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ)) :
    ∀ actor, q*(issuedLots n actor : ℝ) ≤ initialCash E actor := by
  intro actor
  cases actor with
  | inl i =>
    have h := (he.feasible i).2
    unfold current at h
    rw [hn i] at h
    change q*(n i : ℝ) ≤ (E.buyers i).cash
    linarith
  | inr _ => simp [issuedLots,OptimalLotsExecution.issuedLots,initialCash]

theorem actual_commensurate_execution (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ))
    (consent settled : Actors I → ℕ → ℕ → Prop)
    (hevidence : ∀ i, 0 < n i →
      consent (.inl i) (n i) (ManyBuyerEscrow.receiptId (Sum.inl i : Actors I)) ∧
      settled (.inl i) (n i) (ManyBuyerEscrow.receiptId (Sum.inl i : Actors I))) :
    ∃ s, Reachable (termsFor P E q a he) consent settled (initialCash E) s ∧
      Valid (termsFor P E q a he) (initialCash E) s ∧ s.phase = .released ∧
      (∀ i, (activeUnits s (.inl i) : ℝ) = a i) ∧
      (∀ j, activeUnits s (.inr j) = 0) ∧
      (∀ i, s.funds.wallet (.inl i) = current (E.buyers i) q (a i)) ∧
      s.funds.operating = P.buffer ∧
      P.outside ≤ s.funds.builderPaid-P.physicalCost := by
  let T := termsFor P E q a he
  have hcap : (∑ actor, issuedLots n actor) = T.cap := lot_total P E q a he n hn
  have hcash : ∀ actor, T.price*(issuedLots n actor : ℝ) ≤ initialCash E actor :=
    lots_affordable P E q a he n hn
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
    ManyBuyerEscrow.release_many T (initialCash E) (issuedLots n) ManyBuyerEscrow.receiptId
      consent settled (initial_cash_nonnegative E) hcash hcap
      ManyBuyerEscrow.receiptId_injective hev hbudget
  refine ⟨s,hr,hv,hp,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hunits (.inl i)]
    exact (hn i).symm
  · intro j
    exact hunits (.inr j)
  · intro i
    have hu : s.funds.units (.inl i) = n i := by
      simpa [activeUnits,hp,issuedLots,OptimalLotsExecution.issuedLots] using hunits (.inl i)
    have hw := hv.1.subscriber_identity (.inl i)
    change s.funds.wallet (.inl i)+q*(s.funds.units (.inl i) : ℝ) = (E.buyers i).cash at hw
    rw [hu,← hn i] at hw
    unfold current
    linarith
  · change s.funds.operating = q*(P.cap : ℝ)-constructionQuote P q at hoper
    unfold constructionQuote supply at hoper
    linarith
  · change s.funds.builderPaid = constructionQuote P q at hbuilder
    have h := quote_covers_cost_and_outside P q ((funding_iff_floor P q).mp he.funded)
    linarith

theorem reached_operating_paths {T : Type*} (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (consent settled : Actors I → ℕ → ℕ → Prop) (s : State (Actors I))
    (hr : Reachable (termsFor P E q a he) consent settled (initialCash E) s)
    (hp : s.phase = .released) (flows : T → List ℝ)
    (hb : ∀ state, FormationLedgerCore.bufferNeeded (flows state) ≤ P.buffer) :
    ∀ state, FormationLedgerCore.CashSafe s.funds.operating (flows state) ∧
      FormationLedgerCore.cashAfter s.funds.operating (flows state) = P.buffer+(flows state).sum := by
  have hv := reachable_valid (termsFor P E q a he) consent settled (initialCash E)
    (initial_cash_nonnegative E) s hr
  exact released_all_paths_and_receipts (A := Actors I) P q he.price_pos
    ((funding_iff_floor P q).mp he.funded)
    (.inr 0) (.inr 1) (.inr 2) (.inr 3) (initialCash E) s hv hp flows hb

omit [DecidableEq I] in
theorem actual_issue_proceeds (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a) :
    (∑ i, q*a i) = constructionQuote P q+P.buffer := by
  rw [← Finset.mul_sum,he.clearing,issue_budget_exact]

omit [DecidableEq I] in
theorem actual_receipt_allocation (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a) (terminalCash : ℝ) :
    (∑ i, a i*(terminalCash/supply P)) = terminalCash := by
  rw [← Finset.sum_mul,he.clearing]
  field_simp [(supply_pos P).ne']

def ledgerValue (E : PrimaryCRRAFormation.Economy I S) (s : State (Actors I)) (i : I) : ℝ :=
  OwnershipCRRA.utility (E.buyers i).gamma (s.funds.wallet (.inl i))+
    ∑ state, (E.buyers i).weight state*OwnershipCRRA.utility ((E.buyers i).eta state)
      ((E.buyers i).income state+(activeUnits s (.inl i) : ℝ)*E.output state)

omit [Fintype I] [DecidableEq I] in
theorem ledger_value_matches (E : PrimaryCRRAFormation.Economy I S) (q : ℝ)
    (a : I → ℝ) (s : State (Actors I))
    (hstock : ∀ i, (activeUnits s (.inl i) : ℝ) = a i)
    (hwallet : ∀ i, s.funds.wallet (.inl i) = current (E.buyers i) q (a i)) :
    ∀ i, ledgerValue E s i = value (E.buyers i) q (a i) := by
  intro i
  unfold ledgerValue value
  rw [hwallet i,hstock i]
  congr 1
  apply Finset.sum_congr rfl
  intro state _
  rw [PrimaryCRRAFormation.common_asset_future]

omit [DecidableEq I] in
theorem reached_optimality_and_participation (P : Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (s : State (Actors I))
    (hstock : ∀ i, (activeUnits s (.inl i) : ℝ) = a i)
    (hwallet : ∀ i, s.funds.wallet (.inl i) = current (E.buyers i) q (a i)) :
    (∀ i x, Feasible (E.buyers i) q x → value (E.buyers i) q x ≤ ledgerValue E s i) ∧
      (∀ i, value (E.buyers i) q 0 ≤ ledgerValue E s i) := by
  have hm := ledger_value_matches E q a s hstock hwallet
  constructor
  · intro i x hx
    rw [hm i]
    exact he.optimal i x hx
  · intro i
    rw [hm i]
    exact PrimaryCRRAFormation.actual_subscriber_participation P E he i

theorem actual_formation_lifecycle {T : Type*} (P : Plan)
    (E : PrimaryCRRAFormation.Economy I S) (q : ℝ) (a : I → ℝ)
    (he : PrimaryCRRAFormation.Equilibrium P E q a)
    (n : I → ℕ) (hn : ∀ i, a i = (n i : ℝ))
    (consent settled : Actors I → ℕ → ℕ → Prop)
    (hevidence : ∀ i, 0 < n i →
      consent (.inl i) (n i) (ManyBuyerEscrow.receiptId (Sum.inl i : Actors I)) ∧
      settled (.inl i) (n i) (ManyBuyerEscrow.receiptId (Sum.inl i : Actors I)))
    (flows : T → List ℝ)
    (hb : ∀ state, FormationLedgerCore.bufferNeeded (flows state) ≤ P.buffer) :
    ∃ s, Reachable (termsFor P E q a he) consent settled (initialCash E) s ∧
      Valid (termsFor P E q a he) (initialCash E) s ∧ s.phase = .released ∧
      (∀ i, (activeUnits s (.inl i) : ℝ) = a i) ∧
      (∀ j, activeUnits s (.inr j) = 0) ∧
      (∀ i, s.funds.wallet (.inl i) = current (E.buyers i) q (a i)) ∧
      s.funds.operating = P.buffer ∧
      P.outside ≤ s.funds.builderPaid-P.physicalCost ∧
      (∀ i x, Feasible (E.buyers i) q x → value (E.buyers i) q x ≤ ledgerValue E s i) ∧
      (∀ i, value (E.buyers i) q 0 ≤ ledgerValue E s i) ∧
      (∀ state, FormationLedgerCore.CashSafe s.funds.operating (flows state) ∧
        FormationLedgerCore.cashAfter s.funds.operating (flows state) = P.buffer+(flows state).sum) := by
  obtain ⟨s,hr,hv,hp,hstock,hadmin,hwallet,hbuffer,hissuer⟩ :=
    actual_commensurate_execution P E q a he n hn consent settled hevidence
  have hu := reached_optimality_and_participation P E q a he s hstock hwallet
  have hf := reached_operating_paths P E q a he consent settled s hr hp flows hb
  exact ⟨s,hr,hv,hp,hstock,hadmin,hwallet,hbuffer,hissuer,hu.1,hu.2,hf⟩

end CRRALotsExecution

#print axioms CRRALotsExecution.initial_cash_nonnegative
#print axioms CRRALotsExecution.roles_separate
#print axioms CRRALotsExecution.lot_total
#print axioms CRRALotsExecution.lots_affordable
#print axioms CRRALotsExecution.actual_commensurate_execution
#print axioms CRRALotsExecution.reached_operating_paths
#print axioms CRRALotsExecution.actual_issue_proceeds
#print axioms CRRALotsExecution.actual_receipt_allocation
#print axioms CRRALotsExecution.ledger_value_matches
#print axioms CRRALotsExecution.reached_optimality_and_participation
#print axioms CRRALotsExecution.actual_formation_lifecycle
