import PrimaryCRRAFormation
import PersistentWire

/-! One exact risky economic witness connected to the executable funding core.
Evidence remains supplied; the persistent database is tested, not kernel-proved. -/
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace ConnectedEnterpriseDemo

noncomputable def output (s : Fin 2) : ℝ := if s=0 then 2 else 0
noncomputable def beta (i : Fin 2) : ℝ := if i=0 then 7/9 else 5/9
noncomputable def buyer (i : Fin 2) : PrimaryCRRA.Household (Fin 2) where
  cash := if i=0 then 16 else 20
  gamma := 1
  income := fun _ => 1
  eta := fun _ => 1
  weight := fun s => (if s=0 then 9/10 else 1/10)*beta i
  output := output
  cash_pos := by split_ifs <;> norm_num
  gamma_pos := by norm_num
  income_pos := by intro s; norm_num
  eta_pos := by intro s; norm_num
  weight_nonneg := by intro s; fin_cases s <;> fin_cases i <;> norm_num [beta]
  output_nonneg := by intro s; fin_cases s <;> norm_num [output]

noncomputable def economy : PrimaryCRRAFormation.Economy (Fin 2) (Fin 2) :=
  ⟨buyer,output,(by intro s; fin_cases s <;> norm_num [output]),fun _ _ => rfl⟩
def plan : VoluntaryPrimaryMarket.Plan := ⟨6,7,5,0,by decide,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem fixture_risky : output 0 = 2 ∧ output 1 = 0 := by norm_num [output]
theorem buyer_kkt (i : Fin 2) : PrimaryCRRA.KKT (buyer i) 2 3 := by
  fin_cases i <;>
    norm_num [PrimaryCRRA.KKT,PrimaryCRRA.Feasible,PrimaryCRRA.score,
      PrimaryCRRA.current,PrimaryCRRA.marginal,PrimaryCRRA.future,buyer,
      Fin.sum_univ_two,output,beta,Real.rpow_neg_one]

theorem unique_optimal_choice (i : Fin 2) (a : ℝ)
    (ha : PrimaryCRRA.Feasible (buyer i) 2 a) (hne : a ≠ 3) :
    PrimaryCRRA.value (buyer i) 2 a < PrimaryCRRA.value (buyer i) 2 3 :=
  PrimaryCRRA.kkt_unique_optimum (buyer i) (by norm_num) (buyer_kkt i) ha hne

theorem actual_formation : PrimaryCRRAFormation.Equilibrium plan economy 2 (fun _ => 3) := by
  refine ⟨by norm_num,fun i => (buyer_kkt i).1,?_,?_,?_,?_⟩
  · intro i a ha
    exact PrimaryCRRA.kkt_globally_optimal (buyer i) (buyer_kkt i) ha
  · norm_num [VoluntaryPrimaryMarket.supply,plan,Fin.sum_univ_two]
  · norm_num [plan,VoluntaryPrimaryMarket.supply]
  · intro enter
    cases enter <;> norm_num [VoluntaryPrimaryMarket.issuerUtility,
      VoluntaryPrimaryMarket.constructionQuote,VoluntaryPrimaryMarket.supply,plan]

theorem formation_unique {q : ℝ} {a : Fin 2 → ℝ}
    (h : PrimaryCRRAFormation.Equilibrium plan economy q a) :
    q=2 ∧ a=(fun _ => 3) :=
  PrimaryCRRAFormation.actual_formation_unique plan economy h actual_formation

theorem voluntary_participation (i : Fin 2) :
    PrimaryCRRA.value (buyer i) 2 0 ≤ PrimaryCRRA.value (buyer i) 2 3 :=
  PrimaryCRRAFormation.actual_subscriber_participation plan economy actual_formation i

def terms : IntegerEscrow.Terms (Fin 6) :=
  ⟨2,by decide,6,by decide,7,5,10,20,by decide,0,1,2,3⟩
def cash (a : Fin 6) : ℕ := if a=4 then 16 else if a=5 then 20 else 0
def genesis : EscrowSnapshot.Snapshot 6 := ⟨739,0,100,8,terms,cash,IntegerEscrow.initial cash⟩
def yes : Fin 6 → ℕ → ℕ → Bool := fun _ _ _ => true
def requests : List (AtomicEscrow.Request 6) :=
  [⟨10,0,.subscribe 1 4 3 100⟩,⟨11,1,.subscribe 1 5 3 101⟩,
   ⟨12,2,.close 0⟩,⟨13,3,.approve 2 Finset.univ⟩,⟨14,4,.release 1⟩]
def completed : AtomicEscrow.Store 6 :=
  AtomicEscrow.run (EscrowSnapshot.context genesis) yes yes ⟨genesis,[]⟩ requests
def buyerActor (i : Fin 2) : Fin 6 := if i=0 then 4 else 5

theorem final_numbers :
    completed.current.revision=5 ∧ completed.journal.length=5 ∧
    completed.current.state.phase=PrimaryEscrow.Phase.released ∧
    completed.current.state.funds.wallet 4=10 ∧ completed.current.state.funds.wallet 5=14 ∧
    completed.current.state.funds.units 4=3 ∧ completed.current.state.funds.units 5=3 ∧
    completed.current.state.funds.escrow=0 ∧ completed.current.state.funds.operating=5 ∧
    completed.current.state.funds.builderPaid=7 := by decide

theorem all_entries_admitted : ∀ e ∈ completed.journal, e.accepted=true := by decide
theorem subscribed_units_match (i : Fin 2) : completed.current.state.funds.units (buyerActor i)=3 := by
  fin_cases i
  · simpa [buyerActor] using final_numbers.2.2.2.2.2.1
  · simpa [buyerActor] using final_numbers.2.2.2.2.2.2.1

theorem current_consumption_matches (i : Fin 2) :
    (completed.current.state.funds.wallet (buyerActor i) : ℝ)=PrimaryCRRA.current (buyer i) 2 3 := by
  fin_cases i
  · norm_num [buyerActor,PrimaryCRRA.current,buyer,final_numbers.2.2.2.1]
  · norm_num [buyerActor,PrimaryCRRA.current,buyer,final_numbers.2.2.2.2.1]

noncomputable def ledgerValue (i : Fin 2) : ℝ :=
  OwnershipCRRA.utility (buyer i).gamma (completed.current.state.funds.wallet (buyerActor i) : ℝ)+
    ∑ s, (buyer i).weight s*OwnershipCRRA.utility ((buyer i).eta s)
      ((buyer i).income s+(completed.current.state.funds.units (buyerActor i) : ℝ)*output s)

theorem ledger_value_matches (i : Fin 2) : ledgerValue i=PrimaryCRRA.value (buyer i) 2 3 := by
  unfold ledgerValue PrimaryCRRA.value PrimaryCRRA.future
  rw [current_consumption_matches,subscribed_units_match]
  rfl

theorem persistent_target_is_actual_optimum (i : Fin 2) (a : ℝ)
    (ha : PrimaryCRRA.Feasible (buyer i) 2 a) : PrimaryCRRA.value (buyer i) 2 a ≤ ledgerValue i := by
  rw [ledger_value_matches]
  exact actual_formation.optimal i a ha

noncomputable def flows (s : Fin 2) : List ℝ := if s=0 then [-5,12] else [-5,0]
theorem dated_buffer_exact (s : Fin 2) : FormationLedgerCore.bufferNeeded (flows s)=5 := by
  fin_cases s <;> norm_num [flows,FormationLedgerCore.bufferNeeded]
theorem operating_affordable (s : Fin 2) :
    FormationLedgerCore.CashSafe (completed.current.state.funds.operating : ℝ) (flows s) := by
  rw [FormationLedgerCore.safe_iff_buffer,dated_buffer_exact,final_numbers.2.2.2.2.2.2.2.2.1]
  norm_num
theorem terminal_receipts_match (s : Fin 2) :
    FormationLedgerCore.cashAfter (completed.current.state.funds.operating : ℝ) (flows s)=6*output s := by
  rw [final_numbers.2.2.2.2.2.2.2.2.1]
  fin_cases s <;> norm_num [flows,output,FormationLedgerCore.cashAfter]

theorem complete_wire_roundtrip :
    PersistentWire.readStore 6 (PersistentWire.storeWire completed)=some completed :=
  PersistentWire.readStore_wire completed

theorem history_replays : PersistentWire.replayStore genesis yes yes completed=completed := by rfl
theorem complete_history_recovers :
    PersistentWire.recover genesis yes yes (PersistentWire.storeWire completed)=some completed := by
  simp [PersistentWire.recover,PersistentWire.readStore_wire,history_replays]

end ConnectedEnterpriseDemo

#print axioms ConnectedEnterpriseDemo.fixture_risky
#print axioms ConnectedEnterpriseDemo.buyer_kkt
#print axioms ConnectedEnterpriseDemo.unique_optimal_choice
#print axioms ConnectedEnterpriseDemo.actual_formation
#print axioms ConnectedEnterpriseDemo.formation_unique
#print axioms ConnectedEnterpriseDemo.voluntary_participation
#print axioms ConnectedEnterpriseDemo.final_numbers
#print axioms ConnectedEnterpriseDemo.all_entries_admitted
#print axioms ConnectedEnterpriseDemo.subscribed_units_match
#print axioms ConnectedEnterpriseDemo.current_consumption_matches
#print axioms ConnectedEnterpriseDemo.ledger_value_matches
#print axioms ConnectedEnterpriseDemo.persistent_target_is_actual_optimum
#print axioms ConnectedEnterpriseDemo.dated_buffer_exact
#print axioms ConnectedEnterpriseDemo.operating_affordable
#print axioms ConnectedEnterpriseDemo.terminal_receipts_match
#print axioms ConnectedEnterpriseDemo.complete_wire_roundtrip
#print axioms ConnectedEnterpriseDemo.history_replays
#print axioms ConnectedEnterpriseDemo.complete_history_recovers
