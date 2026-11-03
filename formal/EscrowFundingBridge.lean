import PrimaryEscrow

/-! Guarded histories and bridges to the accepted dated cash-buffer and
ownership-ledger invariants. No claim of external authentication or custody. -/
noncomputable section
open scoped BigOperators

namespace PrimaryEscrow

section Histories
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Consent and settled-bank-transfer evidence are supplied under the fixed
enterprise terms. The state machine does not establish their physical truth. -/
inductive Step (T : Terms A) (consent settled : A → ℕ → ℕ → Prop) :
    State A → State A → Prop
  | subscribe (s) (actor a : A) (n r : ℕ)
      (role : actor = T.custodian) (collecting : s.phase = .collecting)
      (positive : 0 < n) (cap : totalUnits s.funds + n ≤ T.cap)
      (cash : T.price * (n : ℝ) ≤ s.funds.wallet a) (fresh : r ∉ s.receipts)
      (time : s.now ≤ T.subscribeDeadline) (unpaused : .subscriptions ∉ s.paused)
      (authorized : consent a n r) (settlement : settled a n r) :
      Step T consent settled s (settle T s a n r)
  | close (s) (actor : A) (role : actor = T.issuer)
      (collecting : s.phase = .collecting) (full : totalUnits s.funds = T.cap)
      (budget : T.construction + T.reserve ≤ s.funds.escrow)
      (time : s.now ≤ T.subscribeDeadline) (unpaused : .funding ∉ s.paused) :
      Step T consent settled s (fund s)
  | payConstruction (s) (actor : A) (role : actor = T.custodian)
      (funded : s.phase = .funded) (evidence : Finset.univ ⊆ s.approved)
      (time : s.now ≤ T.releaseDeadline) (unpaused : .release ∉ s.paused) :
      Step T consent settled s (release T s)
  | abort (s) (actor : A) (open_ : s.phase = .collecting ∨ s.phase = .funded)
      (role : actor = T.issuer ∨ (actor = T.custodian ∧
        ((s.phase = .collecting ∧ T.subscribeDeadline < s.now) ∨
         (s.phase = .funded ∧ T.releaseDeadline < s.now)))) :
      Step T consent settled s (cancel s)
  | returnCash (s) (actor a : A) (role : actor = T.custodian)
      (cancelled : s.phase = .cancelled) (positive : 0 < s.funds.units a) :
      Step T consent settled s (refund T s a)
  | approve (s) (actor : A) (gates : Finset Gate) (role : actor = T.verifier) :
      Step T consent settled s (attest s gates)
  | withdrawApproval (s) (actor : A) (gate : Gate) (role : actor = T.verifier) :
      Step T consent settled s (revoke s gate)
  | dispute (s) (actor : A) (action : Action) (role : actor = T.verifier) :
      Step T consent settled s (pause s action)
  | resolveDispute (s) (actor : A) (action : Action) (role : actor = T.resolver) :
      Step T consent settled s (resolve s action)
  | advanceTime (s) (time : ℕ) (monotone : s.now ≤ time) :
      Step T consent settled s (tick s time)

theorem step_preserves_valid (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℝ) (s t : State A) (hv : Valid T cash s)
    (hs : Step T consent settled s t) : Valid T cash t := by
  cases hs with
  | subscribe _ a n r _ hp _ hc hw _ _ _ _ _ => exact settle_valid T cash s a n r hv hp hc hw
  | close _ _ hp hf hb _ _ => exact fund_valid T cash s hv hp hf hb
  | payConstruction _ _ hp he ht _ => exact release_valid T cash s hv hp he ht
  | abort _ hp _ => exact cancel_valid T cash s hv hp
  | returnCash _ a _ hp _ => exact refund_valid T cash s a hv hp
  | approve _ _ _ => exact hv
  | withdrawApproval _ _ _ => exact hv
  | dispute _ _ _ => exact hv
  | resolveDispute _ _ _ => exact hv
  | advanceTime _ _ => exact hv

inductive Reachable (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℝ) : State A → Prop
  | start : Reachable T consent settled cash (initial cash)
  | next {s t} (previous : Reachable T consent settled cash s)
      (transition : Step T consent settled s t) : Reachable T consent settled cash t

theorem reachable_valid (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℝ) (hc : ∀ a, 0 ≤ cash a) (s : State A)
    (hr : Reachable T consent settled cash s) : Valid T cash s := by
  induction hr with
  | start => exact initial_valid T cash hc
  | next previous transition ih => exact step_preserves_valid T consent settled cash _ _ ih transition

theorem receipts_monotone (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (s t : State A) (hs : Step T consent settled s t) : s.receipts ⊆ t.receipts := by
  cases hs with
  | subscribe => exact Finset.subset_insert _ _
  | close => exact Finset.Subset.refl _
  | payConstruction => exact Finset.Subset.refl _
  | abort => exact Finset.Subset.refl _
  | returnCash => exact Finset.Subset.refl _
  | approve => exact Finset.Subset.refl _
  | withdrawApproval => exact Finset.Subset.refl _
  | dispute => exact Finset.Subset.refl _
  | resolveDispute => exact Finset.Subset.refl _
  | advanceTime => exact Finset.Subset.refl _

def CanRefund (s : State A) (a : A) : Prop := s.phase = .cancelled ∧ 0 < s.funds.units a

omit [Fintype A] in
theorem refund_not_repeatable (T : Terms A) (s : State A) (a : A) :
    ¬ CanRefund (refund T s a) a := by simp [CanRefund, refund_zeros_entitlement]

omit [Fintype A] [DecidableEq A] in
theorem disputes_do_not_block_refunds (s : State A) (a : A) (action : Action) :
    CanRefund (pause s action) a ↔ CanRefund s a := Iff.rfl

theorem refund_available_and_funded (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℝ) (s : State A) (a : A) (hv : Valid T cash s) (h : CanRefund s a) :
    Step T consent settled s (refund T s a) ∧
      T.price * (s.funds.units a : ℝ) ≤ s.funds.escrow ∧ Valid T cash (refund T s a) :=
  ⟨Step.returnCash s T.custodian a rfl h.1 h.2,
    refund_affordable T cash s a hv h.1, refund_valid T cash s a hv h.1⟩

theorem release_available (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℝ) (s : State A) (hv : Valid T cash s) (hp : s.phase = .funded)
    (he : Finset.univ ⊆ s.approved) (ht : s.now ≤ T.releaseDeadline)
    (hu : .release ∉ s.paused) :
    Step T consent settled s (release T s) ∧ Valid T cash (release T s) :=
  ⟨Step.payConstruction s T.custodian rfl hp he ht hu,
    release_valid T cash s hv hp he ht⟩

theorem funding_close_available (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℝ) (s : State A) (hv : Valid T cash s) (hp : s.phase = .collecting)
    (hf : totalUnits s.funds = T.cap) (hb : T.construction + T.reserve ≤ s.funds.escrow)
    (ht : s.now ≤ T.subscribeDeadline) (hu : .funding ∉ s.paused) :
    Step T consent settled s (fund s) ∧ Valid T cash (fund s) :=
  ⟨Step.close s T.issuer rfl hp hf hb ht hu, fund_valid T cash s hv hp hf hb⟩

theorem timeout_cancellation_available (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (s : State A) (h : (s.phase = .collecting ∧ T.subscribeDeadline < s.now) ∨
      (s.phase = .funded ∧ T.releaseDeadline < s.now)) :
    Step T consent settled s (cancel s) := by
  apply Step.abort s T.custodian
  · exact h.elim (fun x => Or.inl x.1) (fun x => Or.inr x.1)
  · exact Or.inr ⟨rfl, h⟩

end Histories

theorem released_construction_and_buffer {A : Type*} [Fintype A]
    (T : Terms A) (cash : A → ℝ) (s : State A) (hv : Valid T cash s)
    (hp : s.phase = .released) :
    s.funds.builderPaid = T.construction ∧ T.reserve ≤ s.funds.operating ∧
      s.funds.escrow = 0 ∧ totalUnits s.funds = T.cap ∧
      Finset.univ ⊆ s.releaseEvidence ∧ s.releaseTime ≤ T.releaseDeadline := by
  have hh := hv.2
  simp only [PhaseSound, hp] at hh
  exact ⟨hh.2.2.1, hh.2.2.2.2.1, hh.1, hh.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩

theorem released_all_paths_affordable {A S : Type*} [Fintype A]
    (T : Terms A) (cash : A → ℝ) (s : State A) (hv : Valid T cash s)
    (hp : s.phase = .released) (flows : S → List ℝ)
    (hb : ∀ state, FormationLedgerCore.bufferNeeded (flows state) ≤ T.reserve) :
    ∀ state, FormationLedgerCore.CashSafe s.funds.operating (flows state) := by
  have h := (released_construction_and_buffer T cash s hv hp).2.1
  intro state
  apply (FormationLedgerCore.safe_iff_buffer _ _).mpr
  exact le_trans (hb state) h

theorem released_terminal_cash_identity {A S : Type*} [Fintype A]
    (T : Terms A) (cash : A → ℝ) (s : State A) (hv : Valid T cash s)
    (hp : s.phase = .released) (flows : S → List ℝ) (state : S) :
    FormationLedgerCore.cashAfter s.funds.operating (flows state) =
      T.price * (T.cap : ℝ) - T.construction + (flows state).sum := by
  have hh := hv.2
  simp only [PhaseSound, hp] at hh
  rw [FormationLedgerCore.cash_after_identity, hh.2.2.2.1]

/-- Operating capital is NOT also inserted as distributable investor cash.
This is a fresh distribution ledger, carrying only the activated stock. -/
def certificateLedger {A R : Type*} (T : Terms A) (s : State A) (seed : A) :
    FormationLedgerCore.Ledger A R :=
  {FormationLedgerCore.initial seed with
    holdings := s.funds.units
    issued := T.cap
    closed := true}

theorem released_ledger_valid {A R : Type*} [Fintype A] [Fintype R]
    [DecidableEq A] [DecidableEq R]
    (T : Terms A) (cash : A → ℝ) (s : State A) (seed : A) (hv : Valid T cash s)
    (hp : s.phase = .released) :
    FormationLedgerCore.Valid T.cap (certificateLedger (R := R) T s seed) := by
  have hh := (released_construction_and_buffer T cash s hv hp).2.2.2.1
  constructor <;> simp [certificateLedger, FormationLedgerCore.initial,
    FormationLedgerCore.reserved, totalUnits] at *
  exact hh

theorem no_double_counted_operating_cash {A R : Type*}
    (T : Terms A) (s : State A) (seed : A) :
    (certificateLedger (R := R) T s seed).vault = 0 ∧
      (certificateLedger (R := R) T s seed).received = 0 := ⟨rfl, rfl⟩

end PrimaryEscrow

#print axioms PrimaryEscrow.step_preserves_valid
#print axioms PrimaryEscrow.reachable_valid
#print axioms PrimaryEscrow.receipts_monotone
#print axioms PrimaryEscrow.refund_not_repeatable
#print axioms PrimaryEscrow.disputes_do_not_block_refunds
#print axioms PrimaryEscrow.refund_available_and_funded
#print axioms PrimaryEscrow.release_available
#print axioms PrimaryEscrow.funding_close_available
#print axioms PrimaryEscrow.timeout_cancellation_available
#print axioms PrimaryEscrow.released_construction_and_buffer
#print axioms PrimaryEscrow.released_all_paths_affordable
#print axioms PrimaryEscrow.released_terminal_cash_identity
#print axioms PrimaryEscrow.released_ledger_valid
#print axioms PrimaryEscrow.no_double_counted_operating_cash
