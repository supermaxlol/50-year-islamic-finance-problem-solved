import IntegerEscrowRefinement

/-! One executable dispatcher; the admitted branch is proved against the
accepted integer relation. External check soundness and storage stay explicit. -/
open scoped BigOperators

namespace EscrowDispatcher
open IntegerEscrow PrimaryEscrow

inductive Event (A : Type*) where
  | subscribe (actor account : A) (quantity receipt : ℕ)
  | close (actor : A)
  | release (actor : A)
  | cancel (actor : A)
  | refund (actor account : A)
  | approve (actor : A) (gates : Finset Gate)
  | revoke (actor : A) (gate : Gate)
  | pause (actor : A) (action : Action)
  | resolve (actor : A) (action : Action)
  | tick (time : ℕ)

structure Result (A : Type*) where
  accepted : Bool
  state : IntegerEscrow.State A

variable {A : Type*} [Fintype A] [DecidableEq A]

def Guard (T : IntegerEscrow.Terms A) (consentCheck settlementCheck : A → ℕ → ℕ → Bool)
    (s : IntegerEscrow.State A) : Event A → Prop
  | .subscribe actor a n r => actor = T.custodian ∧ s.phase = .collecting ∧
      0 < n ∧ IntegerEscrow.totalUnits s+n ≤ T.cap ∧ T.price*n ≤ s.funds.wallet a ∧
      r ∉ s.receipts ∧ s.now ≤ T.subscribeDeadline ∧ .subscriptions ∉ s.paused ∧
      consentCheck a n r = true ∧ settlementCheck a n r = true
  | .close actor => actor = T.issuer ∧ s.phase = .collecting ∧
      IntegerEscrow.totalUnits s = T.cap ∧ T.construction+T.reserve ≤ s.funds.escrow ∧
      s.now ≤ T.subscribeDeadline ∧ .funding ∉ s.paused
  | .release actor => actor = T.custodian ∧ s.phase = .funded ∧ Finset.univ ⊆ s.approved ∧
      s.now ≤ T.releaseDeadline ∧ .release ∉ s.paused ∧ T.construction ≤ s.funds.escrow
  | .cancel actor => (s.phase = .collecting ∨ s.phase = .funded) ∧
      (actor = T.issuer ∨ (actor = T.custodian ∧
        ((s.phase = .collecting ∧ T.subscribeDeadline < s.now) ∨
         (s.phase = .funded ∧ T.releaseDeadline < s.now))))
  | .refund actor a => actor = T.custodian ∧ s.phase = .cancelled ∧
      0 < s.funds.units a ∧ T.price*s.funds.units a ≤ s.funds.escrow
  | .approve actor _ => actor = T.verifier
  | .revoke actor _ => actor = T.verifier
  | .pause actor _ => actor = T.verifier
  | .resolve actor _ => actor = T.resolver
  | .tick time => s.now ≤ time

instance guardDecidable (T : IntegerEscrow.Terms A)
    (cc sc : A → ℕ → ℕ → Bool) (s : IntegerEscrow.State A) (e : Event A) :
    Decidable (Guard T cc sc s e) := by
  cases e <;> dsimp only [Guard] <;> infer_instance

omit [Fintype A] in
def evolve (T : IntegerEscrow.Terms A) (s : IntegerEscrow.State A) : Event A → IntegerEscrow.State A
  | .subscribe _ a n r => IntegerEscrow.settle T s a n r
  | .close _ => IntegerEscrow.fund s
  | .release _ => IntegerEscrow.release T s
  | .cancel _ => IntegerEscrow.cancel s
  | .refund _ a => IntegerEscrow.refund T s a
  | .approve _ gates => IntegerEscrow.attest s gates
  | .revoke _ gate => IntegerEscrow.revoke s gate
  | .pause _ action => IntegerEscrow.pause s action
  | .resolve _ action => IntegerEscrow.resolve s action
  | .tick time => IntegerEscrow.tick s time

def dispatch (T : IntegerEscrow.Terms A) (cc sc : A → ℕ → ℕ → Bool)
    (s : IntegerEscrow.State A) (e : Event A) : Result A :=
  if Guard T cc sc s e then ⟨true,evolve T s e⟩ else ⟨false,s⟩

def run (T : IntegerEscrow.Terms A) (cc sc : A → ℕ → ℕ → Bool)
    (s : IntegerEscrow.State A) : List (Event A) → IntegerEscrow.State A
  | [] => s
  | e :: events => run T cc sc (dispatch T cc sc s e).state events

theorem guarded_step (T : IntegerEscrow.Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (s : IntegerEscrow.State A) (e : Event A) (h : Guard T cc sc s e) :
    IntegerEscrow.Step T consent settled s (evolve T s e) := by
  cases e with
  | subscribe actor a n r =>
    rcases h with ⟨role,hp,hn,hcap,hcash,hfresh,ht,hu,hc',hs'⟩
    exact IntegerEscrow.Step.subscribe s actor a n r role hp hn hcap hcash hfresh ht hu
      (hc a n r hc') (hs a n r hs')
  | close actor =>
    rcases h with ⟨role,hp,hfull,hbudget,ht,hu⟩
    exact IntegerEscrow.Step.close s actor role hp hfull hbudget ht hu
  | release actor =>
    rcases h with ⟨role,hp,he,ht,hu,hcash⟩
    exact IntegerEscrow.Step.payConstruction s actor role hp he ht hu hcash
  | cancel actor => exact IntegerEscrow.Step.abort s actor h.1 h.2
  | refund actor a => exact IntegerEscrow.Step.returnCash s actor a h.1 h.2.1 h.2.2.1 h.2.2.2
  | approve actor gates => exact IntegerEscrow.Step.approve s actor gates h
  | revoke actor gate => exact IntegerEscrow.Step.withdrawApproval s actor gate h
  | pause actor action => exact IntegerEscrow.Step.dispute s actor action h
  | resolve actor action => exact IntegerEscrow.Step.resolveDispute s actor action h
  | tick time => exact IntegerEscrow.Step.advanceTime s time h

theorem accepted_iff_guard (T : IntegerEscrow.Terms A) (cc sc : A → ℕ → ℕ → Bool)
    (s : IntegerEscrow.State A) (e : Event A) :
    (dispatch T cc sc s e).accepted = true ↔ Guard T cc sc s e := by
  by_cases h : Guard T cc sc s e <;> simp [dispatch,h]

theorem accepted_sound (T : IntegerEscrow.Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (s : IntegerEscrow.State A) (e : Event A) (ha : (dispatch T cc sc s e).accepted = true) :
    IntegerEscrow.Step T consent settled s (dispatch T cc sc s e).state := by
  have hg := (accepted_iff_guard T cc sc s e).mp ha
  simpa only [dispatch,ite_eq_left hg] using guarded_step T consent settled cc sc hc hs s e hg

theorem rejected_unchanged (T : IntegerEscrow.Terms A) (cc sc : A → ℕ → ℕ → Bool)
    (s : IntegerEscrow.State A) (e : Event A) (hr : (dispatch T cc sc s e).accepted = false) :
    (dispatch T cc sc s e).state = s := by
  by_cases hg : Guard T cc sc s e
  · simp [dispatch,hg] at hr
  · simp [dispatch,hg]

theorem step_or_same (T : IntegerEscrow.Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (s : IntegerEscrow.State A) (e : Event A) :
    IntegerEscrow.Step T consent settled s (dispatch T cc sc s e).state ∨
      (dispatch T cc sc s e).state = s := by
  by_cases hg : Guard T cc sc s e
  · left
    simpa only [dispatch,ite_eq_left hg] using guarded_step T consent settled cc sc hc hs s e hg
  · right
    simp [dispatch,hg]

theorem run_reachable (T : IntegerEscrow.Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (cash : A → ℕ) (s : IntegerEscrow.State A) (events : List (Event A))
    (hr : IntegerEscrow.Reachable T consent settled cash s) :
    IntegerEscrow.Reachable T consent settled cash (run T cc sc s events) := by
  induction events generalizing s with
  | nil => exact hr
  | cons e events ih =>
    change IntegerEscrow.Reachable T consent settled cash (run T cc sc (dispatch T cc sc s e).state events)
    apply ih
    rcases step_or_same T consent settled cc sc hc hs s e with h | h
    · exact IntegerEscrow.Reachable.next hr h
    · rw [h]
      exact hr

theorem run_initial_valid {delta : ℝ} (hd : 0 < delta) (T : IntegerEscrow.Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (cash : A → ℕ) (events : List (Event A)) :
    PrimaryEscrow.Valid (decodeTerms delta hd T) (moneyMap delta cash)
      (decode delta (run T cc sc (IntegerEscrow.initial cash) events)) :=
  IntegerEscrow.reachable_valid hd T consent settled cash _
    (run_reachable T consent settled cc sc hc hs cash _ events IntegerEscrow.Reachable.start)

theorem run_cash_conservation (T : IntegerEscrow.Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (cash : A → ℕ) (events : List (Event A)) :
    let s := run T cc sc (IntegerEscrow.initial cash) events
    (∑ a, s.funds.wallet a)+s.funds.escrow+s.funds.operating+s.funds.builderPaid = ∑ a, cash a := by
  exact IntegerEscrow.total_cash_conservation (show (0 : ℝ) < 1 from zero_lt_one)
    T consent settled cash _
    (run_reachable T consent settled cc sc hc hs cash _ events IntegerEscrow.Reachable.start)

theorem dispatch_receipts_monotone (T : IntegerEscrow.Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (s : IntegerEscrow.State A) (e : Event A) : s.receipts ⊆ (dispatch T cc sc s e).state.receipts := by
  rcases step_or_same T consent settled cc sc hc hs s e with h | h
  · have href := IntegerEscrow.step_refines (show (0 : ℝ) < 1 from zero_lt_one) T consent settled _ _ h
    exact PrimaryEscrow.receipts_monotone _ consent settled _ _ href
  · rw [h]

theorem run_receipts_monotone (T : IntegerEscrow.Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cc sc : A → ℕ → ℕ → Bool)
    (hc : ∀ a n r, cc a n r = true → consent a n r)
    (hs : ∀ a n r, sc a n r = true → settled a n r)
    (s : IntegerEscrow.State A) (events : List (Event A)) : s.receipts ⊆ (run T cc sc s events).receipts := by
  induction events generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons e events ih =>
    exact Finset.Subset.trans (dispatch_receipts_monotone T consent settled cc sc hc hs s e)
      (ih (dispatch T cc sc s e).state)

end EscrowDispatcher

#print axioms EscrowDispatcher.guarded_step
#print axioms EscrowDispatcher.accepted_iff_guard
#print axioms EscrowDispatcher.accepted_sound
#print axioms EscrowDispatcher.rejected_unchanged
#print axioms EscrowDispatcher.step_or_same
#print axioms EscrowDispatcher.run_reachable
#print axioms EscrowDispatcher.run_initial_valid
#print axioms EscrowDispatcher.run_cash_conservation
#print axioms EscrowDispatcher.dispatch_receipts_monotone
#print axioms EscrowDispatcher.run_receipts_monotone
