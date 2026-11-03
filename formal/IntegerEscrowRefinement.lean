import IntegerEscrowCore
import CRRALotsExecution

/-! Forward simulation of every admitted minor-unit transition, including
refund and governance. Persistence and an external payment adapter are separate. -/
noncomputable section
open scoped BigOperators

namespace IntegerEscrow

theorem amount_eq_iff {delta : ℝ} (hd : 0 < delta) (m n : ℕ) :
    amount delta m = amount delta n ↔ m = n := by
  constructor
  · intro h
    exact le_antisymm ((amount_le_iff hd m n).mp h.le) ((amount_le_iff hd n m).mp h.ge)
  · intro h
    rw [h]

section Histories
variable {A : Type*} [Fintype A] [DecidableEq A]

inductive Step (T : Terms A) (consent settled : A → ℕ → ℕ → Prop) : State A → State A → Prop
  | subscribe (s) (actor a : A) (n r : ℕ)
      (role : actor = T.custodian) (collecting : s.phase = .collecting)
      (positive : 0 < n) (cap : totalUnits s+n ≤ T.cap)
      (cash : T.price*n ≤ s.funds.wallet a) (fresh : r ∉ s.receipts)
      (time : s.now ≤ T.subscribeDeadline) (unpaused : .subscriptions ∉ s.paused)
      (authorized : consent a n r) (settlement : settled a n r) :
      Step T consent settled s (settle T s a n r)
  | close (s) (actor : A) (role : actor = T.issuer)
      (collecting : s.phase = .collecting) (full : totalUnits s = T.cap)
      (budget : T.construction+T.reserve ≤ s.funds.escrow)
      (time : s.now ≤ T.subscribeDeadline) (unpaused : .funding ∉ s.paused) :
      Step T consent settled s (fund s)
  | payConstruction (s) (actor : A) (role : actor = T.custodian)
      (funded : s.phase = .funded) (evidence : Finset.univ ⊆ s.approved)
      (time : s.now ≤ T.releaseDeadline) (unpaused : .release ∉ s.paused)
      (cash : T.construction ≤ s.funds.escrow) : Step T consent settled s (release T s)
  | abort (s) (actor : A) (open_ : s.phase = .collecting ∨ s.phase = .funded)
      (role : actor = T.issuer ∨ (actor = T.custodian ∧
        ((s.phase = .collecting ∧ T.subscribeDeadline < s.now) ∨
         (s.phase = .funded ∧ T.releaseDeadline < s.now)))) : Step T consent settled s (cancel s)
  | returnCash (s) (actor a : A) (role : actor = T.custodian)
      (cancelled : s.phase = .cancelled) (positive : 0 < s.funds.units a)
      (cash : T.price*s.funds.units a ≤ s.funds.escrow) : Step T consent settled s (refund T s a)
  | approve (s) (actor : A) (gates : Finset PrimaryEscrow.Gate) (role : actor = T.verifier) :
      Step T consent settled s (attest s gates)
  | withdrawApproval (s) (actor : A) (gate : PrimaryEscrow.Gate) (role : actor = T.verifier) :
      Step T consent settled s (revoke s gate)
  | dispute (s) (actor : A) (action : PrimaryEscrow.Action) (role : actor = T.verifier) :
      Step T consent settled s (pause s action)
  | resolveDispute (s) (actor : A) (action : PrimaryEscrow.Action) (role : actor = T.resolver) :
      Step T consent settled s (resolve s action)
  | advanceTime (s) (time : ℕ) (monotone : s.now ≤ time) : Step T consent settled s (tick s time)

theorem step_refines {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (s t : State A) (hs : Step T consent settled s t) :
    PrimaryEscrow.Step (decodeTerms delta hd T) consent settled (decode delta s) (decode delta t) := by
  cases hs with
  | subscribe actor a n r role hp hn hcap hcash hf ht hu hc he =>
    rw [decode_settle delta hd T s a n r hcash]
    apply PrimaryEscrow.Step.subscribe (T := decodeTerms delta hd T) (decode delta s) actor a n r role hp hn hcap
    · change amount delta T.price*(n : ℝ) ≤ amount delta (s.funds.wallet a)
      rw [← amount_mul]
      exact (amount_le_iff hd _ _).mpr hcash
    · exact hf
    · exact ht
    · exact hu
    · exact hc
    · exact he
  | close actor role hp hf hb ht hu =>
    apply PrimaryEscrow.Step.close (T := decodeTerms delta hd T) (decode delta s) actor role hp hf
    · change amount delta T.construction+amount delta T.reserve ≤ amount delta s.funds.escrow
      rw [← amount_add]
      exact (amount_le_iff hd _ _).mpr hb
    · exact ht
    · exact hu
  | payConstruction actor role hp he ht hu hc =>
    rw [decode_release delta hd T s hc]
    exact PrimaryEscrow.Step.payConstruction (decode delta s) actor role hp he ht hu
  | abort actor hp role => exact PrimaryEscrow.Step.abort (decode delta s) actor hp role
  | returnCash actor a role hp hn hc =>
    rw [decode_refund delta hd T s a hc]
    exact PrimaryEscrow.Step.returnCash (decode delta s) actor a role hp hn
  | approve actor gates role => exact PrimaryEscrow.Step.approve (decode delta s) actor gates role
  | withdrawApproval actor gate role =>
    exact PrimaryEscrow.Step.withdrawApproval (decode delta s) actor gate role
  | dispute actor action role => exact PrimaryEscrow.Step.dispute (decode delta s) actor action role
  | resolveDispute actor action role =>
    exact PrimaryEscrow.Step.resolveDispute (decode delta s) actor action role
  | advanceTime time hm => exact PrimaryEscrow.Step.advanceTime (decode delta s) time hm

inductive Reachable (T : Terms A) (consent settled : A → ℕ → ℕ → Prop)
    (cash : A → ℕ) : State A → Prop
  | start : Reachable T consent settled cash (initial cash)
  | next {s t} (previous : Reachable T consent settled cash s)
      (transition : Step T consent settled s t) : Reachable T consent settled cash t

theorem reachable_refines {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cash : A → ℕ) (s : State A)
    (hr : Reachable T consent settled cash s) :
    PrimaryEscrow.Reachable (decodeTerms delta hd T) consent settled (moneyMap delta cash) (decode delta s) := by
  induction hr with
  | start => rw [decode_initial]; exact PrimaryEscrow.Reachable.start
  | next previous transition ih =>
    exact PrimaryEscrow.Reachable.next ih (step_refines hd T consent settled _ _ transition)

theorem reachable_valid {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cash : A → ℕ) (s : State A)
    (hr : Reachable T consent settled cash s) :
    PrimaryEscrow.Valid (decodeTerms delta hd T) (moneyMap delta cash) (decode delta s) :=
  PrimaryEscrow.reachable_valid _ consent settled (moneyMap delta cash)
    (fun a => amount_nonnegative hd.le (cash a)) (decode delta s)
    (reachable_refines hd T consent settled cash s hr)

theorem refund_affordable {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cash : A → ℕ) (s : State A) (a : A)
    (hr : Reachable T consent settled cash s) (hp : s.phase = .cancelled) :
    T.price*s.funds.units a ≤ s.funds.escrow := by
  apply (amount_le_iff hd _ _).mp
  rw [amount_mul]
  exact PrimaryEscrow.refund_affordable _ (moneyMap delta cash) (decode delta s) a
    (reachable_valid hd T consent settled cash s hr) hp

theorem release_affordable {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cash : A → ℕ) (s : State A)
    (hr : Reachable T consent settled cash s) (hp : s.phase = .funded) :
    T.construction ≤ s.funds.escrow := by
  have hv := reachable_valid hd T consent settled cash s hr
  have hh := hv.2
  simp only [decode,PrimaryEscrow.PhaseSound,hp] at hh
  apply (amount_le_iff hd _ _).mp
  have hb : amount delta T.construction+amount delta T.reserve ≤ amount delta s.funds.escrow := hh.2.2.2
  linarith [amount_nonnegative hd.le T.reserve]

omit [DecidableEq A] in
theorem amount_sum (delta : ℝ) (cash : A → ℕ) : amount delta (∑ a, cash a) = ∑ a, amount delta (cash a) := by
  simp only [amount,Nat.cast_sum,Finset.mul_sum]

theorem total_cash_conservation {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cash : A → ℕ) (s : State A)
    (hr : Reachable T consent settled cash s) :
    (∑ a, s.funds.wallet a)+s.funds.escrow+s.funds.operating+s.funds.builderPaid = ∑ a, cash a := by
  have hh := PrimaryEscrow.total_cash_conservation _ (moneyMap delta cash) (decode delta s)
    (reachable_valid hd T consent settled cash s hr)
  change (∑ a, amount delta (s.funds.wallet a))+amount delta s.funds.escrow+
    amount delta s.funds.operating+amount delta s.funds.builderPaid = ∑ a, amount delta (cash a) at hh
  apply (amount_eq_iff hd _ _).mp
  simpa only [amount_add,amount_sum] using hh

theorem released_accounting {delta : ℝ} (hd : 0 < delta) (T : Terms A)
    (consent settled : A → ℕ → ℕ → Prop) (cash : A → ℕ) (s : State A)
    (hr : Reachable T consent settled cash s) (hp : s.phase = .released) :
    s.funds.builderPaid = T.construction ∧ T.reserve ≤ s.funds.operating ∧
      s.funds.escrow = 0 ∧ totalUnits s = T.cap ∧
      Finset.univ ⊆ s.releaseEvidence ∧ s.releaseTime ≤ T.releaseDeadline := by
  have hh := PrimaryEscrow.released_construction_and_buffer _ (moneyMap delta cash) (decode delta s)
    (reachable_valid hd T consent settled cash s hr) hp
  refine ⟨(amount_eq_iff hd _ _).mp hh.1,(amount_le_iff hd _ _).mp hh.2.1,?_,
    hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2⟩
  apply (amount_eq_iff hd _ 0).mp
  have he0 : amount delta s.funds.escrow = 0 := hh.2.2.1
  simpa only [amount,Nat.cast_zero,mul_zero] using he0

end Histories

theorem represented_budget {S : Type*} (H : PrimaryCRRA.Household S)
    {delta q a : ℝ} (hd : 0 < delta) (p w n : ℕ)
    (hq : q = amount delta p) (hw : H.cash = amount delta w) (ha : a = (n : ℝ))
    (hf : PrimaryCRRA.Feasible H q a) :
    p*n ≤ w ∧ amount delta (w-p*n) = PrimaryCRRA.current H q a := by
  have hc := hf.2
  unfold PrimaryCRRA.current at hc
  have hcost : amount delta (p*n) ≤ amount delta w := by
    rw [amount_mul,← hq,← hw,← ha]
    linarith
  have hn := (amount_le_iff hd _ _).mp hcost
  refine ⟨hn,?_⟩
  rw [amount_sub delta hn,amount_mul]
  unfold PrimaryCRRA.current
  rw [hq,hw,ha]

theorem actual_equilibrium_wallets {I S : Type*} [Fintype I] [Fintype S]
    (P : VoluntaryPrimaryMarket.Plan) (E : PrimaryCRRAFormation.Economy I S)
    (q : ℝ) (a : I → ℝ) (he : PrimaryCRRAFormation.Equilibrium P E q a)
    {delta : ℝ} (hd : 0 < delta) (p : ℕ) (cash n : I → ℕ)
    (hq : q = amount delta p) (hc : ∀ i, (E.buyers i).cash = amount delta (cash i))
    (hn : ∀ i, a i = (n i : ℝ)) :
    ∀ i, p*n i ≤ cash i ∧ amount delta (cash i-p*n i) = PrimaryCRRA.current (E.buyers i) q (a i) :=
  fun i => represented_budget (E.buyers i) hd p (cash i) (n i) hq (hc i) (hn i) (he.feasible i)

end IntegerEscrow

#print axioms IntegerEscrow.amount_eq_iff
#print axioms IntegerEscrow.step_refines
#print axioms IntegerEscrow.reachable_refines
#print axioms IntegerEscrow.reachable_valid
#print axioms IntegerEscrow.refund_affordable
#print axioms IntegerEscrow.release_affordable
#print axioms IntegerEscrow.amount_sum
#print axioms IntegerEscrow.total_cash_conservation
#print axioms IntegerEscrow.released_accounting
#print axioms IntegerEscrow.represented_budget
#print axioms IntegerEscrow.actual_equilibrium_wallets
