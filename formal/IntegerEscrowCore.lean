import EscrowFundingBridge

/-! Exact minor-unit escrow arithmetic. No rounding, signed-cash coercion or
unguarded natural subtraction is identified with real subtraction. -/
open scoped BigOperators

namespace IntegerEscrow
open PrimaryEscrow FormationLedgerCore

def amount (delta : ℝ) (n : ℕ) : ℝ := delta*(n : ℝ)
def moneyMap {A : Type*} (delta : ℝ) (cash : A → ℕ) : A → ℝ := fun a => amount delta (cash a)

theorem amount_nonnegative {delta : ℝ} (hd : 0 ≤ delta) (n : ℕ) : 0 ≤ amount delta n :=
  mul_nonneg hd (Nat.cast_nonneg n)

theorem amount_add (delta : ℝ) (m n : ℕ) : amount delta (m+n) = amount delta m+amount delta n := by
  simp only [amount,Nat.cast_add,mul_add]

theorem amount_mul (delta : ℝ) (p n : ℕ) : amount delta (p*n) = amount delta p*(n : ℝ) := by
  simp only [amount,Nat.cast_mul,mul_assoc]

theorem amount_sub (delta : ℝ) {m n : ℕ} (hn : n ≤ m) :
    amount delta (m-n) = amount delta m-amount delta n := by
  simp only [amount,Nat.cast_sub hn,mul_sub]

theorem amount_le_iff {delta : ℝ} (hd : 0 < delta) (m n : ℕ) :
    amount delta m ≤ amount delta n ↔ m ≤ n := by
  unfold amount
  constructor
  · intro h
    by_contra hn
    have hnm : (n : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_not_ge hn)
    exact not_lt_of_ge h (mul_lt_mul_of_pos_left hnm hd)
  · intro h
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) hd.le

structure Terms (A : Type*) where
  price : ℕ
  price_pos : 0 < price
  cap : ℕ
  cap_pos : 0 < cap
  construction : ℕ
  reserve : ℕ
  subscribeDeadline : ℕ
  releaseDeadline : ℕ
  deadline_order : subscribeDeadline ≤ releaseDeadline
  issuer : A
  custodian : A
  verifier : A
  resolver : A

structure Accounts (A : Type*) where
  wallet : A → ℕ
  units : A → ℕ
  escrow : ℕ
  operating : ℕ
  builderPaid : ℕ

structure State (A : Type*) where
  funds : Accounts A
  phase : Phase
  approved : Finset Gate
  releaseEvidence : Finset Gate
  releaseTime : ℕ
  paused : Finset Action
  receipts : Finset ℕ
  now : ℕ

def totalUnits {A : Type*} [Fintype A] (s : State A) : ℕ := ∑ a, s.funds.units a

def decodeTerms {A : Type*} (delta : ℝ) (hd : 0 < delta) (T : Terms A) : PrimaryEscrow.Terms A where
  price := amount delta T.price
  price_pos := mul_pos hd (by exact_mod_cast T.price_pos)
  cap := T.cap
  cap_pos := T.cap_pos
  construction := amount delta T.construction
  construction_nonneg := amount_nonnegative hd.le _
  reserve := amount delta T.reserve
  reserve_nonneg := amount_nonnegative hd.le _
  subscribeDeadline := T.subscribeDeadline
  releaseDeadline := T.releaseDeadline
  deadline_order := T.deadline_order
  issuer := T.issuer
  custodian := T.custodian
  verifier := T.verifier
  resolver := T.resolver

def decodeAccounts {A : Type*} (delta : ℝ) (f : Accounts A) : PrimaryEscrow.Accounts A :=
  ⟨moneyMap delta f.wallet,f.units,amount delta f.escrow,amount delta f.operating,amount delta f.builderPaid⟩

def decode {A : Type*} (delta : ℝ) (s : State A) : PrimaryEscrow.State A :=
  ⟨decodeAccounts delta s.funds,s.phase,s.approved,s.releaseEvidence,s.releaseTime,s.paused,s.receipts,s.now⟩

def initial {A : Type*} (cash : A → ℕ) : State A :=
  ⟨⟨cash,fun _ => 0,0,0,0⟩,.collecting,∅,∅,0,∅,∅,0⟩

def settle {A : Type*} [DecidableEq A] (T : Terms A) (s : State A) (a : A) (n r : ℕ) : State A :=
  {s with
    funds := {s.funds with
    wallet := natDebit s.funds.wallet a (T.price*n)
    units := natCredit s.funds.units a n
    escrow := s.funds.escrow+T.price*n}
    receipts := insert r s.receipts}

def fund {A : Type*} (s : State A) : State A := {s with phase := .funded}
def release {A : Type*} (T : Terms A) (s : State A) : State A :=
  {s with
    phase := .released
    funds := {s.funds with escrow := 0,operating := s.funds.escrow-T.construction,builderPaid := T.construction}
    releaseEvidence := s.approved
    releaseTime := s.now}
def cancel {A : Type*} (s : State A) : State A := {s with phase := .cancelled}
def refund {A : Type*} [DecidableEq A] (T : Terms A) (s : State A) (a : A) : State A :=
  {s with funds := {s.funds with
    wallet := natCredit s.funds.wallet a (T.price*s.funds.units a)
    units := natDebit s.funds.units a (s.funds.units a)
    escrow := s.funds.escrow-T.price*s.funds.units a}}
def attest {A : Type*} (s : State A) (gates : Finset Gate) : State A :=
  {s with approved := s.approved ∪ gates}
def revoke {A : Type*} (s : State A) (gate : Gate) : State A := {s with approved := s.approved.erase gate}
def pause {A : Type*} (s : State A) (action : Action) : State A := {s with paused := insert action s.paused}
def resolve {A : Type*} (s : State A) (action : Action) : State A := {s with paused := s.paused.erase action}
def tick {A : Type*} (s : State A) (time : ℕ) : State A := {s with now := time}
def activeUnits {A : Type*} (s : State A) (a : A) : ℕ :=
  if s.phase = .released then s.funds.units a else 0

theorem moneyMap_credit {A : Type*} [DecidableEq A] (delta : ℝ)
    (f : A → ℕ) (a : A) (n : ℕ) :
    moneyMap delta (natCredit f a n) = cashAdd (moneyMap delta f) a (amount delta n) := by
  funext i
  by_cases hi : i = a
  · subst i
    simp only [moneyMap,natCredit,cashAdd,ite_true,amount_add]
  · simp [moneyMap,natCredit,cashAdd,hi,amount]

theorem moneyMap_debit {A : Type*} [DecidableEq A] (delta : ℝ)
    (f : A → ℕ) (a : A) (n : ℕ) (hn : n ≤ f a) :
    moneyMap delta (natDebit f a n) = cashAdd (moneyMap delta f) a (-(amount delta n)) := by
  funext i
  by_cases hi : i = a
  · subst i
    simp only [moneyMap,natDebit,cashAdd,ite_true,amount_sub delta hn]
    ring
  · simp [moneyMap,natDebit,cashAdd,hi]

theorem decode_initial {A : Type*} (delta : ℝ) (cash : A → ℕ) :
    decode delta (initial cash) = PrimaryEscrow.initial (moneyMap delta cash) := by
  simp [decode,decodeAccounts,initial,PrimaryEscrow.initial,amount]

theorem decode_total {A : Type*} [Fintype A] (delta : ℝ) (s : State A) :
    PrimaryEscrow.totalUnits (decode delta s).funds = totalUnits s := rfl

theorem decode_settle {A : Type*} [DecidableEq A] (delta : ℝ) (hd : 0 < delta)
    (T : Terms A) (s : State A) (a : A) (n r : ℕ) (hc : T.price*n ≤ s.funds.wallet a) :
    decode delta (settle T s a n r) =
      PrimaryEscrow.settle (decodeTerms delta hd T) (decode delta s) a n r := by
  simp only [decode,decodeAccounts,settle,PrimaryEscrow.settle,decodeTerms,
    moneyMap_debit delta _ a _ hc,amount_add,amount_mul]

theorem decode_release {A : Type*} (delta : ℝ) (hd : 0 < delta)
    (T : Terms A) (s : State A) (hc : T.construction ≤ s.funds.escrow) :
    decode delta (release T s) = PrimaryEscrow.release (decodeTerms delta hd T) (decode delta s) := by
  have hz : amount delta 0 = 0 := by simp [amount]
  simp only [decode,decodeAccounts,release,PrimaryEscrow.release,decodeTerms,amount_sub delta hc,hz]

theorem decode_refund {A : Type*} [DecidableEq A] (delta : ℝ) (hd : 0 < delta)
    (T : Terms A) (s : State A) (a : A) (hc : T.price*s.funds.units a ≤ s.funds.escrow) :
    decode delta (refund T s a) = PrimaryEscrow.refund (decodeTerms delta hd T) (decode delta s) a := by
  simp only [decode,decodeAccounts,refund,PrimaryEscrow.refund,decodeTerms,
    moneyMap_credit,amount_sub delta hc,amount_mul]

theorem decode_governance {A : Type*} (delta : ℝ) (s : State A)
    (gates : Finset Gate) (gate : Gate) (action : Action) (time : ℕ) :
    decode delta (fund s) = PrimaryEscrow.fund (decode delta s) ∧
      decode delta (cancel s) = PrimaryEscrow.cancel (decode delta s) ∧
      decode delta (attest s gates) = PrimaryEscrow.attest (decode delta s) gates ∧
      decode delta (revoke s gate) = PrimaryEscrow.revoke (decode delta s) gate ∧
      decode delta (pause s action) = PrimaryEscrow.pause (decode delta s) action ∧
      decode delta (resolve s action) = PrimaryEscrow.resolve (decode delta s) action ∧
      decode delta (tick s time) = PrimaryEscrow.tick (decode delta s) time :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem decode_active {A : Type*} (delta : ℝ) (s : State A) (a : A) :
    PrimaryEscrow.activeUnits (decode delta s) a = activeUnits s a := rfl

end IntegerEscrow

#print axioms IntegerEscrow.amount_nonnegative
#print axioms IntegerEscrow.amount_add
#print axioms IntegerEscrow.amount_mul
#print axioms IntegerEscrow.amount_sub
#print axioms IntegerEscrow.amount_le_iff
#print axioms IntegerEscrow.moneyMap_credit
#print axioms IntegerEscrow.moneyMap_debit
#print axioms IntegerEscrow.decode_initial
#print axioms IntegerEscrow.decode_total
#print axioms IntegerEscrow.decode_settle
#print axioms IntegerEscrow.decode_release
#print axioms IntegerEscrow.decode_refund
#print axioms IntegerEscrow.decode_governance
#print axioms IntegerEscrow.decode_active
