import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Guarded specification, not a semantics/refinement proof of Python. -/
noncomputable section
open scoped BigOperators

namespace FormationLedgerCore

/-- Signed cash events are ordered by actual availability/due time. -/
def bufferNeeded : List ℝ → ℝ
  | [] => 0
  | x :: xs => max 0 (bufferNeeded xs - x)

def CashSafe : ℝ → List ℝ → Prop
  | b, [] => 0 ≤ b
  | b, x :: xs => 0 ≤ b ∧ CashSafe (b+x) xs

def cashAfter : ℝ → List ℝ → ℝ
  | b, [] => b
  | b, x :: xs => cashAfter (b+x) xs

theorem buffer_nonnegative (xs : List ℝ) : 0 ≤ bufferNeeded xs := by
  cases xs with
  | nil => exact le_refl 0
  | cons x xs => exact le_max_left _ _

theorem safe_iff_buffer (xs : List ℝ) (b : ℝ) :
    CashSafe b xs ↔ bufferNeeded xs ≤ b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simp only [CashSafe, bufferNeeded, max_le_iff, ih]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem safe_terminal_nonnegative (xs : List ℝ) (b : ℝ) (h : CashSafe b xs) :
    0 ≤ cashAfter b xs := by
  induction xs generalizing b with
  | nil => exact h
  | cons x xs ih => exact ih (b+x) h.2

theorem cash_after_identity (xs : List ℝ) (b : ℝ) : cashAfter b xs = b+xs.sum := by
  induction xs generalizing b with
  | nil => simp [cashAfter]
  | cons x xs ih => simp only [cashAfter, List.sum_cons, ih]; ring

/-- Settled subscriptions must pay construction AND the dated liquidity buffer. -/
theorem formation_funding_iff (subscriptions construction : ℝ) (xs : List ℝ) :
    CashSafe (subscriptions-construction) xs ↔
      construction+bufferNeeded xs ≤ subscriptions := by
  rw [safe_iff_buffer]
  constructor <;> intro h <;> linarith

theorem all_states_funding_iff {S : Type*} (subscriptions construction : ℝ)
    (flows : S → List ℝ) :
    (∀ s, CashSafe (subscriptions-construction) (flows s)) ↔
      ∀ s, construction+bufferNeeded (flows s) ≤ subscriptions := by
  simp only [formation_funding_iff]

section Updates
variable {A : Type*} [DecidableEq A]

def cashAdd (f : A → ℝ) (a : A) (v : ℝ) : A → ℝ :=
  fun i => f i + if i=a then v else 0

def natCredit (f : A → ℕ) (a : A) (n : ℕ) : A → ℕ :=
  fun i => f i + if i=a then n else 0

def natDebit (f : A → ℕ) (a : A) (n : ℕ) : A → ℕ :=
  fun i => f i - if i=a then n else 0

variable [Fintype A]

theorem sum_cashAdd (f : A → ℝ) (a : A) (v : ℝ) :
    (∑ i, cashAdd f a v i) = (∑ i, f i)+v := by
  classical
  simp [cashAdd, Finset.sum_add_distrib]

theorem sum_natCredit (f : A → ℕ) (a : A) (n : ℕ) :
    (∑ i, natCredit f a n i) = (∑ i, f i)+n := by
  classical
  simp [natCredit, Finset.sum_add_distrib]

theorem sum_natDebit (f : A → ℕ) (a : A) (n : ℕ) (hn : n ≤ f a) :
    (∑ i, natDebit f a n i)+n = ∑ i, f i := by
  have h : natCredit (natDebit f a n) a n = f := by
    funext i
    by_cases hi : i=a
    · subst i
      simp [natCredit, natDebit, Nat.sub_add_cancel hn]
    · simp [natCredit, natDebit, hi]
  have hs := congrArg (fun g : A → ℕ => ∑ i, g i) h
  simpa only [sum_natCredit] using hs

end Updates

structure Ledger (A R : Type*) where
  holdings : A → ℕ
  nonce : A → ℕ
  issued : ℕ
  claims : A → ℝ
  pending : R → ℝ
  payee : R → A
  used : Finset R
  active : Finset R
  periods : Finset ℕ
  snapshots : ℕ → A → ℕ
  vault : ℝ
  paid : ℝ
  received : ℝ
  closed : Bool
  terminal : Bool

section Ledger
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R]

def reserved (s : Ledger A R) : ℝ := (∑ i, s.claims i)+(∑ r, s.pending r)

structure Valid (cap : ℕ) (s : Ledger A R) : Prop where
  stock : (∑ i, s.holdings i) = s.issued
  cap_bound : s.issued ≤ cap
  claims_nonnegative : ∀ i, 0 ≤ s.claims i
  pending_nonnegative : ∀ r, 0 ≤ s.pending r
  funded : reserved s ≤ s.vault
  cash_conserved : s.vault+s.paid = s.received
  paid_nonnegative : 0 ≤ s.paid
  closed_full : s.closed=true → s.issued=cap
  terminal_closed : s.terminal=true → s.closed=true
  active_used : s.active ⊆ s.used
  inactive_zero : ∀ r, r ∉ s.active → s.pending r=0

def initial (seed : A) : Ledger A R :=
  ⟨fun _ => 0, fun _ => 0, 0, fun _ => 0, fun _ => 0, fun _ => seed,
    ∅, ∅, ∅, fun _ _ => 0, 0, 0, 0, false, false⟩

omit [DecidableEq A] [DecidableEq R] in
theorem initial_valid (cap : ℕ) (seed : A) : Valid cap (initial (R := R) seed) := by
  constructor <;> simp [initial, reserved]

def mint (s : Ledger A R) (a : A) (n : ℕ) : Ledger A R :=
  {s with holdings := natCredit s.holdings a n, issued := s.issued+n}

def close (s : Ledger A R) : Ledger A R := {s with closed := true}

def transfer (s : Ledger A R) (a b : A) (n : ℕ) : Ledger A R :=
  {s with
    holdings := natCredit (natDebit s.holdings a n) b n
    nonce := natCredit s.nonce a 1}

def deposit (s : Ledger A R) (x : ℝ) : Ledger A R :=
  {s with vault := s.vault+x, received := s.received+x}

/-- Payouts include explicitly allocated fees. Allocation policy is separately
certified against the snapshot; budget preservation does not prove its code. -/
def distribute (s : Ledger A R) (period : ℕ) (payout : A → ℝ)
    (last : Bool) : Ledger A R :=
  {s with
    claims := fun i => s.claims i+payout i
    periods := insert period s.periods
    snapshots := Function.update s.snapshots period s.holdings
    terminal := last}

def request (s : Ledger A R) (a : A) (r : R) (x : ℝ) : Ledger A R :=
  {s with
    claims := cashAdd s.claims a (-x)
    pending := cashAdd s.pending r x
    payee := Function.update s.payee r a
    used := insert r s.used
    active := insert r s.active
    nonce := natCredit s.nonce a 1}

def confirm (s : Ledger A R) (r : R) : Ledger A R :=
  {s with
    pending := cashAdd s.pending r (-s.pending r)
    active := s.active.erase r
    vault := s.vault-s.pending r
    paid := s.paid+s.pending r}

def cancel (s : Ledger A R) (r : R) : Ledger A R :=
  {s with
    claims := cashAdd s.claims (s.payee r) (s.pending r)
    pending := cashAdd s.pending r (-s.pending r)
    active := s.active.erase r}

omit [DecidableEq R] in
theorem mint_valid (cap : ℕ) (s : Ledger A R) (a : A) (n : ℕ)
    (hv : Valid cap s) (ho : s.closed=false) (hc : s.issued+n ≤ cap) :
    Valid cap (mint s a n) := by
  refine {hv with stock := ?_, cap_bound := hc, closed_full := ?_}
  · change (∑ i, natCredit s.holdings a n i)=s.issued+n
    rw [sum_natCredit, hv.stock]
  · intro h
    change s.closed=true at h
    simp [ho] at h

omit [DecidableEq A] [DecidableEq R] in
theorem close_valid (cap : ℕ) (s : Ledger A R) (hv : Valid cap s)
    (hc : s.issued=cap) : Valid cap (close s) := by
  exact {hv with closed_full := fun _ => hc, terminal_closed := fun _ => rfl}

omit [DecidableEq R] in
theorem transfer_valid (cap : ℕ) (s : Ledger A R) (a b : A) (n : ℕ)
    (hv : Valid cap s) (hn : n ≤ s.holdings a) :
    Valid cap (transfer s a b n) := by
  refine {hv with stock := ?_}
  change (∑ i, natCredit (natDebit s.holdings a n) b n i)=s.issued
  rw [sum_natCredit, sum_natDebit _ _ _ hn, hv.stock]

omit [DecidableEq A] [DecidableEq R] in
theorem deposit_valid (cap : ℕ) (s : Ledger A R) (x : ℝ)
    (hv : Valid cap s) (hx : 0 ≤ x) : Valid cap (deposit s x) := by
  refine {hv with funded := ?_, cash_conserved := ?_}
  · change reserved s ≤ s.vault+x
    linarith [hv.funded]
  · change (s.vault+x)+s.paid=s.received+x
    linarith [hv.cash_conserved]

omit [DecidableEq A] [DecidableEq R] in
theorem distribute_valid (cap : ℕ) (s : Ledger A R) (period : ℕ)
    (payout : A → ℝ) (last : Bool) (hv : Valid cap s)
    (hp : ∀ i, 0 ≤ payout i) (hb : reserved s+(∑ i, payout i) ≤ s.vault)
    (hc : s.closed=true) : Valid cap (distribute s period payout last) := by
  refine {hv with claims_nonnegative := ?_, funded := ?_, terminal_closed := fun _ => hc}
  · intro i
    exact add_nonneg (hv.claims_nonnegative i) (hp i)
  · change (∑ i, (s.claims i + payout i)) + (∑ r, s.pending r) ≤ s.vault
    rw [Finset.sum_add_distrib]
    unfold reserved at hb
    linarith

theorem request_valid (cap : ℕ) (s : Ledger A R) (a : A) (r : R) (x : ℝ)
    (hv : Valid cap s) (hx : 0 ≤ x) (ha : x ≤ s.claims a)
    (hr : r ∉ s.used) : Valid cap (request s a r x) := by
  have hz : s.pending r = 0 := hv.inactive_zero r (fun h => hr (hv.active_used h))
  refine {hv with
    claims_nonnegative := ?_
    pending_nonnegative := ?_
    funded := ?_
    active_used := ?_
    inactive_zero := ?_}
  · intro i
    by_cases hi : i=a
    · subst i
      change 0 ≤ cashAdd s.claims a (-x) a
      simp only [cashAdd, ite_true]
      linarith
    · simpa [request, cashAdd, hi] using hv.claims_nonnegative i
  · intro t
    by_cases ht : t=r
    · subst t
      simpa [request, cashAdd, hz] using hx
    · simpa [request, cashAdd, ht] using hv.pending_nonnegative t
  · change (∑ i, cashAdd s.claims a (-x) i)+(∑ t, cashAdd s.pending r x t) ≤ s.vault
    rw [sum_cashAdd, sum_cashAdd]
    have hf := hv.funded
    unfold reserved at hf
    linarith
  · exact Finset.insert_subset_insert r hv.active_used
  · intro t ht
    have hh : t ≠ r ∧ t ∉ s.active := by
      simpa only [request, Finset.mem_insert, not_or] using ht
    simpa [request, cashAdd, hh.1] using hv.inactive_zero t hh.2

omit [DecidableEq A] in
theorem confirm_valid (cap : ℕ) (s : Ledger A R) (r : R)
    (hv : Valid cap s) : Valid cap (confirm s r) := by
  refine {hv with
    pending_nonnegative := ?_
    funded := ?_
    cash_conserved := ?_
    paid_nonnegative := add_nonneg hv.paid_nonnegative (hv.pending_nonnegative r)
    active_used := ?_
    inactive_zero := ?_}
  · intro t
    by_cases ht : t=r
    · subst t
      simp [confirm, cashAdd]
    · simpa [confirm, cashAdd, ht] using hv.pending_nonnegative t
  · change (∑ i, s.claims i)+(∑ t, cashAdd s.pending r (-s.pending r) t) ≤ s.vault-s.pending r
    rw [sum_cashAdd]
    have hf := hv.funded
    unfold reserved at hf
    linarith
  · change (s.vault-s.pending r)+(s.paid+s.pending r)=s.received
    linarith [hv.cash_conserved]
  · exact fun _ ht => hv.active_used (Finset.mem_of_mem_erase ht)
  · intro t ht
    by_cases he : t=r
    · subst t
      simp [confirm, cashAdd]
    · have hnot : t ∉ s.active := by
        intro hin
        exact ht (Finset.mem_erase.mpr ⟨he, hin⟩)
      simpa [confirm, cashAdd, he] using hv.inactive_zero t hnot

theorem cancel_valid (cap : ℕ) (s : Ledger A R) (r : R)
    (hv : Valid cap s) : Valid cap (cancel s r) := by
  refine {hv with
    claims_nonnegative := ?_
    pending_nonnegative := ?_
    funded := ?_
    active_used := ?_
    inactive_zero := ?_}
  · intro i
    exact add_nonneg (hv.claims_nonnegative i) (by split_ifs <;> linarith [hv.pending_nonnegative r])
  · intro t
    by_cases ht : t=r
    · subst t
      simp [cancel, cashAdd]
    · simpa [cancel, cashAdd, ht] using hv.pending_nonnegative t
  · change (∑ i, cashAdd s.claims (s.payee r) (s.pending r) i)+
      (∑ t, cashAdd s.pending r (-s.pending r) t) ≤ s.vault
    rw [sum_cashAdd, sum_cashAdd]
    have hf := hv.funded
    unfold reserved at hf
    linarith
  · exact fun _ ht => hv.active_used (Finset.mem_of_mem_erase ht)
  · intro t ht
    by_cases he : t=r
    · subst t
      simp [cancel, cashAdd]
    · have hnot : t ∉ s.active := by
        intro hin
        exact ht (Finset.mem_erase.mpr ⟨he, hin⟩)
      simpa [cancel, cashAdd, he] using hv.inactive_zero t hnot

/-- A policy predicate is a checked contract certificate, not a proved rounding
implementation. Actors are already authenticated by an external adapter. -/
inductive Step (cap : ℕ) (issuer custodian : A)
    (policy : (A → ℕ) → (A → ℝ) → Prop) : Ledger A R → Ledger A R → Prop
  | issue (s) (actor a : A) (n : ℕ)
      (role : actor=issuer) (open_ : s.closed=false) (positive : 0<n)
      (limit : s.issued+n≤cap) : Step cap issuer custodian policy s (mint s a n)
  | finish (s) (actor : A) (role : actor=issuer) (open_ : s.closed=false)
      (full : s.issued=cap) : Step cap issuer custodian policy s (close s)
  | move (s) (actor a b : A) (n expected : ℕ)
      (role : actor=a) (active_ : s.closed=true) (live : s.terminal=false)
      (distinct : a≠b) (positive : 0<n) (enough : n≤s.holdings a)
      (fresh : expected=s.nonce a) : Step cap issuer custodian policy s (transfer s a b n)
  | receive (s) (actor : A) (x : ℝ) (role : actor=custodian)
      (live : s.terminal=false) (positive : 0<x) :
      Step cap issuer custodian policy s (deposit s x)
  | declare (s) (actor : A) (period : ℕ) (payout : A → ℝ) (last : Bool)
      (role : actor=custodian) (active_ : s.closed=true) (live : s.terminal=false)
      (fresh : period∉s.periods) (nonnegative : ∀ i, 0≤payout i)
      (budget : reserved s+(∑ i, payout i)≤s.vault)
      (final_budget : last=true → reserved s+(∑ i, payout i)=s.vault)
      (contract : policy s.holdings payout) :
      Step cap issuer custodian policy s (distribute s period payout last)
  | withdraw (s) (actor a : A) (r : R) (x : ℝ) (expected : ℕ)
      (role : actor=a) (positive : 0<x) (enough : x≤s.claims a)
      (fresh : r∉s.used) (nonce_fresh : expected=s.nonce a) :
      Step cap issuer custodian policy s (request s a r x)
  | settle (s) (actor : A) (r : R) (role : actor=custodian) (pending : r∈s.active) :
      Step cap issuer custodian policy s (confirm s r)
  | restore (s) (actor : A) (r : R) (role : actor=custodian) (pending : r∈s.active) :
      Step cap issuer custodian policy s (cancel s r)

theorem step_preserves_valid (cap : ℕ) (issuer custodian : A)
    (policy : (A → ℕ) → (A → ℝ) → Prop) (s t : Ledger A R)
    (hv : Valid cap s) (hs : Step cap issuer custodian policy s t) : Valid cap t := by
  cases hs with
  | issue _ a n _ ho _ hc => exact mint_valid cap s a n hv ho hc
  | finish _ _ _ hc => exact close_valid cap s hv hc
  | move _ a b n _ _ _ _ _ _ hn _ => exact transfer_valid cap s a b n hv hn
  | receive _ x _ _ hx => exact deposit_valid cap s x hv hx.le
  | declare _ period p last _ hc _ _ hp hb _ _ =>
      exact distribute_valid cap s period p last hv hp hb hc
  | withdraw _ a r x _ _ hx ha hr _ => exact request_valid cap s a r x hv hx.le ha hr
  | settle _ r _ _ => exact confirm_valid cap s r hv
  | restore _ r _ _ => exact cancel_valid cap s r hv

inductive Reachable (cap : ℕ) (issuer custodian seed : A)
    (policy : (A → ℕ) → (A → ℝ) → Prop) : Ledger A R → Prop
  | start : Reachable cap issuer custodian seed policy (initial seed)
  | next {s t} (previous : Reachable cap issuer custodian seed policy s)
      (transition : Step cap issuer custodian policy s t) :
      Reachable cap issuer custodian seed policy t

theorem reachable_valid (cap : ℕ) (issuer custodian seed : A)
    (policy : (A → ℕ) → (A → ℝ) → Prop) (s : Ledger A R)
    (hr : Reachable cap issuer custodian seed policy s) : Valid cap s := by
  induction hr with
  | start => exact initial_valid cap seed
  | next _ hs ih => exact step_preserves_valid cap issuer custodian policy _ _ ih hs

omit [DecidableEq R] [Fintype A] [Fintype R] in
theorem transfer_nonce_advances (s : Ledger A R) (a b : A) (n : ℕ) :
    (transfer s a b n).nonce a=s.nonce a+1 := by simp [transfer, natCredit]

omit [DecidableEq R] [Fintype A] [Fintype R] in
theorem transfer_old_nonce_rejected (s : Ledger A R) (a b : A) (n : ℕ) :
    s.nonce a≠(transfer s a b n).nonce a := by rw [transfer_nonce_advances]; omega

omit [DecidableEq R] [Fintype A] [Fintype R] in
theorem transfer_preserves_declared_rights (s : Ledger A R) (a b : A) (n : ℕ) :
    (transfer s a b n).claims=s.claims ∧
      (transfer s a b n).snapshots=s.snapshots := ⟨rfl,rfl⟩

omit [DecidableEq R] [DecidableEq A] [Fintype A] [Fintype R] in
theorem declared_snapshot (s : Ledger A R) (p : ℕ) (x : A → ℝ) (last : Bool) :
    (distribute s p x last).snapshots p=s.holdings := by simp [distribute]

omit [DecidableEq R] [DecidableEq A] [Fintype A] [Fintype R] in
theorem earlier_snapshot_unchanged (s : Ledger A R) (p q : ℕ) (x : A → ℝ)
    (last : Bool) (hq : q≠p) :
    (distribute s p x last).snapshots q=s.snapshots q := by simp [distribute, hq]

omit [DecidableEq A] [Fintype A] [Fintype R] in
theorem confirmed_request_not_active (s : Ledger A R) (r : R) :
    r∉(confirm s r).active := by simp [confirm]

omit [Fintype A] [Fintype R] in
theorem cancelled_request_not_active (s : Ledger A R) (r : R) :
    r∉(cancel s r).active := by simp [cancel]

omit [Fintype A] [Fintype R] in
theorem request_id_not_reusable (s : Ledger A R) (a : A) (r : R) (x : ℝ) :
    r∈(request s a r x).used := by simp [request]

omit [DecidableEq A] [DecidableEq R] in
theorem final_distribution_fully_reserved (s : Ledger A R) (p : ℕ) (x : A → ℝ)
    (hb : reserved s+(∑ i, x i)=s.vault) :
    reserved (distribute s p x true)=(distribute s p x true).vault := by
  change (∑ i, (s.claims i+x i))+(∑ r, s.pending r)=s.vault
  rw [Finset.sum_add_distrib]
  unfold reserved at hb
  linarith

end Ledger

end FormationLedgerCore

#print axioms FormationLedgerCore.buffer_nonnegative
#print axioms FormationLedgerCore.safe_iff_buffer
#print axioms FormationLedgerCore.safe_terminal_nonnegative
#print axioms FormationLedgerCore.cash_after_identity
#print axioms FormationLedgerCore.formation_funding_iff
#print axioms FormationLedgerCore.all_states_funding_iff
#print axioms FormationLedgerCore.sum_cashAdd
#print axioms FormationLedgerCore.sum_natCredit
#print axioms FormationLedgerCore.sum_natDebit
#print axioms FormationLedgerCore.initial_valid
#print axioms FormationLedgerCore.mint_valid
#print axioms FormationLedgerCore.close_valid
#print axioms FormationLedgerCore.transfer_valid
#print axioms FormationLedgerCore.deposit_valid
#print axioms FormationLedgerCore.distribute_valid
#print axioms FormationLedgerCore.request_valid
#print axioms FormationLedgerCore.confirm_valid
#print axioms FormationLedgerCore.cancel_valid
#print axioms FormationLedgerCore.step_preserves_valid
#print axioms FormationLedgerCore.reachable_valid
#print axioms FormationLedgerCore.transfer_nonce_advances
#print axioms FormationLedgerCore.transfer_old_nonce_rejected
#print axioms FormationLedgerCore.transfer_preserves_declared_rights
#print axioms FormationLedgerCore.declared_snapshot
#print axioms FormationLedgerCore.earlier_snapshot_unchanged
#print axioms FormationLedgerCore.confirmed_request_not_active
#print axioms FormationLedgerCore.cancelled_request_not_active
#print axioms FormationLedgerCore.request_id_not_reusable
#print axioms FormationLedgerCore.final_distribution_fully_reserved
