import FormationLedgerCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! One fixed-price, fixed-supply enterprise. Guarded specification only:
settlement attestations and formal identities are trusted interface inputs. -/
noncomputable section
open scoped BigOperators

namespace PrimaryEscrow
open FormationLedgerCore

inductive Phase | collecting | funded | released | cancelled
  deriving DecidableEq

inductive Gate | identity | beneficialOwner | assetTitle | contractReview | supplier | delivery
  deriving DecidableEq

instance : Fintype Gate where
  elems := {.identity, .beneficialOwner, .assetTitle, .contractReview, .supplier, .delivery}
  complete := by intro g; cases g <;> simp

inductive Action | subscriptions | funding | release
  deriving DecidableEq

structure Terms (A : Type*) where
  price : ℝ
  price_pos : 0 < price
  cap : ℕ
  cap_pos : 0 < cap
  construction : ℝ
  construction_nonneg : 0 ≤ construction
  reserve : ℝ
  reserve_nonneg : 0 ≤ reserve
  subscribeDeadline : ℕ
  releaseDeadline : ℕ
  deadline_order : subscribeDeadline ≤ releaseDeadline
  issuer : A
  custodian : A
  verifier : A
  resolver : A

structure Accounts (A : Type*) where
  wallet : A → ℝ
  units : A → ℕ
  escrow : ℝ
  operating : ℝ
  builderPaid : ℝ

structure State (A : Type*) where
  funds : Accounts A
  phase : Phase
  approved : Finset Gate
  releaseEvidence : Finset Gate
  releaseTime : ℕ
  paused : Finset Action
  receipts : Finset ℕ
  now : ℕ

def totalUnits {A : Type*} [Fintype A] (f : Accounts A) : ℕ := ∑ a, f.units a

structure CoreValid {A : Type*} [Fintype A] (T : Terms A)
    (initialCash : A → ℝ) (f : Accounts A) : Prop where
  wallets_nonnegative : ∀ a, 0 ≤ f.wallet a
  cap_bound : totalUnits f ≤ T.cap
  subscriber_identity : ∀ a, f.wallet a + T.price * (f.units a : ℝ) = initialCash a
  escrow_nonnegative : 0 ≤ f.escrow
  operating_nonnegative : 0 ≤ f.operating
  builder_nonnegative : 0 ≤ f.builderPaid
  cash_conserved : f.escrow + f.operating + f.builderPaid = T.price * (totalUnits f : ℝ)

def PhaseSound {A : Type*} [Fintype A] (T : Terms A) (p : Phase)
    (f : Accounts A) (evidence : Finset Gate) (releaseTime : ℕ) : Prop :=
  match p with
  | .collecting | .cancelled => f.operating = 0 ∧ f.builderPaid = 0
  | .funded => f.operating = 0 ∧ f.builderPaid = 0 ∧ totalUnits f = T.cap ∧
      T.construction + T.reserve ≤ f.escrow
  | .released => f.escrow = 0 ∧ totalUnits f = T.cap ∧
      f.builderPaid = T.construction ∧
      f.operating = T.price * (T.cap : ℝ) - T.construction ∧
      T.reserve ≤ f.operating ∧ Finset.univ ⊆ evidence ∧ releaseTime ≤ T.releaseDeadline

def Valid {A : Type*} [Fintype A] (T : Terms A) (initialCash : A → ℝ)
    (s : State A) : Prop :=
  CoreValid T initialCash s.funds ∧ PhaseSound T s.phase s.funds s.releaseEvidence s.releaseTime

def initial {A : Type*} (cash : A → ℝ) : State A :=
  ⟨⟨cash, fun _ => 0, 0, 0, 0⟩, .collecting, ∅, ∅, 0, ∅, ∅, 0⟩

def settle {A : Type*} [DecidableEq A] (T : Terms A) (s : State A)
    (a : A) (n receipt : ℕ) : State A :=
  {s with
    funds := {s.funds with
      wallet := cashAdd s.funds.wallet a (-(T.price * (n : ℝ)))
      units := natCredit s.funds.units a n
      escrow := s.funds.escrow + T.price * (n : ℝ)}
    receipts := insert receipt s.receipts}

def fund {A : Type*} (s : State A) : State A := {s with phase := .funded}

def release {A : Type*} (T : Terms A) (s : State A) : State A :=
  {s with
    phase := .released
    funds := {s.funds with
      escrow := 0
      operating := s.funds.escrow - T.construction
      builderPaid := T.construction}
    releaseEvidence := s.approved
    releaseTime := s.now}

def cancel {A : Type*} (s : State A) : State A := {s with phase := .cancelled}

def refund {A : Type*} [DecidableEq A] (T : Terms A) (s : State A) (a : A) : State A :=
  {s with funds := {s.funds with
    wallet := cashAdd s.funds.wallet a (T.price * (s.funds.units a : ℝ))
    units := natDebit s.funds.units a (s.funds.units a)
    escrow := s.funds.escrow - T.price * (s.funds.units a : ℝ)}}

def attest {A : Type*} (s : State A) (gates : Finset Gate) : State A :=
  {s with approved := s.approved ∪ gates}

def revoke {A : Type*} (s : State A) (gate : Gate) : State A :=
  {s with approved := s.approved.erase gate}

def pause {A : Type*} (s : State A) (action : Action) : State A :=
  {s with paused := insert action s.paused}

def resolve {A : Type*} (s : State A) (action : Action) : State A :=
  {s with paused := s.paused.erase action}

def tick {A : Type*} (s : State A) (time : ℕ) : State A := {s with now := time}

def activeUnits {A : Type*} (s : State A) (a : A) : ℕ :=
  if s.phase = .released then s.funds.units a else 0

section Accounting
variable {A : Type*} [Fintype A] [DecidableEq A]

theorem settle_total (T : Terms A) (s : State A) (a : A) (n r : ℕ) :
    totalUnits (settle T s a n r).funds = totalUnits s.funds + n := by
  exact sum_natCredit _ a n

theorem refund_total (T : Terms A) (s : State A) (a : A) :
    totalUnits (refund T s a).funds + s.funds.units a = totalUnits s.funds := by
  exact sum_natDebit _ a _ (le_refl _)

omit [DecidableEq A] in
theorem initial_valid (T : Terms A) (cash : A → ℝ) (hc : ∀ a, 0 ≤ cash a) :
    Valid T cash (initial cash) := by
  refine ⟨?_, ?_⟩
  · constructor
    · exact hc
    · simp [initial, totalUnits]
    · intro a; simp [initial]
    · exact le_refl 0
    · exact le_refl 0
    · exact le_refl 0
    · simp [initial, totalUnits]
  · exact ⟨rfl, rfl⟩

theorem settle_valid (T : Terms A) (cash : A → ℝ) (s : State A) (a : A) (n r : ℕ)
    (hv : Valid T cash s) (hp : s.phase = .collecting)
    (hc : totalUnits s.funds + n ≤ T.cap)
    (hw : T.price * (n : ℝ) ≤ s.funds.wallet a) : Valid T cash (settle T s a n r) := by
  have hn : 0 ≤ T.price * (n : ℝ) := mul_nonneg (le_of_lt T.price_pos) (Nat.cast_nonneg n)
  refine ⟨?_, ?_⟩
  · constructor
    · intro i
      by_cases hi : i = a
      · subst i
        simp only [settle, cashAdd, ite_true]
        linarith
      · simpa [settle, cashAdd, hi] using hv.1.wallets_nonnegative i
    · simpa only [settle_total] using hc
    · intro i
      by_cases hi : i = a
      · subst i
        simp only [settle, cashAdd, natCredit, ite_true, Nat.cast_add]
        linarith [hv.1.subscriber_identity a]
      · simpa [settle, cashAdd, natCredit, hi] using hv.1.subscriber_identity i
    · change 0 ≤ s.funds.escrow + T.price * (n : ℝ)
      linarith [hv.1.escrow_nonnegative]
    · exact hv.1.operating_nonnegative
    · exact hv.1.builder_nonnegative
    · rw [settle_total, Nat.cast_add, mul_add]
      change s.funds.escrow + T.price * (n : ℝ) + s.funds.operating +
        s.funds.builderPaid = T.price * (totalUnits s.funds : ℝ) + T.price * (n : ℝ)
      linarith [hv.1.cash_conserved]
  · simpa [PhaseSound, settle, hp] using hv.2

omit [DecidableEq A] in
theorem fund_valid (T : Terms A) (cash : A → ℝ) (s : State A)
    (hv : Valid T cash s) (hp : s.phase = .collecting)
    (hs : totalUnits s.funds = T.cap)
    (hb : T.construction + T.reserve ≤ s.funds.escrow) : Valid T cash (fund s) := by
  have hh : s.funds.operating = 0 ∧ s.funds.builderPaid = 0 := by
    simpa [PhaseSound, hp] using hv.2
  exact ⟨hv.1, hh.1, hh.2, hs, hb⟩

omit [DecidableEq A] in
theorem release_valid (T : Terms A) (cash : A → ℝ) (s : State A)
    (hv : Valid T cash s) (hp : s.phase = .funded)
    (he : Finset.univ ⊆ s.approved) (ht : s.now ≤ T.releaseDeadline) :
    Valid T cash (release T s) := by
  have hh : s.funds.operating = 0 ∧ s.funds.builderPaid = 0 ∧
      totalUnits s.funds = T.cap ∧ T.construction + T.reserve ≤ s.funds.escrow := by
    simpa [PhaseSound, hp] using hv.2
  have hc : s.funds.escrow = T.price * (T.cap : ℝ) := by
    have h := hv.1.cash_conserved
    rw [hh.1, hh.2.1, hh.2.2.1] at h
    simpa using h
  refine ⟨?_, ?_⟩
  · refine {hv.1 with
      escrow_nonnegative := le_refl 0
      operating_nonnegative := ?_
      builder_nonnegative := T.construction_nonneg
      cash_conserved := ?_}
    · change 0 ≤ s.funds.escrow - T.construction
      linarith [hh.2.2.2, T.reserve_nonneg]
    · change 0 + (s.funds.escrow - T.construction) + T.construction =
        T.price * (totalUnits s.funds : ℝ)
      rw [hh.2.2.1, hc]; ring
  · refine ⟨rfl, hh.2.2.1, rfl, ?_, ?_, he, ht⟩
    · change s.funds.escrow - T.construction = T.price * (T.cap : ℝ) - T.construction
      rw [hc]
    · change T.reserve ≤ s.funds.escrow - T.construction
      linarith [hh.2.2.2]

omit [DecidableEq A] in
theorem cancel_valid (T : Terms A) (cash : A → ℝ) (s : State A)
    (hv : Valid T cash s) (hp : s.phase = .collecting ∨ s.phase = .funded) :
    Valid T cash (cancel s) := by
  refine ⟨hv.1, ?_⟩
  rcases hp with hp | hp
  · simpa [PhaseSound, cancel, hp] using hv.2
  · have hh := hv.2
    simp only [PhaseSound, hp] at hh
    exact ⟨hh.1, hh.2.1⟩

omit [DecidableEq A] in
theorem refund_affordable (T : Terms A) (cash : A → ℝ) (s : State A) (a : A)
    (hv : Valid T cash s) (hp : s.phase = .cancelled) :
    T.price * (s.funds.units a : ℝ) ≤ s.funds.escrow := by
  have hh : s.funds.operating = 0 ∧ s.funds.builderPaid = 0 := by
    simpa [PhaseSound, hp] using hv.2
  have hu : s.funds.units a ≤ totalUnits s.funds :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (s.funds.units i)) (Finset.mem_univ a)
  have hur : (s.funds.units a : ℝ) ≤ (totalUnits s.funds : ℝ) := by exact_mod_cast hu
  have he := hv.1.cash_conserved
  rw [hh.1, hh.2] at he
  have hm := mul_le_mul_of_nonneg_left hur (le_of_lt T.price_pos)
  linarith

theorem refund_valid (T : Terms A) (cash : A → ℝ) (s : State A) (a : A)
    (hv : Valid T cash s) (hp : s.phase = .cancelled) : Valid T cash (refund T s a) := by
  have hn : 0 ≤ T.price * (s.funds.units a : ℝ) :=
    mul_nonneg (le_of_lt T.price_pos) (Nat.cast_nonneg _)
  have hb := refund_affordable T cash s a hv hp
  have hs : (totalUnits (refund T s a).funds : ℝ) + (s.funds.units a : ℝ) =
      (totalUnits s.funds : ℝ) := by exact_mod_cast refund_total T s a
  refine ⟨?_, ?_⟩
  · constructor
    · intro i
      by_cases hi : i = a
      · subst i
        simp only [refund, cashAdd, ite_true]
        linarith [hv.1.wallets_nonnegative a]
      · simpa [refund, cashAdd, hi] using hv.1.wallets_nonnegative i
    · have hs' := refund_total T s a
      have hc := hv.1.cap_bound
      omega
    · intro i
      by_cases hi : i = a
      · subst i
        simp only [refund, cashAdd, natDebit, ite_true, Nat.sub_self, Nat.cast_zero,
          mul_zero, add_zero]
        exact hv.1.subscriber_identity a
      · simpa [refund, cashAdd, natDebit, hi] using hv.1.subscriber_identity i
    · change 0 ≤ s.funds.escrow - T.price * (s.funds.units a : ℝ)
      linarith
    · exact hv.1.operating_nonnegative
    · exact hv.1.builder_nonnegative
    · change s.funds.escrow - T.price * (s.funds.units a : ℝ) + s.funds.operating +
        s.funds.builderPaid = T.price * (totalUnits (refund T s a).funds : ℝ)
      have hm := congrArg (fun x : ℝ => T.price * x) hs
      rw [mul_add] at hm
      linarith [hv.1.cash_conserved]
  · simpa [PhaseSound, refund, hp] using hv.2

end Accounting

theorem governance_valid {A : Type*} [Fintype A] (T : Terms A) (cash : A → ℝ)
    (s : State A) (hv : Valid T cash s) (gs : Finset Gate) (g : Gate) (a : Action) (t : ℕ) :
    Valid T cash (attest s gs) ∧ Valid T cash (revoke s g) ∧
      Valid T cash (pause s a) ∧ Valid T cash (resolve s a) ∧ Valid T cash (tick s t) :=
  ⟨hv, hv, hv, hv, hv⟩

theorem refund_zeros_entitlement {A : Type*} [DecidableEq A]
    (T : Terms A) (s : State A) (a : A) : (refund T s a).funds.units a = 0 := by
  simp [refund, natDebit]

theorem receipt_recorded {A : Type*} [DecidableEq A]
    (T : Terms A) (s : State A) (a : A) (n r : ℕ) : r ∈ (settle T s a n r).receipts := by
  simp [settle]

theorem pause_only_named_action {A : Type*} (s : State A) (a b : Action) (h : b ≠ a) :
    (b ∈ (pause s a).paused ↔ b ∈ s.paused) := by simp [pause, h]

theorem pause_preserves_refund_inputs {A : Type*} (s : State A) (action : Action) :
    (pause s action).funds = s.funds ∧ (pause s action).phase = s.phase := ⟨rfl, rfl⟩

theorem release_records_attestations {A : Type*} (T : Terms A) (s : State A) :
    (release T s).releaseEvidence = s.approved ∧ (release T s).releaseTime = s.now := ⟨rfl, rfl⟩

theorem no_active_ownership_before_release {A : Type*} (s : State A)
    (h : s.phase ≠ .released) (a : A) : activeUnits s a = 0 := by simp [activeUnits, h]

theorem released_ownership_reconciles {A : Type*} [Fintype A]
    (T : Terms A) (cash : A → ℝ) (s : State A) (hv : Valid T cash s)
    (hp : s.phase = .released) : (∑ a, activeUnits s a) = T.cap := by
  have hh := hv.2
  simp only [PhaseSound, hp] at hh
  simpa [activeUnits, hp, totalUnits] using hh.2.1

theorem total_cash_conservation {A : Type*} [Fintype A]
    (T : Terms A) (cash : A → ℝ) (s : State A) (hv : Valid T cash s) :
    (∑ a, s.funds.wallet a) + s.funds.escrow + s.funds.operating + s.funds.builderPaid =
      ∑ a, cash a := by
  have hh : (∑ a, (s.funds.wallet a + T.price * (s.funds.units a : ℝ))) = ∑ a, cash a :=
    Finset.sum_congr rfl (fun a _ => hv.1.subscriber_identity a)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum] at hh
  have hc := hv.1.cash_conserved
  unfold totalUnits at hc
  linarith

end PrimaryEscrow

#print axioms PrimaryEscrow.settle_total
#print axioms PrimaryEscrow.refund_total
#print axioms PrimaryEscrow.initial_valid
#print axioms PrimaryEscrow.settle_valid
#print axioms PrimaryEscrow.fund_valid
#print axioms PrimaryEscrow.release_valid
#print axioms PrimaryEscrow.cancel_valid
#print axioms PrimaryEscrow.refund_affordable
#print axioms PrimaryEscrow.refund_valid
#print axioms PrimaryEscrow.governance_valid
#print axioms PrimaryEscrow.refund_zeros_entitlement
#print axioms PrimaryEscrow.receipt_recorded
#print axioms PrimaryEscrow.pause_only_named_action
#print axioms PrimaryEscrow.pause_preserves_refund_inputs
#print axioms PrimaryEscrow.release_records_attestations
#print axioms PrimaryEscrow.no_active_ownership_before_release
#print axioms PrimaryEscrow.released_ownership_reconciles
#print axioms PrimaryEscrow.total_cash_conservation
