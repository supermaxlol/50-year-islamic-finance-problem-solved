import EscrowFundingBridge
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-! Constructed finite subscription histories, not an assumed released state.
Positive integer lots require supplied consent and settlement evidence. -/
noncomputable section
open scoped BigOperators

namespace ManyBuyerEscrow
open PrimaryEscrow

variable {A : Type*} [Fintype A] [DecidableEq A]

def receiptId (a : A) : ℕ := (Fintype.equivFin A a).val

omit [DecidableEq A] in
theorem receiptId_injective : Function.Injective (receiptId (A := A)) := by
  intro a b h
  exact (Fintype.equivFin A).injective (Fin.val_injective h)

omit [Fintype A] [DecidableEq A] in
theorem receipt_fresh (r : A → ℕ) (hr : Function.Injective r)
    (agents : Finset A) (i : A) (hi : i ∉ agents) (receipts : Finset ℕ)
    (hs : receipts ⊆ agents.image r) : r i ∉ receipts := by
  intro hm
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (hs hm)
  have hji : j = i := hr he
  exact hi (hji ▸ hj)

omit [Fintype A] in
theorem zero_extension (n : A → ℕ) (agents : Finset A) (i : A)
    (hi : i ∉ agents) (hz : n i = 0) (s : State A)
    (hs : ∀ a, s.funds.units a = if a ∈ agents then n a else 0) :
    ∀ a, s.funds.units a = if a ∈ insert i agents then n a else 0 := by
  intro a
  rw [hs a]
  by_cases ha : a = i
  · subst a
    simp [hi,hz]
  · simp [Finset.mem_insert,ha]

omit [Fintype A] in
theorem settle_extension (T : Terms A) (n : A → ℕ) (r : A → ℕ)
    (agents : Finset A) (i : A) (hi : i ∉ agents) (s : State A)
    (hs : ∀ a, s.funds.units a = if a ∈ agents then n a else 0) :
    ∀ a, (settle T s i (n i) (r i)).funds.units a =
      if a ∈ insert i agents then n a else 0 := by
  intro a
  change s.funds.units a + (if a = i then n i else 0) = _
  rw [hs a]
  by_cases ha : a = i
  · subst a
    simp [hi]
  · simp [Finset.mem_insert,ha]

theorem processed_cap (T : Terms A) (n : A → ℕ) (agents : Finset A)
    (s : State A) (hs : ∀ a, s.funds.units a = if a ∈ agents then n a else 0)
    (ht : (∑ a, n a) = T.cap) : totalUnits s.funds ≤ T.cap := by
  rw [← ht]
  apply Finset.sum_le_sum
  intro a _
  rw [hs a]
  by_cases ha : a ∈ agents <;> simp [ha]

theorem collect_many (T : Terms A) (cash : A → ℝ) (n : A → ℕ) (r : A → ℕ)
    (consent settled : A → ℕ → ℕ → Prop)
    (hc : ∀ a, 0 ≤ cash a) (hafford : ∀ a, T.price*(n a : ℝ) ≤ cash a)
    (htotal : (∑ a, n a) = T.cap) (hr : Function.Injective r)
    (hevidence : ∀ a, 0 < n a → consent a (n a) (r a) ∧ settled a (n a) (r a))
    (agents : Finset A) :
    ∃ s, Reachable T consent settled cash s ∧ s.phase = .collecting ∧
      s.now = 0 ∧ s.paused = ∅ ∧
      (∀ a, s.funds.units a = if a ∈ agents then n a else 0) ∧
      s.receipts ⊆ agents.image r := by
  induction agents using Finset.induction_on with
  | empty =>
    refine ⟨initial cash, Reachable.start, rfl, rfl, rfl, ?_, ?_⟩
    · intro a; simp [initial]
    · simp [initial]
  | @insert i agents hi ih =>
    obtain ⟨s,hs,hphase,htime,hpause,hunits,hreceipts⟩ := ih
    by_cases hz : n i = 0
    · refine ⟨s,hs,hphase,htime,hpause,zero_extension n agents i hi hz s hunits,?_⟩
      intro v hv
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (hreceipts hv)
      exact Finset.mem_image.mpr ⟨j,Finset.mem_insert_of_mem hj,he⟩
    · have hn : 0 < n i := Nat.pos_of_ne_zero hz
      have hv := reachable_valid T consent settled cash hc s hs
      have hi0 : s.funds.units i = 0 := by simpa [hi] using hunits i
      have hwallet : s.funds.wallet i = cash i := by
        have h := hv.1.subscriber_identity i
        simpa [hi0] using h
      have hnext := settle_extension T n r agents i hi s hunits
      have hcap : totalUnits s.funds+n i ≤ T.cap := by
        have h := processed_cap T n (insert i agents) (settle T s i (n i) (r i)) hnext htotal
        simpa only [settle_total] using h
      have hcash : T.price*(n i : ℝ) ≤ s.funds.wallet i := by
        rw [hwallet]
        exact hafford i
      have hstep : Step T consent settled s (settle T s i (n i) (r i)) :=
        Step.subscribe s T.custodian i (n i) (r i) rfl hphase hn hcap hcash
          (receipt_fresh r hr agents i hi s.receipts hreceipts)
          (by rw [htime]; exact Nat.zero_le _)
          (by rw [hpause]; simp) (hevidence i hn).1 (hevidence i hn).2
      refine ⟨settle T s i (n i) (r i), Reachable.next hs hstep,
        hphase,htime,hpause,hnext,?_⟩
      change insert (r i) s.receipts ⊆ (insert i agents).image r
      simpa only [Finset.image_insert] using Finset.insert_subset_insert (r i) hreceipts

theorem release_many (T : Terms A) (cash : A → ℝ) (n : A → ℕ) (r : A → ℕ)
    (consent settled : A → ℕ → ℕ → Prop)
    (hc : ∀ a, 0 ≤ cash a) (hafford : ∀ a, T.price*(n a : ℝ) ≤ cash a)
    (htotal : (∑ a, n a) = T.cap) (hr : Function.Injective r)
    (hevidence : ∀ a, 0 < n a → consent a (n a) (r a) ∧ settled a (n a) (r a))
    (hbudget : T.construction+T.reserve ≤ T.price*(T.cap : ℝ)) :
    ∃ s, Reachable T consent settled cash s ∧ Valid T cash s ∧
      s.phase = .released ∧ (∀ a, activeUnits s a = n a) ∧
      s.funds.builderPaid = T.construction ∧
      s.funds.operating = T.price*(T.cap : ℝ)-T.construction ∧
      s.funds.escrow = 0 := by
  obtain ⟨s,hs,hphase,htime,hpause,hunits,_⟩ :=
    collect_many T cash n r consent settled hc hafford htotal hr hevidence Finset.univ
  have hall : ∀ a, s.funds.units a = n a := by intro a; simpa using hunits a
  have hv := reachable_valid T consent settled cash hc s hs
  have hfull : totalUnits s.funds = T.cap := by
    unfold totalUnits
    simpa only [hall] using htotal
  have hzero : s.funds.operating = 0 ∧ s.funds.builderPaid = 0 := by
    simpa [PhaseSound,hphase] using hv.2
  have hescrow : s.funds.escrow = T.price*(T.cap : ℝ) := by
    have h := hv.1.cash_conserved
    rw [hzero.1,hzero.2,hfull] at h
    simpa using h
  have hclose : Step T consent settled s (fund s) :=
    Step.close s T.issuer rfl hphase hfull (by rw [hescrow]; exact hbudget)
      (by rw [htime]; exact Nat.zero_le _) (by rw [hpause]; simp)
  have hfunded : Reachable T consent settled cash (fund s) := Reachable.next hs hclose
  have happ : Reachable T consent settled cash (attest (fund s) Finset.univ) :=
    Reachable.next hfunded (Step.approve (fund s) T.verifier Finset.univ rfl)
  have hpay : Step T consent settled (attest (fund s) Finset.univ)
      (release T (attest (fund s) Finset.univ)) := by
    apply Step.payConstruction (attest (fund s) Finset.univ) T.custodian rfl
    · rfl
    · simp [attest]
    · simp [attest,fund,htime]
    · simp [attest,fund,hpause]
  have hreleased := Reachable.next happ hpay
  refine ⟨release T (attest (fund s) Finset.univ),hreleased,
    reachable_valid T consent settled cash hc _ hreleased,rfl,?_,rfl,?_,rfl⟩
  · intro a
    simpa [activeUnits,release,attest,fund] using hall a
  · change s.funds.escrow-T.construction = T.price*(T.cap : ℝ)-T.construction
    rw [hescrow]

end ManyBuyerEscrow

#print axioms ManyBuyerEscrow.receiptId_injective
#print axioms ManyBuyerEscrow.receipt_fresh
#print axioms ManyBuyerEscrow.zero_extension
#print axioms ManyBuyerEscrow.settle_extension
#print axioms ManyBuyerEscrow.processed_cap
#print axioms ManyBuyerEscrow.collect_many
#print axioms ManyBuyerEscrow.release_many
