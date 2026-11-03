import EscrowDispatcher
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn

/-! Exact, canonical, numeric full snapshots. The transport parser and durable
storage are outside the kernel theorem; no state field is silently discarded. -/
namespace EscrowSnapshot
open IntegerEscrow PrimaryEscrow

abbrev Wire := List (List ℕ)

structure Snapshot (n : ℕ) where
  ledgerId : ℕ
  revision : ℕ
  currencyTag : ℕ
  termsVersion : ℕ
  terms : IntegerEscrow.Terms (Fin n)
  initialCash : Fin n → ℕ
  state : IntegerEscrow.State (Fin n)

def values {n : ℕ} (xs : List ℕ) : Fin n → ℕ := fun a => xs[a.val]?.getD 0

theorem values_ofFn {n : ℕ} (f : Fin n → ℕ) : values (List.ofFn f) = f := by
  funext a
  simp [values,a.isLt]

def phaseCode : Phase → ℕ
  | .collecting => 0 | .funded => 1 | .released => 2 | .cancelled => 3
def readPhase : ℕ → Option Phase
  | 0 => some .collecting | 1 => some .funded
  | 2 => some .released | 3 => some .cancelled | _ => none

theorem readPhase_code (p : Phase) : readPhase (phaseCode p) = some p := by
  cases p <;> rfl

def bit (p : Prop) [Decidable p] : ℕ := if p then 1 else 0
def gateCode : Gate → ℕ
  | .identity => 0 | .beneficialOwner => 1 | .assetTitle => 2
  | .contractReview => 3 | .supplier => 4 | .delivery => 5
def gateRow (s : Finset Gate) : List ℕ :=
  [bit (.identity ∈ s),bit (.beneficialOwner ∈ s),bit (.assetTitle ∈ s),
   bit (.contractReview ∈ s),bit (.supplier ∈ s),bit (.delivery ∈ s)]
def readGates (xs : List ℕ) : Finset Gate :=
  Finset.univ.filter fun g => xs[gateCode g]?.getD 0 = 1

theorem readGates_row (s : Finset Gate) : readGates (gateRow s) = s := by
  ext g
  simp only [readGates,Finset.mem_filter,Finset.mem_univ,true_and]
  cases g <;> simp [gateRow,gateCode,bit]

def actionCode : Action → ℕ
  | .subscriptions => 0 | .funding => 1 | .release => 2
def actionRow (s : Finset Action) : List ℕ :=
  [bit (.subscriptions ∈ s),bit (.funding ∈ s),bit (.release ∈ s)]
def readActions (xs : List ℕ) : Finset Action :=
  ({.subscriptions,.funding,.release} : Finset Action).filter
    fun a => xs[actionCode a]?.getD 0 = 1

theorem readActions_row (s : Finset Action) : readActions (actionRow s) = s := by
  ext a
  simp only [readActions,Finset.mem_filter]
  cases a <;> simp [actionRow,actionCode,bit]

def account (n x : ℕ) : Option (Fin n) := if h : x < n then some ⟨x,h⟩ else none

theorem account_val {n : ℕ} (a : Fin n) : account n a.val = some a := by
  simp [account,a.isLt]

def termsRow {n : ℕ} (t : IntegerEscrow.Terms (Fin n)) : List ℕ :=
  [t.price,t.cap,t.construction,t.reserve,t.subscribeDeadline,t.releaseDeadline,
    t.issuer.val,t.custodian.val,t.verifier.val,t.resolver.val]

def readTerms (n : ℕ) : List ℕ → Option (IntegerEscrow.Terms (Fin n))
  | [price,cap,k,b,d1,d2,i,c,v,r] => do
    if hp : 0 < price then
      if hn : 0 < cap then
        if hd : d1 ≤ d2 then
          let issuer ← account n i
          let custodian ← account n c
          let verifier ← account n v
          let resolver ← account n r
          pure ⟨price,hp,cap,hn,k,b,d1,d2,hd,issuer,custodian,verifier,resolver⟩
        else none
      else none
    else none
  | _ => none

theorem readTerms_row {n : ℕ} (t : IntegerEscrow.Terms (Fin n)) :
    readTerms n (termsRow t) = some t := by
  cases t
  simp [*, termsRow,readTerms,account_val]

def encode {n : ℕ} (s : Snapshot n) : Wire :=
  [[1,n,s.ledgerId,s.revision,s.currencyTag,s.termsVersion],
   termsRow s.terms,List.ofFn s.initialCash,
   List.ofFn s.state.funds.wallet,List.ofFn s.state.funds.units,
   [s.state.funds.escrow,s.state.funds.operating,s.state.funds.builderPaid,
    phaseCode s.state.phase,s.state.releaseTime,s.state.now],
   gateRow s.state.approved,gateRow s.state.releaseEvidence,
   actionRow s.state.paused,s.state.receipts.sort]

def readRaw (n : ℕ) : Wire → Option (Snapshot n)
  | [[1,n',id,rev,currency,version],ts,cash,wallet,units,
      [escrow,operating,paid,phase,time,now],approved,evidence,paused,receipts] =>
    if n' = n then do
      let terms ← readTerms n ts
      let phase ← readPhase phase
      pure ⟨id,rev,currency,version,terms,values cash,
        ⟨⟨values wallet,values units,escrow,operating,paid⟩,phase,
          readGates approved,readGates evidence,time,readActions paused,receipts.toFinset,now⟩⟩
    else none
  | _ => none

theorem readRaw_encode {n : ℕ} (s : Snapshot n) : readRaw n (encode s) = some s := by
  rcases s with ⟨id,rev,currency,version,terms,cash,⟨⟨wallet,units,escrow,operating,paid⟩,
    phase,approved,evidence,time,paused,receipts,now⟩⟩
  simp [encode,readRaw,readTerms_row,readPhase_code,values_ofFn,
    readGates_row,readActions_row]

/- The re-encoding check rejects noncanonical rows, lengths, flags and receipt
duplicates/order instead of silently accepting readRaw's provisional values. -/
def decode (n : ℕ) (wire : Wire) : Option (Snapshot n) := do
  let s ← readRaw n wire
  if encode s = wire then some s else none

theorem decode_encode {n : ℕ} (s : Snapshot n) : decode n (encode s) = some s := by
  simp [decode,readRaw_encode]

theorem accepted_canonical {n : ℕ} {wire : Wire} {s : Snapshot n}
    (h : decode n wire = some s) : encode s = wire := by
  unfold decode at h
  cases hr : readRaw n wire with
  | none => simp [hr] at h
  | some t =>
    simp only [hr,Option.bind_eq_bind,Option.bind_some] at h
    split_ifs at h with hc
    · cases h
      exact hc

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro s t h
  have hd := congrArg (decode n) h
  simpa only [decode_encode,Option.some.injEq] using hd

def context {n : ℕ} (s : Snapshot n) : Wire :=
  [[1,n,s.ledgerId,s.currencyTag,s.termsVersion],termsRow s.terms,List.ofFn s.initialCash]

def loadBound {n : ℕ} (expected : Snapshot n) (wire : Wire) : Option (Snapshot n) := do
  let s ← decode n wire
  if context s = context expected then some s else none

theorem loadBound_encode {n : ℕ} (s : Snapshot n) : loadBound s (encode s) = some s := by
  simp [loadBound,decode_encode]

theorem loadBound_context {n : ℕ} {expected s : Snapshot n} {wire : Wire}
    (h : loadBound expected wire = some s) : context s = context expected := by
  unfold loadBound at h
  cases hd : decode n wire with
  | none => simp [hd] at h
  | some t =>
    simp only [hd,Option.bind_eq_bind,Option.bind_some] at h
    split_ifs at h with hc
    · cases h
      exact hc

theorem mismatched_context_rejected {n : ℕ} (expected s : Snapshot n)
    (h : context s ≠ context expected) : loadBound expected (encode s) = none := by
  simp [loadBound,decode_encode,h]

def afterRun {n : ℕ} (s : Snapshot n) (cc sc : Fin n → ℕ → ℕ → Bool)
    (events : List (EscrowDispatcher.Event (Fin n))) : Snapshot n :=
  {s with state := EscrowDispatcher.run s.terms cc sc s.state events}

theorem saved_run_restores {n : ℕ} (s : Snapshot n) (cc sc : Fin n → ℕ → ℕ → Bool)
    (events : List (EscrowDispatcher.Event (Fin n))) :
    loadBound s (encode (afterRun s cc sc events)) = some (afterRun s cc sc events) := by
  simp [loadBound,decode_encode,context,afterRun]

theorem restored_initial_valid {n : ℕ} {delta : ℝ} (hd : 0 < delta)
    (s : Snapshot n) (consent settled : Fin n → ℕ → ℕ → Prop)
    (cc sc : Fin n → ℕ → ℕ → Bool)
    (hc : ∀ a q r, cc a q r = true → consent a q r)
    (hs : ∀ a q r, sc a q r = true → settled a q r)
    (events : List (EscrowDispatcher.Event (Fin n)))
    (hi : s.state = IntegerEscrow.initial s.initialCash) :
    let t := afterRun s cc sc events
    loadBound s (encode t) = some t ∧
    PrimaryEscrow.Valid (IntegerEscrow.decodeTerms delta hd s.terms)
      (IntegerEscrow.moneyMap delta s.initialCash) (IntegerEscrow.decode delta t.state) := by
  refine ⟨saved_run_restores s cc sc events,?_⟩
  simp only [afterRun,hi]
  exact EscrowDispatcher.run_initial_valid hd s.terms consent settled cc sc hc hs s.initialCash events

end EscrowSnapshot

#print axioms EscrowSnapshot.values_ofFn
#print axioms EscrowSnapshot.readPhase_code
#print axioms EscrowSnapshot.readGates_row
#print axioms EscrowSnapshot.readActions_row
#print axioms EscrowSnapshot.account_val
#print axioms EscrowSnapshot.readTerms_row
#print axioms EscrowSnapshot.readRaw_encode
#print axioms EscrowSnapshot.decode_encode
#print axioms EscrowSnapshot.accepted_canonical
#print axioms EscrowSnapshot.encode_injective
#print axioms EscrowSnapshot.loadBound_encode
#print axioms EscrowSnapshot.loadBound_context
#print axioms EscrowSnapshot.mismatched_context_rejected
#print axioms EscrowSnapshot.saved_run_restores
#print axioms EscrowSnapshot.restored_initial_valid
