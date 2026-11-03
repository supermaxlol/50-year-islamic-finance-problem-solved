import AtomicEscrow

/-! Complete numeric transaction envelopes. JSON/SQL I/O remain explicit
runtime/storage boundaries; the economic core is imported, not translated. -/
namespace PersistentWire
open PrimaryEscrow EscrowDispatcher EscrowSnapshot AtomicEscrow
abbrev Packet := List Wire

def readGate : ℕ → Option Gate
  | 0 => some .identity | 1 => some .beneficialOwner | 2 => some .assetTitle
  | 3 => some .contractReview | 4 => some .supplier | 5 => some .delivery | _ => none
def readAction : ℕ → Option Action
  | 0 => some .subscriptions | 1 => some .funding | 2 => some .release | _ => none
theorem readGate_code (g : Gate) : readGate (gateCode g) = some g := by cases g <;> rfl
theorem readAction_code (a : Action) : readAction (actionCode a) = some a := by cases a <;> rfl

def rawEvent (n : ℕ) : List ℕ → Option (Event (Fin n))
  | [0,a,b,q,r] => do pure (.subscribe (← account n a) (← account n b) q r)
  | [1,a] => do pure (.close (← account n a))
  | [2,a] => do pure (.release (← account n a))
  | [3,a] => do pure (.cancel (← account n a))
  | [4,a,b] => do pure (.refund (← account n a) (← account n b))
  | 5 :: a :: gates => do pure (.approve (← account n a) (readGates gates))
  | [6,a,g] => do pure (.revoke (← account n a) (← readGate g))
  | [7,a,b] => do pure (.pause (← account n a) (← readAction b))
  | [8,a,b] => do pure (.resolve (← account n a) (← readAction b))
  | [9,t] => some (.tick t)
  | _ => none

theorem rawEvent_row {n : ℕ} (e : Event (Fin n)) : rawEvent n (eventRow e) = some e := by
  cases e <;> simp [eventRow,rawEvent,account_val,readGate_code,readAction_code,readGates_row]

def readEvent (n : ℕ) (xs : List ℕ) : Option (Event (Fin n)) := do
  let e ← rawEvent n xs
  if eventRow e = xs then some e else none
theorem readEvent_row {n : ℕ} (e : Event (Fin n)) : readEvent n (eventRow e) = some e := by
  simp [readEvent,rawEvent_row]

def requestWire {n : ℕ} (r : Request n) : Wire := [[r.id,r.expectedRevision],eventRow r.event]
def readRequest (n : ℕ) : Wire → Option (Request n)
  | [[id,rev],event] => do pure ⟨id,rev,(← readEvent n event)⟩
  | _ => none
theorem readRequest_wire {n : ℕ} (r : Request n) : readRequest n (requestWire r) = some r := by
  cases r
  simp [readRequest,requestWire,readEvent_row]

def boolCode (b : Bool) : ℕ := if b then 1 else 0
def readBool : ℕ → Option Bool
  | 0 => some false | 1 => some true | _ => none
theorem readBool_code (b : Bool) : readBool (boolCode b) = some b := by cases b <;> rfl

def entryWire {n : ℕ} (e : Entry n) : Wire :=
  [e.request.id,e.request.expectedRevision,boolCode e.accepted] :: eventRow e.request.event :: encode e.post
def readEntry (n : ℕ) : Wire → Option (Entry n)
  | [id,rev,b] :: event :: post => do
    pure ⟨⟨id,rev,(← readEvent n event)⟩,(← readBool b),(← EscrowSnapshot.decode n post)⟩
  | _ => none
theorem readEntry_wire {n : ℕ} (e : Entry n) : readEntry n (entryWire e) = some e := by
  rcases e with ⟨⟨id,rev,event⟩,b,post⟩
  simp [entryWire,readEntry,readEvent_row,readBool_code,decode_encode]

def readEntries (n : ℕ) : List Wire → Option (List (Entry n))
  | [] => some []
  | e :: es => do pure ((← readEntry n e) :: (← readEntries n es))
theorem readEntries_wire {n : ℕ} (es : List (Entry n)) :
    readEntries n (es.map entryWire) = some es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [readEntries,readEntry_wire,ih]

def storeWire {n : ℕ} (s : Store n) : Packet :=
  [[219,1,n]] :: encode s.current :: s.journal.map entryWire
def rawStore (n : ℕ) : Packet → Option (Store n)
  | [[219,1,n']] :: current :: journal =>
    if n' = n then do pure ⟨(← EscrowSnapshot.decode n current),(← readEntries n journal)⟩
    else none
  | _ => none
theorem rawStore_wire {n : ℕ} (s : Store n) : rawStore n (storeWire s) = some s := by
  cases s
  simp [storeWire,rawStore,decode_encode,readEntries_wire]

def readStore (n : ℕ) (packet : Packet) : Option (Store n) := do
  let s ← rawStore n packet
  if storeWire s = packet then some s else none
theorem readStore_wire {n : ℕ} (s : Store n) : readStore n (storeWire s) = some s := by
  simp [readStore,rawStore_wire]
theorem storeWire_injective {n : ℕ} : Function.Injective (@storeWire n) := by
  intro s t h
  have hh := congrArg (readStore n) h
  simpa only [readStore_wire,Option.some.injEq] using hh

def modeCode : Mode → ℕ
  | .committed => 0 | .replay => 1 | .conflict => 2 | .stale => 3 | .wrongContext => 4
def readMode : ℕ → Option Mode
  | 0 => some .committed | 1 => some .replay | 2 => some .conflict
  | 3 => some .stale | 4 => some .wrongContext | _ => none
theorem readMode_code (m : Mode) : readMode (modeCode m) = some m := by cases m <;> rfl
def outcomeWire {n : ℕ} : Option (Entry n) → Wire
  | none => [] | some e => entryWire e
def readOutcome (n : ℕ) : Wire → Option (Option (Entry n))
  | [] => some none
  | w => (readEntry n w).map some
theorem readOutcome_wire {n : ℕ} (e : Option (Entry n)) :
    readOutcome n (outcomeWire e) = some e := by
  cases e with
  | none => rfl
  | some e => rcases e with ⟨⟨id,rev,event⟩,b,post⟩; simp [outcomeWire,entryWire,readOutcome,readEntry,readEvent_row,readBool_code,decode_encode]

def resultWire {n : ℕ} (r : Result n) : Packet :=
  [[219,2,n,modeCode r.mode]] :: outcomeWire r.outcome :: storeWire r.store
def readResult (n : ℕ) : Packet → Option (Result n)
  | [[219,2,n',mode]] :: outcome :: store =>
    if n' = n then do pure ⟨(← readMode mode),(← readStore n store),(← readOutcome n outcome)⟩
    else none
  | _ => none
theorem readResult_wire {n : ℕ} (r : Result n) : readResult n (resultWire r) = some r := by
  cases r
  simp [resultWire,readResult,readMode_code,readStore_wire,readOutcome_wire]

def serializedSubmit (n : ℕ) (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (packet : Packet) (request : Wire) : Option Packet := do
  let s ← readStore n packet
  let r ← readRequest n request
  pure (resultWire (AtomicEscrow.submit expected cc sc s r))

theorem serializedSubmit_wire {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) :
    serializedSubmit n expected cc sc (storeWire s) (requestWire r) =
      some (resultWire (AtomicEscrow.submit expected cc sc s r)) := by
  simp [serializedSubmit,readStore_wire,readRequest_wire]

theorem serializedSubmit_decodes {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) :
    (serializedSubmit n expected cc sc (storeWire s) (requestWire r)).bind (readResult n) =
      some (AtomicEscrow.submit expected cc sc s r) := by
  simp [serializedSubmit_wire,readResult_wire]

/- Recovery replays committed requests under one fixed evidence policy. The
prototype explicitly uses a fixed mock policy, not current real attestations. -/
def replayStore {n : ℕ} (genesis : Snapshot n) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) : Store n :=
  AtomicEscrow.run (context genesis) cc sc ⟨genesis,[]⟩ (s.journal.reverse.map Entry.request)
def recover {n : ℕ} (genesis : Snapshot n) (cc sc : Fin n → ℕ → ℕ → Bool)
    (packet : Packet) : Option (Store n) := do
  let s ← readStore n packet
  if storeWire (replayStore genesis cc sc s) = packet then some s else none

theorem recovery_sound {n : ℕ} (g : Snapshot n) (cc sc : Fin n → ℕ → ℕ → Bool)
    (packet : Packet) (s : Store n) (h : recover g cc sc packet = some s) :
    s = replayStore g cc sc s := by
  unfold recover at h
  cases hr : readStore n packet with
  | none => simp [hr] at h
  | some t =>
    simp only [hr,Option.bind_eq_bind,Option.bind_some] at h
    split_ifs at h with hc
    · cases h
      have ht : storeWire s = packet := by
        unfold readStore at hr
        cases hh : rawStore n packet with
        | none => simp [hh] at hr
        | some z =>
          simp only [hh,Option.bind_eq_bind,Option.bind_some] at hr
          split_ifs at hr with hz
          · cases hr; exact hz
      exact storeWire_injective (ht.trans hc.symm)

theorem recovery_valid {n : ℕ} {delta : ℝ} (hd : 0 < delta)
    (g : Snapshot n) (consent settled : Fin n → ℕ → ℕ → Prop)
    (cc sc : Fin n → ℕ → ℕ → Bool)
    (hc : ∀ a q r, cc a q r = true → consent a q r)
    (hs : ∀ a q r, sc a q r = true → settled a q r)
    (hi : g.state = IntegerEscrow.initial g.initialCash)
    (packet : Packet) (s : Store n) (hr : recover g cc sc packet = some s) :
    PrimaryEscrow.Valid (IntegerEscrow.decodeTerms delta hd s.current.terms)
      (IntegerEscrow.moneyMap delta s.current.initialCash) (IntegerEscrow.decode delta s.current.state) := by
  have he := recovery_sound g cc sc packet s hr
  have hv : PrimaryEscrow.Valid (IntegerEscrow.decodeTerms delta hd (replayStore g cc sc s).current.terms)
      (IntegerEscrow.moneyMap delta (replayStore g cc sc s).current.initialCash)
      (IntegerEscrow.decode delta (replayStore g cc sc s).current.state) :=
    AtomicEscrow.run_valid hd (context g) consent settled cc sc hc hs g
      (s.journal.reverse.map Entry.request) hi
  rw [← he] at hv
  exact hv

end PersistentWire

#print axioms PersistentWire.readGate_code
#print axioms PersistentWire.readAction_code
#print axioms PersistentWire.rawEvent_row
#print axioms PersistentWire.readEvent_row
#print axioms PersistentWire.readRequest_wire
#print axioms PersistentWire.readBool_code
#print axioms PersistentWire.readEntry_wire
#print axioms PersistentWire.readEntries_wire
#print axioms PersistentWire.rawStore_wire
#print axioms PersistentWire.readStore_wire
#print axioms PersistentWire.storeWire_injective
#print axioms PersistentWire.readMode_code
#print axioms PersistentWire.readOutcome_wire
#print axioms PersistentWire.readResult_wire
#print axioms PersistentWire.serializedSubmit_wire
#print axioms PersistentWire.serializedSubmit_decodes
#print axioms PersistentWire.recovery_sound
#print axioms PersistentWire.recovery_valid
