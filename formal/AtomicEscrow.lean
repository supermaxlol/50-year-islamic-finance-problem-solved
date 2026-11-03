import EscrowSnapshot

/-! A linearized transaction specification. The complete return store is one
commit unit; a storage backend must refine this atomic primitive separately. -/
namespace AtomicEscrow
open IntegerEscrow PrimaryEscrow EscrowDispatcher EscrowSnapshot

def eventRow {n : ℕ} : Event (Fin n) → List ℕ
  | .subscribe actor a q r => [0,actor.val,a.val,q,r]
  | .close actor => [1,actor.val]
  | .release actor => [2,actor.val]
  | .cancel actor => [3,actor.val]
  | .refund actor a => [4,actor.val,a.val]
  | .approve actor gates => [5,actor.val] ++ gateRow gates
  | .revoke actor gate => [6,actor.val,gateCode gate]
  | .pause actor action => [7,actor.val,actionCode action]
  | .resolve actor action => [8,actor.val,actionCode action]
  | .tick time => [9,time]

theorem gateCode_eq {g h : Gate} : gateCode g = gateCode h ↔ g = h := by
  cases g <;> cases h <;> simp [gateCode]
theorem actionCode_eq {a b : Action} : actionCode a = actionCode b ↔ a = b := by
  cases a <;> cases b <;> simp [actionCode]
theorem gateRow_eq {g h : Finset Gate} : gateRow g = gateRow h ↔ g = h := by
  constructor
  · intro he
    have hr := congrArg readGates he
    simpa only [readGates_row] using hr
  · intro he
    rw [he]

theorem eventRow_injective {n : ℕ} : Function.Injective (@eventRow n) := by
  intro e f h
  cases e <;> cases f <;>
    simp_all [eventRow,gateCode_eq,actionCode_eq,gateRow_eq,Fin.ext_iff]

structure Request (n : ℕ) where
  id : ℕ
  expectedRevision : ℕ
  event : Event (Fin n)

def requestKey {n : ℕ} (r : Request n) : List ℕ :=
  r.expectedRevision :: eventRow r.event

theorem requestKey_binding {n : ℕ} (r t : Request n)
    (h : requestKey r = requestKey t) :
    r.expectedRevision = t.expectedRevision ∧ r.event = t.event := by
  have hh : r.expectedRevision = t.expectedRevision ∧ eventRow r.event = eventRow t.event :=
    List.cons.inj h
  exact ⟨hh.1,eventRow_injective hh.2⟩

structure Entry (n : ℕ) where
  request : Request n
  accepted : Bool
  post : Snapshot n

structure Store (n : ℕ) where
  current : Snapshot n
  journal : List (Entry n)

inductive Mode | committed | replay | conflict | stale | wrongContext
  deriving DecidableEq

structure Result (n : ℕ) where
  mode : Mode
  store : Store n
  outcome : Option (Entry n)

def lookup {n : ℕ} (id : ℕ) : List (Entry n) → Option (Entry n)
  | [] => none
  | e :: es => if e.request.id = id then some e else lookup id es

def fresh {n : ℕ} (cc sc : Fin n → ℕ → ℕ → Bool) (s : Store n) (r : Request n) : Result n :=
  let out := dispatch s.current.terms cc sc s.current.state r.event
  let post := {s.current with revision := s.current.revision+1,state := out.state}
  let entry := Entry.mk r out.accepted post
  ⟨.committed,⟨post,entry :: s.journal⟩,some entry⟩

/- The cache lookup precedes the revision check: an identical retry returns its
original outcome after later transactions, without rerunning evidence checks. -/
def submit {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) : Result n :=
  if context s.current = expected then
    match lookup r.id s.journal with
    | some old =>
      if requestKey old.request = requestKey r then ⟨.replay,s,some old⟩
      else ⟨.conflict,s,none⟩
    | none =>
      if r.expectedRevision = s.current.revision then fresh cc sc s r
      else ⟨.stale,s,none⟩
  else ⟨.wrongContext,s,none⟩

theorem fresh_eq {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (hc : context s.current = expected)
    (hl : lookup r.id s.journal = none) (hv : r.expectedRevision = s.current.revision) :
    submit expected cc sc s r = fresh cc sc s r := by
  simp [submit,hc,hl,hv]

theorem committed_iff {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) :
    (submit expected cc sc s r).mode = .committed ↔
      context s.current = expected ∧ lookup r.id s.journal = none ∧
      r.expectedRevision = s.current.revision := by
  by_cases hc : context s.current = expected
  · cases hl : lookup r.id s.journal with
    | none =>
      by_cases hv : r.expectedRevision = s.current.revision <;>
        simp [submit,hc,hl,hv,fresh]
    | some old =>
      by_cases hk : requestKey old.request = requestKey r <;>
        simp [submit,hc,hl,hk]
  · simp [submit,hc]

theorem noncommit_unchanged {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (h : (submit expected cc sc s r).mode ≠ .committed) :
    (submit expected cc sc s r).store = s := by
  by_cases hc : context s.current = expected
  · cases hl : lookup r.id s.journal with
    | none =>
      by_cases hv : r.expectedRevision = s.current.revision
      · simp [submit,hc,hl,hv,fresh] at h
      · simp [submit,hc,hl,hv]
    | some old =>
      by_cases hk : requestKey old.request = requestKey r <;> simp [submit,hc,hl,hk]
  · simp [submit,hc]

theorem cached_retry {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (old : Entry n)
    (hc : context s.current = expected) (hl : lookup r.id s.journal = some old)
    (hk : requestKey old.request = requestKey r) :
    submit expected cc sc s r = ⟨.replay,s,some old⟩ := by
  simp [submit,hc,hl,hk]

theorem conflicting_retry {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (old : Entry n)
    (hc : context s.current = expected) (hl : lookup r.id s.journal = some old)
    (hk : requestKey old.request ≠ requestKey r) :
    submit expected cc sc s r = ⟨.conflict,s,none⟩ := by
  simp [submit,hc,hl,hk]

theorem stale_unchanged {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (hc : context s.current = expected)
    (hl : lookup r.id s.journal = none) (hv : r.expectedRevision ≠ s.current.revision) :
    submit expected cc sc s r = ⟨.stale,s,none⟩ := by
  simp [submit,hc,hl,hv]

theorem committed_revision {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (h : (submit expected cc sc s r).mode = .committed) :
    (submit expected cc sc s r).store.current.revision = s.current.revision+1 := by
  rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
  rw [fresh_eq expected cc sc s r hc hl hv]
  rfl

theorem stale_read_cannot_commit_twice {n : ℕ} (expected : Wire)
    (cc sc : Fin n → ℕ → ℕ → Bool) (s : Store n) (r t : Request n)
    (h : (submit expected cc sc s r).mode = .committed)
    (hv : t.expectedRevision = s.current.revision) :
    (submit expected cc sc (submit expected cc sc s r).store t).mode ≠ .committed := by
  intro ht
  have he := ((committed_iff expected cc sc (submit expected cc sc s r).store t).mp ht).2.2
  rw [committed_revision expected cc sc s r h,hv] at he
  omega

theorem committed_coherent {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (h : (submit expected cc sc s r).mode = .committed) :
    ∃ e, (submit expected cc sc s r).outcome = some e ∧
      (submit expected cc sc s r).store.journal = e :: s.journal ∧
      (submit expected cc sc s r).store.current = e.post ∧
      e.request = r ∧ e.accepted = (dispatch s.current.terms cc sc s.current.state r.event).accepted ∧
      e.post.state = (dispatch s.current.terms cc sc s.current.state r.event).state := by
  rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
  rw [fresh_eq expected cc sc s r hc hl hv]
  exact ⟨_,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem committed_refusal_state {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (h : (submit expected cc sc s r).mode = .committed)
    (hr : (dispatch s.current.terms cc sc s.current.state r.event).accepted = false) :
    (submit expected cc sc s r).store.current.state = s.current.state := by
  rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
  rw [fresh_eq expected cc sc s r hc hl hv]
  exact rejected_unchanged s.current.terms cc sc s.current.state r.event hr

theorem fresh_retry {n : ℕ} (expected : Wire) (cc sc cc' sc' : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (h : (submit expected cc sc s r).mode = .committed) :
    (submit expected cc' sc' (submit expected cc sc s r).store r).mode = .replay ∧
    (submit expected cc' sc' (submit expected cc sc s r).store r).store =
      (submit expected cc sc s r).store ∧
    (submit expected cc' sc' (submit expected cc sc s r).store r).outcome =
      (submit expected cc sc s r).outcome := by
  rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
  rw [fresh_eq expected cc sc s r hc hl hv]
  let old : Entry n := ⟨r,(dispatch s.current.terms cc sc s.current.state r.event).accepted,
    (fresh cc sc s r).store.current⟩
  have hctx : context (fresh cc sc s r).store.current = expected := hc
  have hl' : lookup r.id (fresh cc sc s r).store.journal = some old := by
    simp [fresh,lookup,old]
  rw [cached_retry expected cc' sc' (fresh cc sc s r).store r old hctx hl' rfl]
  exact ⟨rfl,rfl,rfl⟩

theorem fixed_context {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) :
    context (submit expected cc sc s r).store.current = context s.current ∧
    (submit expected cc sc s r).store.current.terms = s.current.terms ∧
    (submit expected cc sc s r).store.current.initialCash = s.current.initialCash := by
  by_cases h : (submit expected cc sc s r).mode = .committed
  · rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
    rw [fresh_eq expected cc sc s r hc hl hv]
    exact ⟨rfl,rfl,rfl⟩
  · rw [noncommit_unchanged expected cc sc s r h]
    exact ⟨rfl,rfl,rfl⟩

theorem journal_retained {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) :
    ∀ e ∈ s.journal, e ∈ (submit expected cc sc s r).store.journal := by
  intro e he
  by_cases h : (submit expected cc sc s r).mode = .committed
  · obtain ⟨entry,_,hj,_,_,_,_⟩ := committed_coherent expected cc sc s r h
    rw [hj]
    exact List.mem_cons_of_mem _ he
  · rw [noncommit_unchanged expected cc sc s r h]
    exact he

theorem lookup_none_iff {n : ℕ} (id : ℕ) (es : List (Entry n)) :
    lookup id es = none ↔ ∀ e ∈ es, e.request.id ≠ id := by
  induction es with
  | nil => simp [lookup]
  | cons e es ih =>
    by_cases h : e.request.id = id <;> simp [lookup,h,ih]

theorem journal_ids_nodup {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (hn : (s.journal.map fun e => e.request.id).Nodup) :
    ((submit expected cc sc s r).store.journal.map fun e => e.request.id).Nodup := by
  by_cases h : (submit expected cc sc s r).mode = .committed
  · rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
    rw [fresh_eq expected cc sc s r hc hl hv]
    change (r.id :: s.journal.map (fun e => e.request.id)).Nodup
    rw [List.nodup_cons]
    refine ⟨?_,hn⟩
    intro hm
    obtain ⟨e,he,hid⟩ := List.mem_map.mp hm
    exact ((lookup_none_iff r.id s.journal).mp hl e he) hid
  · rw [noncommit_unchanged expected cc sc s r h]
    exact hn

theorem lookup_retained {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (r : Request n) (id : ℕ) (old : Entry n)
    (hb : lookup id s.journal = some old) :
    lookup id (submit expected cc sc s r).store.journal = some old := by
  by_cases h : (submit expected cc sc s r).mode = .committed
  · rcases (committed_iff expected cc sc s r).mp h with ⟨hc,hl,hv⟩
    have hne : r.id ≠ id := by
      intro hid
      rw [hid,hb] at hl
      contradiction
    rw [fresh_eq expected cc sc s r hc hl hv]
    simpa only [fresh,lookup,ite_eq_right hne] using hb
  · rw [noncommit_unchanged expected cc sc s r h]
    exact hb

theorem submit_reachable {n : ℕ} (expected : Wire)
    (consent settled : Fin n → ℕ → ℕ → Prop) (cc sc : Fin n → ℕ → ℕ → Bool)
    (hc : ∀ a q r, cc a q r = true → consent a q r)
    (hs : ∀ a q r, sc a q r = true → settled a q r)
    (s : Store n) (r : Request n)
    (hr : IntegerEscrow.Reachable s.current.terms consent settled s.current.initialCash s.current.state) :
    IntegerEscrow.Reachable (submit expected cc sc s r).store.current.terms consent settled
      (submit expected cc sc s r).store.current.initialCash (submit expected cc sc s r).store.current.state := by
  by_cases h : (submit expected cc sc s r).mode = .committed
  · rcases (committed_iff expected cc sc s r).mp h with ⟨hctx,hl,hv⟩
    rw [fresh_eq expected cc sc s r hctx hl hv]
    change IntegerEscrow.Reachable s.current.terms consent settled s.current.initialCash
      (dispatch s.current.terms cc sc s.current.state r.event).state
    rcases step_or_same s.current.terms consent settled cc sc hc hs s.current.state r.event with hp | hp
    · exact IntegerEscrow.Reachable.next hr hp
    · rw [hp]
      exact hr
  · rw [noncommit_unchanged expected cc sc s r h]
    exact hr

def run {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) : List (Request n) → Store n
  | [] => s
  | r :: rs => run expected cc sc (submit expected cc sc s r).store rs

theorem run_ids_nodup {n : ℕ} (expected : Wire) (cc sc : Fin n → ℕ → ℕ → Bool)
    (s : Store n) (rs : List (Request n))
    (hn : (s.journal.map fun e => e.request.id).Nodup) :
    ((run expected cc sc s rs).journal.map fun e => e.request.id).Nodup := by
  induction rs generalizing s with
  | nil => exact hn
  | cons r rs ih => exact ih _ (journal_ids_nodup expected cc sc s r hn)

theorem run_reachable {n : ℕ} (expected : Wire)
    (consent settled : Fin n → ℕ → ℕ → Prop) (cc sc : Fin n → ℕ → ℕ → Bool)
    (hc : ∀ a q r, cc a q r = true → consent a q r)
    (hs : ∀ a q r, sc a q r = true → settled a q r)
    (s : Store n) (rs : List (Request n))
    (hr : IntegerEscrow.Reachable s.current.terms consent settled s.current.initialCash s.current.state) :
    IntegerEscrow.Reachable (run expected cc sc s rs).current.terms consent settled
      (run expected cc sc s rs).current.initialCash (run expected cc sc s rs).current.state := by
  induction rs generalizing s with
  | nil => exact hr
  | cons r rs ih => exact ih _ (submit_reachable expected consent settled cc sc hc hs s r hr)

theorem run_valid {n : ℕ} {delta : ℝ} (hd : 0 < delta) (expected : Wire)
    (consent settled : Fin n → ℕ → ℕ → Prop) (cc sc : Fin n → ℕ → ℕ → Bool)
    (hc : ∀ a q r, cc a q r = true → consent a q r)
    (hs : ∀ a q r, sc a q r = true → settled a q r)
    (s : Snapshot n) (rs : List (Request n)) (hi : s.state = IntegerEscrow.initial s.initialCash) :
    let t := run expected cc sc ⟨s,[]⟩ rs
    PrimaryEscrow.Valid (decodeTerms delta hd t.current.terms) (moneyMap delta t.current.initialCash)
      (IntegerEscrow.decode delta t.current.state) := by
  apply IntegerEscrow.reachable_valid hd
  apply run_reachable expected consent settled cc sc hc hs
  simpa only [hi] using (IntegerEscrow.Reachable.start
    (T := s.terms) (consent := consent) (settled := settled) (cash := s.initialCash))

end AtomicEscrow

#print axioms AtomicEscrow.gateCode_eq
#print axioms AtomicEscrow.actionCode_eq
#print axioms AtomicEscrow.gateRow_eq
#print axioms AtomicEscrow.eventRow_injective
#print axioms AtomicEscrow.requestKey_binding
#print axioms AtomicEscrow.fresh_eq
#print axioms AtomicEscrow.committed_iff
#print axioms AtomicEscrow.noncommit_unchanged
#print axioms AtomicEscrow.cached_retry
#print axioms AtomicEscrow.conflicting_retry
#print axioms AtomicEscrow.stale_unchanged
#print axioms AtomicEscrow.committed_revision
#print axioms AtomicEscrow.stale_read_cannot_commit_twice
#print axioms AtomicEscrow.committed_coherent
#print axioms AtomicEscrow.committed_refusal_state
#print axioms AtomicEscrow.fresh_retry
#print axioms AtomicEscrow.fixed_context
#print axioms AtomicEscrow.journal_retained
#print axioms AtomicEscrow.lookup_none_iff
#print axioms AtomicEscrow.journal_ids_nodup
#print axioms AtomicEscrow.lookup_retained
#print axioms AtomicEscrow.submit_reachable
#print axioms AtomicEscrow.run_ids_nodup
#print axioms AtomicEscrow.run_reachable
#print axioms AtomicEscrow.run_valid
