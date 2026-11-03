import PersistentWire

/-! Bounded mock-evidence prototype. JSON/stdin/OS are runtime trust boundaries.
The executed numeric transformation is PersistentWire.serializedSubmit. -/
namespace PersistentBridge
open Lean IntegerEscrow EscrowSnapshot AtomicEscrow PersistentWire
abbrev A := Fin 6
def terms : IntegerEscrow.Terms A :=
  ⟨2,by decide,6,by decide,7,5,10,20,by decide,0,1,2,3⟩
def cash (a : A) : ℕ := if a = 4 then 16 else if a = 5 then 20 else 0
def genesis : Snapshot 6 := ⟨739,0,100,8,terms,cash,IntegerEscrow.initial cash⟩
def yes : A → ℕ → ℕ → Bool := fun _ _ _ => true
def initial : Store 6 := ⟨genesis,[]⟩

def need {α : Type} (x : Option α) (message : String) : Except String α :=
  match x with | some x => .ok x | none => .error message
def storeReply (s : Store 6) : Json := Json.mkObj [
  ("ok",toJson true),("store",toJson (storeWire s)),
  ("revision",toJson (toString s.current.revision))]

def handle (j : Json) : Except String Json := do
  let args ← j.getArr?
  if args.size ≠ 3 then throw "Expected a three-element command array"
  let op ← args[0]!.getNat?
  if op = 0 then return storeReply initial
  let packet ← fromJson? args[1]! (α := Packet)
  let s ← need (recover genesis yes yes packet) "Store/history/context recovery rejected"
  if op = 1 then return storeReply s
  if op = 3 then
    let retained ← fromJson? args[2]! (α := Packet)
    let expectedResult := match s.journal with
      | [] => []
      | head::_ => resultWire ⟨.committed,s,some head⟩
    if retained ≠ expectedResult then throw "Retained result/store mismatch"
    return storeReply s
  if op ≠ 2 then throw "Unsupported command"
  let request ← fromJson? args[2]! (α := Wire)
  let response ← need (serializedSubmit 6 (context genesis) yes yes (storeWire s) request)
    "Request or complete numeric envelope rejected"
  let out ← need (readResult 6 response) "Internal result decoding failed"
  return Json.mkObj [
    ("ok",toJson true),("packet",toJson response),("store",toJson (storeWire out.store)),
    ("revision",toJson (toString out.store.current.revision)),
    ("mode",toJson (modeCode out.mode)),("outcome",toJson (outcomeWire out.outcome))]

partial def serve (input output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  let answer := match Json.parse line >>= handle with
    | .ok result => result
    | .error message => Json.mkObj [("ok",toJson false),("error",toJson message)]
  output.putStrLn answer.compress
  output.flush
  serve input output

end PersistentBridge

def main : IO Unit := do PersistentBridge.serve (← IO.getStdin) (← IO.getStdout)
