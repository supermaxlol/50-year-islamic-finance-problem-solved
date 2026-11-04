import StrictPrimaryParticipation

/-! Thin exact-integer JSON adapter. Parser, IO and runtime remain tested
boundaries; the executed needed/firstShortfall functions are the proved ones. -/
namespace ReserveWorker
open Lean ReserveCalculator

def integer (j : Json) : Except String Int := do
  let s ← j.getStr?
  match s.toInt? with
  | some n => return n
  | none => throw "Expected a signed integer string"

def handle (j : Json) : Except String Json := do
  let args ← j.getArr?
  if args.size ≠ 2 then throw "Expected [budget, cashflows]"
  let budget ← integer args[0]!
  let entries ← args[1]!.getArr?
  let mut flows : List Int := []
  for e in entries do
    let x ← integer e
    flows := x::flows
  let ordered := flows.reverse
  let result := inspect budget ordered
  let balance := result.2.map (fun n => toString (budget+(ordered.take n).sum))
  return Json.mkObj [
    ("ok",toJson true),("required",toJson (toString result.1)),
    ("affordable",toJson result.2.isNone),("shortfall_prefix",toJson result.2),
    ("shortfall_balance",toJson balance),("terminal_balance",toJson (toString (budget+ordered.sum)))]

partial def serve (input output : IO.FS.Stream) : IO Unit := do
  let line ← input.getLine
  if line.isEmpty then return
  let answer := match Json.parse line >>= handle with
    | .ok result => result
    | .error message => Json.mkObj [("ok",toJson false),("error",toJson message)]
  output.putStrLn answer.compress
  output.flush
  serve input output

end ReserveWorker

def main : IO Unit := do ReserveWorker.serve (← IO.getStdin) (← IO.getStdout)
