import ConnectedEnterpriseDemo

open Lean ConnectedEnterpriseDemo PersistentWire
def main : IO Unit := do
  IO.println (Json.mkObj [
    ("initial",toJson (storeWire (AtomicEscrow.Store.mk genesis []))),
    ("requests",toJson (requests.map requestWire)),
    ("completed",toJson (storeWire completed))]).compress
