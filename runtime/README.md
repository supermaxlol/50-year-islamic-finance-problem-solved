# Bounded persistent research prototype

This directory publishes the original-byte accepted SQLite adapter, Lean
JSON-line transport and backend controls, alongside a portable launch helper.
The core transformation is `PersistentWire.serializedSubmit`; no Python copy
of economic guards determines admission.

## What is proved and what is tested

The pure dispatcher/protocol, complete numeric representations and fixed-policy
recovery are proved in Lean. The Python/SQLite adapter is tested, not formally
proved. It stores revision, full journal/current state and cached result in one
row, under `BEGIN IMMEDIATE` and a conditional version/state update. Fresh success
is returned only after commit. Reopening validates complete history and the
retained result against a pinned genesis.

DELETE journaling, synchronous EXTRA and fullfsync ON are set and read back.
Retained controls exercise 150 exact results/reopens, eight actual competing
writer schedules, six process exits and 13 corruption rejections. Process
termination is not power failure. Atomicity/durability rely on SQLite, its VFS,
the OS/filesystem and the device. See [SQLite transactions](https://www.sqlite.org/lang_transaction.html),
[synchronization](https://www.sqlite.org/pragma.html#pragma_synchronous) and
[atomic-commit assumptions](https://www.sqlite.org/atomiccommit.html).

## Optional reproduction

First run the portable retained-evidence audit from the repository root:

```
python3 scripts/verify_release.py
```

A fresh kernel build and executable run require the pinned Lean dependencies,
sufficient RAM/disk and Python 3.12 or newer. After `lake build`, the complete
backend controls can be rerun on a local POSIX platform with fork support:

```
python3 runtime/verify.py
```

The launch helper changes only build/log locations; it is not a kernel-verified
IO adapter. This release carries the original retained execution evidence, not
a claim that every published source was cold-rebuilt on a new machine. Fresh
outputs go into ignored `runtime/logs/` and `runtime/BACKEND_CONTROLS.json`.
Only newly created test children are terminated by the fault tests. No real
funds or user databases are used, and test output databases are not deleted.

The exact connected economic witness can be exported after building:

```
lake env lean --run runtime/ExportDemo.lean
```

Its accepted complete initial/request/final record is also retained in
`evidence/controls/connected_witness.json`. See [the connected demonstration](../docs/CONNECTED_DEMO.md).

## Exact reserve calculator

After a kernel build, the separate same-source calculator worker accepts one
JSON line `[budget, cashflows]`, with signed integers encoded as strings:

```
lake env lean --run runtime/ReserveWorker.lean
```

For input `["4",["-5","12"]]` it returns required reserve `"5"`, affordability
`false`, first shortfall prefix `1`, its balance `"-1"`, and terminal balance
`"11"`. Positive terminal cash does not pay an earlier bill. Negative initial
budgets can fail at prefix zero. The pure functions are proved; JSON/IO are
tested boundaries. Any positive currency quantum decodes the integer model
exactly, without a rounding claim.

The retained worker replies and sanitized original receipt are in
`evidence/controls/reserve_worker.ndjson` and `reserve_calculator.json`.
`python3 tests/reserve_calculator_controls.py` checks those 566 numerical replies
and seven malformed-input rejections with the original deterministic oracle;
it does not launch Lean or rerun the runtime. The launch command above is
reproduction guidance, not a new cold-build receipt. See
[the theorem and application scope](../docs/STRICT_PARTICIPATION_AND_RESERVES.md).

## Explicit trust boundaries

Role numbers are not authentication. Evidence checks are fixed mocks, not
consent signatures, settled bank transfers or telemetry. Full-history replay
checks consistency, not authenticity: an older valid prefix or a fully rewritten
valid history requires an external freshness/authentication anchor to reject.
The prototype assumes trusted local paths/schema; hostile path replacement,
distributed consensus, production throughput and real custody are outside it.

Do not fundraise with this prototype or describe its output as a legal title,
regulatory/Shariah approval, guaranteed return or production security audit.
