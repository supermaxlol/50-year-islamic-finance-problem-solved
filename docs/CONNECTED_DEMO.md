# From actual household choice to a persistent funding record

This exact two-household example is the finite integration checkpoint, not a
claim about a deployed institution or a new currency.

```text
payoffs/probabilities + preferences/resources
                 ↓ actual global optimization
       price 2; three units per household
                 ↓ cost-covering voluntary formation
       proceeds 12 = construction 7 + reserve 5
                 ↓ five proved-core transactions
       subscriptions → close → approve → release
                 ↓ tested SQLite/reopening/retry execution
       exact complete record matches the proved target
```

## The economy and what is actually established

| Input/result | Household 1 | Household 2 |
|---|---:|---:|
| Current resources | 16 | 20 |
| Preference/waiting weight | 7/9 | 5/9 |
| Background income in either state | 1 | 1 |
| Unique optimal holding at price 2 | 3 | 3 |
| Remaining current consumption | 10 | 14 |
| Future consumption in good state | 7 | 7 |
| Future consumption in bad state | 1 | 1 |

Both use logarithmic utility. The project pays two units per ownership unit with
probability 9/10, or zero with probability 1/10. Effective state weights combine
those probabilities with household preference weights. There is no lending
benchmark. The KKT conditions and accepted strict-concavity/global-optimality
theorem identify actual unique optima against every affordable nonnegative
holding; they are not arbitrary allocations given an equity label.

The six supplied units clear. The issue covers construction seven plus operating
reserve five. The issuer breaks even and accepts equality with its zero outside
option. This is rational weak participation, not a proof that an indifferent
supplier must enter. The accepted formation theorem also proves uniqueness of
the formed price/holdings in this specified economy.

## What reaches the ledger

Four separate administrative accounts are 0–3; the households are 4–5. Five
typed requests post the two three-unit subscriptions, close, approve every named
gate and release. The final store has revision five, five admitted journal
entries, wallets ten/fourteen, active units three/three, escrow zero, operating
cash five and builder payment seven. The ledger objective equals each household's
actual economic objective. Its complete encoding recovers by replay.

The retained SQLite run obtains exactly that entire initial/final store. It
executes five commits, reopens after each, then retries each original request
after release. Cached outcomes return without changing the final record.

The two supplied operating cashflow paths are `[-5,+12]` and `[-5,0]`. The exact
required reserve is five; terminal enterprise cash is twelve or zero, matching
six units paying two or zero. Physical loss is not removed. These operating
flows are an accounting theorem, not new operating-payment API operations or
observed business performance.

## The justified composed claim

> One exact risky economy's actual voluntary cost-covering choices correspond
> to a proved executable funding history, whose complete final record is obtained
> and recovered by the specified tested persistent implementation, under its
> explicit evidence/runtime/storage assumptions.

The economic and pure execution statements have 18 new audited endpoints in
`ConnectedEnterpriseDemo.lean`. Database execution is tested, not kernel-proved.
Consent/settlement are mock evidence. Authentication, real custody, enforceable
title, fees, arbitrary lots, endogenous scale, actual fundraising and welfare
effects are not established by this example.

This is the planned bounded prototype's stopping point. Further mathematics,
production software and field work can proceed as distinct projects. The focused
mathematical paper need not wait for all of them.
