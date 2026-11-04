# Strict formation, stress tolerance and exact reserve certificates

Stage 224 adds one accepted module with 23 retained declaration audits, using
standard foundations only. It sharpens three connected questions without
changing the supplied household economy, scale or productive payoff contract.

## 1. Who strictly wants to participate?

For one fresh issue, let supply be N>0, construction cost K, operating reserve
B and supplier outside option R. The funding floor is q_min=(K+B+R)/N.
Actual demand D(q) comes from finite households' unique CRRA optima with positive
current resources and independent positive future incomes. It is not an
assumed demand schedule.

At an actual formed equilibrium these conditions are equivalent:

- The supplier strictly prefers entry to its outside option.
- qN>K+B+R, equivalently q>q_min.
- D(q_min)>N.

Thus a strictly participating formed equilibrium exists exactly when strict
floor demand covers more than supply. Equality in the earlier weak criterion
allows indifference; it does not compel entry. Each subscriber strictly gains
relative to zero investment exactly when its actual holding is positive.
Positive clearing supply ensures at least one such subscriber, not that every
household invests or that every citizen benefits.

The original connected price-two, six-unit example pays construction seven and
reserve five; its supplier is indifferent. A supplied construction-six variant
has the same actual price and three-unit holdings, with issuer entry utility
one versus outside zero and strict gains for both subscribers. This is an
economic variant, not an endogenous technology discovery or a newly executed
persistent funding trace. The original trace is preserved unchanged.

## 2. How much cashflow stress can the funding support?

Write P_x(n) for cumulative net receipts through event n, including zero.
The minimum safe reserve b(x) is the largest cumulative deficit. If aligned
stressed receipts obey P_y(n)>=P_x(n)-epsilon at every prefix, then

```
b(y) <= b(x) + epsilon
```

A two-sided prefix discrepancy also gives |b(y)-b(x)|<=epsilon. If nominal
paths require at most L, the same fixed-primitives formation economy admits
the sufficient funded stress window

```
L + epsilon <= B <= qN - K - R
```

A loose stress bound makes this sufficient, not necessary. The exact stressed
path still has its exact minimum-buffer test. For equal path totals, terminal
cash agrees at the same starting reserve. Nevertheless, the separate treasury
paths [3,-5,12] and [0,-5,15] require reserves two and five respectively: delaying
an early receipt can cause a payment failure despite positive terminal cash.
These are not the six-unit fixture's productive payoff data.

Dates, stress bounds and forecast paths are supplied. Payoff/terminal-distribution
compatibility must be checked separately; a shock changing contracted receipts
or settlement timing requires a new valuation problem.

## 3. What does the executable certificate guarantee?

For signed integer minor-unit flows, the actual executed function is

```
needed([]) = 0
needed(x::xs) = max(0, needed(xs)-x)
```

It computes the least affordable budget. The companion function returns no
shortfall exactly when that budget is covered; otherwise its index is within
the supplied list, its balance is negative and all earlier balances are
nonnegative. Prefix zero covers a negative starting budget. For any positive
currency quantum delta, the decoded real minimum is delta*needed(flows).
There is no floating-point or rounding assumption.

`ReserveCalculator.certified_strict_funding` composes successful certificates
with an actual same-supply formed reference, strict cost headroom and an exactly
represented reserve. The result gives actual equilibrium, strict issuer
participation and dated affordability on every supplied certified path.
It does not infer physical truth, legal rights or actual payments from integers.

## Evidence and reproduction

- [Accepted joint source](../formal/StrictPrimaryParticipation.lean): seven
  strict-participation, seven stress and nine calculator audit endpoints.
- [Retained axiom log](../evidence/axioms/StrictPrimaryParticipation.txt): clean,
  using only `propext`, `Classical.choice`, `Quot.sound` where required.
- [Same-source worker](../runtime/ReserveWorker.lean): JSON/IO wrapper around
  those proved integer functions.
- [Retained runtime receipt](../evidence/controls/reserve_calculator.json) and
  [replies](../evidence/controls/reserve_worker.ndjson): 566 exact numerical
  comparisons plus seven malformed rejections. Private local binding paths are
  removed from the receipt with explicit transformation and original hashes.
- [Portable retained-reply check](../tests/reserve_calculator_controls.py): the
  original oracle and deterministic cases, with a new read-only wrapper. It
  independently recomputes prefix sums, minimum reserve and earliest failure;
  it does not rerun the runtime or use a copy of the recursive algorithm.

The release audit checks retained evidence and source identities, not a fresh
cold build. Parser/runtime/compiler, external evidence, custody and hardware
remain explicit trust boundaries. Neither this reserve result nor the funding
example establishes automatic fundraising, universal welfare or profitability.
