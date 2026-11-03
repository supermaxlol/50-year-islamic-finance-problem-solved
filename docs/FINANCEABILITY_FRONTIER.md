# When can voluntary funding also cover operating bills?

The formation theorem and dated cash theorem answer different questions.
Stage 222 connects them for one fixed-scale fresh issue.

Let a reference plan actually form at price q with N units. Hold household
resources, preferences, productive payoffs and N fixed. A new plan's construction
K, reserve B and supplier outside option R satisfy:

```text
formation  <=>  K + B + R <= q N
```

Whenever the new plan forms, its actual price and household holdings equal
the reference values. Costs can change viability without changing price: the
households still solve the same problem and clear the same fixed supply.
This is not a general claim that costs do not affect prices. If costs change
output, payoffs, issue size, household resources or available investments, the
comparison no longer holds those primitives fixed.

For each supplied dated net-cashflow path, the required buffer is its maximum
cumulative shortfall, including the zero initial prefix. For finitely many
paths, let L be the maximum of these required buffers. Then:

```text
formation AND every dated bill affordable  <=>  L <= B <= q N - K - R
```

The proof covers an arbitrary supplied family path by path; the finite maximum
is a convenient summary. If the interval is empty, the fixed issue cannot meet
both requirements. Cutting reserves can close a funding gap only by violating
operating affordability if it takes B below L.

## Exact connected example

The [accepted risky demonstration](CONNECTED_DEMO.md) has q=2, N=6, K=7, R=0,
and net operating paths (-5,12) and (-5,0). Required reserve is five; affordable
reserve is at most 12-7=5. Thus the safe interval is [5,5], with no headroom.
Reserve four misses the first payment, while reserve six cannot be financed
with the unchanged demand/payoffs/issue.

## Formal scope

[`FinanceabilityFrontier.lean`](../formal/FinanceabilityFrontier.lean) imports
the actual finite-household CRRA primary-formation economy and
[`FormationLedgerCore`](../formal/FormationLedgerCore.lean). Seven audited
results establish equilibrium transfer, price/holding invariance, the total-cost
and reserve frontiers, lower-cost preservation, above-frontier nonformation and
the exact safe reserve window. Source and clean axiom log are retained verbatim.

The plan is supplied and the issuer is price-taking, with weak participation.
The theorem does not optimize technology, output or scale, make every project
financeable or prove a deployed business solvent. Cash-path affordability does
not alone establish terminal distribution compatibility: supplied cashflows
must agree with the productive-payoff contract. Omitted shocks, false external
evidence, custody and actual payments remain outside this theorem. This small
compositional extension is not a claim of historical first-ever priority.
