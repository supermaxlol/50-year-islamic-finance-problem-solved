# Verified Foundations for Interest-Free Finance

**A machine-checked general-equilibrium existence theory for economies with no interest-rate benchmark.**

To the author's knowledge, this is the first general-equilibrium existence
development — from the fixed-point theorem up to a competitive equilibrium — that
is fully verified by a proof assistant **and** constructed with no risk-free /
interest-bearing asset anywhere. Every theorem is axiom-audited: it depends only
on Lean 4's three standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`, no added axioms, no gaps.

## What is proven

- **Kakutani** fixed-point theorem for correspondences; **Brouwer** fixed-point theorem.
- **Gale–Nikaido–Debreu existence**: a continuous excess-demand map obeying
  Walras' law on the price simplex has a market-clearing price (strong and weak forms).
- **Berge's maximum theorem** (fixed-, varying-, and compact-subset domain forms):
  demand varies continuously with prices.
- **Budget lower-hemicontinuity**; **unique maximizer from strict concavity**.
- **Competitive equilibrium with utility-maximizing households**
  (`optimizing_economy_equilibrium`): a strictly concave utility induces unique,
  continuous, budget-feasible demand, and there exists a clearing price at which
  the optimal allocation satisfies every market.

The construction uses **no numeraire interest rate**. The classical objection
that valuation and equilibrium require an interest-rate benchmark does not hold
for this class.

## Scope — what this does *and does not* claim

For precision (and because overclaiming helps no one):

- This is a **defined class** of economies (CRRA / strictly-concave utility, finite
  goods, specific structure), not a fully general theory of all economies.
- It is a **mathematical-foundations** result. It makes **no** empirical,
  institutional, legal, or Shariah (jurisprudential) claim. The broader project of
  interest-free finance has those components too; this repository addresses the
  theoretical-foundations one.
- `optimizing_economy_equilibrium` is an Arrow–Debreu-style competitive-equilibrium
  existence theorem; instantiating the engine on a specific interest-free
  asset-market structure is further applied work on the same machinery.

## Verify it yourself

Requires Lean 4 (`v4.35.0`) and Mathlib (`v4.35.0`). See `NOTICE.md` for the
Brouwer/Kakutani dependency.

```sh
lake exe cache get              # fetch the Mathlib build cache
lake build                      # build the development
lake env lean GEOverlap.lean    # re-run the #print axioms audit
```

- `GEOverlap.lean` — the full development.
- `AXIOM_AUDIT.txt` — the axiom audit (every theorem: `[propext, Classical.choice, Quot.sound]`).
- `SEAL_GND.json` — module hash, theorem inventory, and provenance.

## Author

Shehzad Ahmed — ORCID [0009-0007-3538-6811](https://orcid.org/0009-0007-3538-6811).
