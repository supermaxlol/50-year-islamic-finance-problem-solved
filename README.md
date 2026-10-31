# Verified Foundations for Interest-Free Finance

**A machine-checked general-equilibrium existence theory for economies with no interest-rate benchmark.**

To the author's knowledge, this is the first general-equilibrium existence
development — from the fixed-point theorem up to a competitive equilibrium — that
is fully verified by a proof assistant **and** constructed with no risk-free /
interest-bearing asset anywhere. All **21 headline theorems** are axiom-audited:
each depends only on Lean 4's three standard foundational axioms (`propext`,
`Classical.choice`, `Quot.sound`) — no `sorry`, no added axioms, no gaps, no warnings.

## What is proven

**The machinery**
- **Kakutani** fixed-point theorem for correspondences; **Brouwer** fixed-point theorem.
- **Gale–Nikaido–Debreu existence**: a continuous excess-demand map obeying
  Walras' law on the price simplex has a market-clearing price (strong and weak forms).
- **Berge's maximum theorem** (fixed-, varying-, and compact-subset domain forms):
  demand varies continuously with prices.
- **Budget lower-hemicontinuity**; **unique maximizer from strict concavity**.

**The equilibria** (each built end-to-end on the machinery above)
- **Utility-maximizing households** (`optimizing_economy_equilibrium`): a strictly
  concave utility induces unique, continuous, budget-feasible demand, and a clearing
  price exists at which the optimal allocation satisfies every market.
- **General preferences** (`general_preferences_equilibrium`): the same, for **any**
  continuous strictly-concave utility — not just the quadratic case.
- **Interest-free asset market** (`interest_free_asset_market_equilibrium`): a
  competitive equilibrium for an overlapping-payoff asset market with **no risk-free
  asset** — state-contingent (equity/partnership-like) claims, not fixed-interest debt.
- **Incomplete markets / Radner** (`incomplete_markets_equilibrium_exists`): existence
  witnessed with strictly incomplete asset span (one asset, two states) — the payoff
  needs full *column* rank, never spanning.
- **Multi-period / intertemporal** (`intertemporal_equilibrium_exists`): an
  Arrow–Debreu date-event equilibrium exists over a finite horizon. The equilibrium
  **date-event prices are the discount factors** — time value of money arises as an
  *endogenous shadow price*, with no interest rate, bond, or risk-free asset in the
  primitives.

The construction uses **no numeraire interest rate**. The classical objection
that valuation, discounting, and equilibrium require an interest-rate benchmark
does not hold for this class.

## Scope — what this does *and does not* claim

For precision (and because overclaiming helps no one):

- This is a **defined class** of economies (finite goods/states, strictly-concave
  utility, specific structure), not a fully general theory of all economies.
- It is a **mathematical-foundations** result. It makes **no** empirical,
  institutional, legal, or Shariah (jurisprudential) claim. The broader project of
  interest-free finance has those components too; this repository addresses the
  theoretical-foundations one.
- It establishes **existence and coherence** of interest-free equilibrium and
  discounting. It does **not** address the informational and control functions of
  debt (safe-claim / liquidity / screening / costly-state-verification / control-in-
  default). Those live in contract theory and mechanism design, not equilibrium
  existence, and remain open.
- Open on the pure-theory side too: the Sonnenschein–Mantel–Debreu realization
  result and *sequential* (Radner-trading) multi-period equilibrium are not formalized
  here — they are separate, large general-equilibrium programs, not instances of this
  engine.

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
