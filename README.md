# Verified Foundations for Interest-Free Finance

**A machine-checked general-equilibrium existence theory for economies with no interest-rate benchmark.**

To the author's knowledge, this is the first general-equilibrium existence
development — from the fixed-point theorem up to a competitive equilibrium — that
is fully verified by a proof assistant **and** constructed with no risk-free /
interest-bearing asset anywhere. All **25 headline theorems** are axiom-audited:
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
- **Positive time value from impatience** (`positive_time_value_from_impatience`):
  a one-agent, two-date log-utility economy whose unique competitive equilibrium has
  **discount factor exactly `β ∈ (0,1)`** — future consumption strictly discounted,
  the discount factor being the equilibrium price ratio `p₁/p₀ = β`, with no interest rate.
- **Non-uniqueness** (`equilibrium_not_unique`): an explicit continuous excess demand
  satisfying Walras' law exactly that clears at **two distinct prices** — the
  economically-relevant content of Sonnenschein–Mantel–Debreu, witnessed with a
  non-degenerate (non-autarky) excess demand.
- **Sequential (Radner) trading** (`radner_implements_arrow_debreu`): with Arrow
  securities, the sequential asset-trading budget set *equals* the Arrow–Debreu
  date-event budget set — so the intertemporal equilibrium is implementable by
  one-period asset trading, with no complete date-0 contingent market.
- **Production** (`production_equilibrium_exists`): adding constant-returns
  (zero-profit) firms, a clearing price still exists — consumer excess demand is met
  by production in every market.

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
- Still open: the full Sonnenschein–Mantel–Debreu *realization* result (constructing
  households whose aggregate demand is a prescribed `z`; the non-uniqueness *upshot*
  is witnessed above, but the surjectivity construction is a separate, genuinely hard
  program). *Incomplete-market* (GEI) sequential equilibrium and *decreasing-returns*
  production with profit-share distribution are the general cases of the two theorems
  above (which cover complete markets and constant returns respectively). And
  *monetary* time value (liquidity / convenience yield) needs a money object — a
  different model, not this engine.

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
