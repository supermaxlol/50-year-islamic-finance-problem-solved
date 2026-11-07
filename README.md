# Verified Foundations for Interest-Free Finance

**Machine-checked foundations, productive-ownership equilibrium and bounded
funding institutions without an externally supplied lending benchmark.**

We construct defined ownership economies in which payoffs, probabilities,
preferences, resources and permitted trades determine valuation and holdings.
The connected applications cover proportional ownership certificates, funded
mutual protection, supplied compute enterprises, dated operating affordability
and a guarded primary-subscription/escrow lifecycle.

The November 2026 update contains **90 Lean modules** and **918 recorded
declaration-audit endpoints** across the foundation and accepted extension chain.
Endpoints include supporting lemmas and controls; they are not 918 independent
discoveries. All retained logs are clean and use only standard foundations
(`propext`, `Classical.choice`, `Quot.sound`). Proof sources and runtime artifacts
marked source-identical retain their accepted bytes; receipt sanitization and
portable wrappers are disclosed separately. This release audit does not pretend
that copying accepted evidence is a fresh cold rebuild.

Start with [the detailed status table](docs/PROGRAMME_STATUS.md),
[remaining gaps and claim upgrades](docs/ROADMAP.md), and
[the primary funding constitution](docs/PRIMARY_FUNDING.md).

**Where the mechanism fits in the real world — [technical-fit memos](docs/TECHNICAL_FIT_2026-11-06.md)** (69 memos, §Z failure matrix) and its companion synthesis, **[bigger picture](docs/BIGGER_PICTURE_2026-11-06.md)** (one maths for the last 50 and the next 50).

# One maths for the last 50 and the next 50.

## Solved the 50-year-old Islamic finance maths problem — and the maths problem we will face in the next 50 years

## Why this matters — the missing piece

As automation lets capital produce more of the output and labor less of it, the
economic question shifts from *"what is my wage?"* to *"what do I own?"*
Economists have seen this coming — the problem is often posed as *whoever owns the
machines ends up owning the output* — but the ownership answer has always carried
an unproven hole: no one had shown that an economy in which people are sustained by
**ownership of production instead of wages** can actually *clear* — positive
prices, budgets that balance, markets that settle — and do so with **no
interest-rate benchmark** anchoring it.

That coherence result is the piece that was missing, and it is what this work
supplies, **machine-checked**: for a defined economy built on state-contingent
ownership claims, a competitive equilibrium exists, with binding budgets, exact
clearing, and no risk-free lending rate. It does not forecast automation or claim
any policy is just or achievable — it proves that the economy such a world would
require is mathematically coherent rather than wishful. Interest-free finance is
one instance; the result is secular and general.

## Latest connected results

- **Actual heterogeneous overlapping-payoff markets:** existence with global
  household optimization, positive prices, binding budgets and exact clearing;
  initially assetless households are included in the stated finite CRRA class.
- **Multiplicity and conditional uniqueness:** an actual economy supports two
  distinct equilibria. Around a supported no-net-trade reference, a separate
  theorem establishes unique actual equilibria and one-sided boundary responses
  for sufficiently small admissible joint primitive changes.
- **Ownership certificates and funded protection:** specified denomination,
  backing, exhaustion and cash-allocation identities are connected to valuation.
- **Compute and due-date cash:** supplied bottleneck production and funded
  operating plans produce payoff data; the exact cash buffer characterizes
  payment affordability across supplied state paths.
- **Primary escrow (Stage 209):** 32 audited endpoints cover consented settled
  subscription posting, budgeted close, attested release, ownership activation,
  cancellation, affordable non-repeatable refunds and named dispute scopes.
  Released cash meets the imported operating-buffer condition.
- **Actual voluntary formation (Stages 211–214):** in the defined single-new-issue
  class, funded formation exists if and only if actual household demand at the
  construction/buffer/outside-option floor covers supply. Independent positive
  future incomes and arbitrary positive CRRA curvatures are admitted. Actual
  natural-lot-compatible choices connect to reached escrow release.
- **Exact executable funding (Stages 215–218):** integer money refines the
  real-valued rules; the proved dispatcher and versioned protocol handle
  refusals, cached retries, conflicting identifiers and stale versions.
- **Persistence (Stage 219):** complete journal/result encoding, same-core
  correspondence and conditional replay recovery are proved. The local SQLite
  adapter passes 150 exact comparisons, eight competing-writer schedules, six
  process-exit cases and 13 corruption rejections. SQLite itself is not proved.
- **Connected demonstration (Stage 220):** two households' unique actual choices,
  cost-covering formation, five executable funding requests and complete recovered
  state are connected in Lean. The same final record is obtained in SQLite,
  including reopening and cached retries. This is a risky two-state synthetic
  enterprise, not observed fundraising or a guaranteed-return investment.
- **Financeability frontier (Stage 222):** holding household primitives, payoffs
  and issue size fixed, a formed price gives an exact ceiling on construction,
  reserve and supplier outside option. Formation and dated operating affordability
  hold together exactly when the required buffer fits below that ceiling.
  See the [safe reserve window](docs/FINANCEABILITY_FRONTIER.md).
- **Strict participation, stress and exact reserves (Stage 224):** strict issuer
  participation holds exactly when actual demand at the funding floor strictly
  exceeds supply. Positive subscribers strictly gain relative to zero investment.
  Cumulative cashflow loss bounds give funded reserve-stress certificates. The
  proved integer calculator returns the minimum reserve and earliest negative
  cash prefix; the same functions' transport passes 566 exact comparisons and
  seven malformed-input rejections. See [the connected guarantees and limits](docs/STRICT_PARTICIPATION_AND_RESERVES.md).
- **Integer payouts, fees and certified price bounds (Stage 226):** a declared
  ordered cumulative-quota rule distributes integer cash after a basis-point fee
  with exact fee-plus-owner conservation, zero payment to zero ownership, and error
  below one minor unit per payment; it is the declared ordered-rounding rule, not
  the older largest-remainder allocator. Feasible household-score certificates
  enclose the actual formed price — a log-utility example gives the interval
  `[1.99, 2.01]` (midpoint error at most `1/100`) and certifies strictly inactive
  households — without inserting the known price; this is a conditional certificate,
  not a general numerical solver. The payout transport passes 508 exact comparisons
  and eleven malformed-input rejections. No new database run is involved. See
  [payouts and price certificates](docs/PAYOUTS_AND_PRICE_CERTIFICATES.md).
- **Production, welfare and general-equilibrium frontier (Stages 228–249):** endogenous
  profit-maximizing production with profit income in household budgets; multi-issue
  interacting formation; decreasing returns and a money object; both SMD directions
  (function-level realizability and the rational-demand aggregate excess demand);
  micro-founded multi-household equilibrium; first and second welfare theorems (including
  a separating-hyperplane support result and its economic wrapper from preferences);
  core, uniqueness and money premium; Walras' law from local non-satiation; Nash
  bargaining; continuous firm supply over a production set; and expenditure
  minimization. The upstream engines are a set-valued Gale–Nikaido–Debreu theorem,
  a general Berge maximum theorem, a price-extraction/separating-price lemma, and a
  reusable production-economy structure. Full Mantel surjectivity and genuinely
  sequential incomplete-market equilibrium remain open; see
  [the frontier note](docs/GE_FRONTIER_2026-11-06.md).

The economic and pure executable core is **proved**; the database adapter is
**tested under explicit storage/runtime assumptions**. Truthful physical evidence,
authentication, real custody, legal title and demonstrated social outcomes are
not supplied by these results. See the [connected example](docs/CONNECTED_DEMO.md),
[implementation contract](runtime/README.md) and [roadmap](docs/ROADMAP.md).

## What this contribution is — and is not

This repository is a **sealed 90-module Lean formalization**, SHA-audited and kept to
standard foundations, rare in this space because it separates two questions the
literature usually blurs:

- **(a) Existence:** payoffs, preferences and permitted trades can close an
  ownership economy *without an external lending benchmark*.
- **(b) Allocation/settlement:** conservation-preserving settlement at minor-unit
  granularity with ordered cumulative-quota distribution.

Both are proved **in the model** — binding-budget clearing with productive
payoffs and certificates. They point at the mechanism bottleneck, not at every
consequence of the production equation.

### The "50-year problem" in Islamic finance — what it is

The phrase originates with the critique coined by **M. Ayub (2007)**, reinforced by
**M. Umer Chapra**, and echoed by **Monzer Kahf**: despite five decades of
instrument engineering, Islamic finance has not built a genuinely riba-free
benchmark. Practice prices against LIBOR/SOFR/SONIA/MYOR-i and preserves a
carry on those liquidity assumptions; murabaha/tawarruq reproduce the cash-flow
shape of conventional credit; genuine profit-and-loss sharing (musharakah/
mudarabah) remains a small slice of assets; IIBR/MYOR-i are transaction-referenced
Islamic references that inherit conventional overnight structure. None of these is
a formal claim made by this repo; they are the market facts the repo is positioned
against.

### What this repository closes — and what it does not

| Missing from the 50-year problem | Can this mechanism deliver it? |
|---|---|
| A price-formation rule independent of risk-free rates | **Yes, in the model** — binding-budget clearing with productive payoffs + certificates; no exogenous benchmark import is required |
| Executable, conservation-preserving settlement for equity/profit-share | **Yes, in the model** — machine-checked transitions at minor-unit granularity with ordered cumulative-quota payout |
| A widely accepted benchmark rate for the industry | **No** — market coordination + regulator problem; price without it does not self-adopt |
| Jurisprudential acceptance by sharia councils | **No** — the proof shows computational correctness, not fiqh judgement |
| Banks actually stopping LIBOR/SOFR proxies | **No** — liquidity, hedging and contracts shift for institutional, not formal, reasons |

**Claim.** *Here is a machine-checkable proof that a defined ownership economy
can clear, conserve, and distribute without an external interest-rate
benchmark — the missing mechanism behind the 50-year problem.*

**Not claimed.** *"I solved the 50-year problem."* That extends beyond any formal
artifact; the remaining three items are out of scope and belong to institutions and
people.

## Relationship to earlier economics

General-equilibrium existence with household ownership of production is
classical: see [Arrow and Debreu (1954)](https://doi.org/10.2307/1907353) and
[McKenzie (1954)](https://doi.org/10.2307/1907539). This repository does not claim
to have first discovered the possibility of valuation without a primitive loan.
Its contribution is the explicit formal development, connected ownership-market
extensions, sensitivity results and bounded institutional applications. No
first-ever priority conclusion is certified by the source/axiom audit.

## Original foundations module: what is proven

The original `GEOverlap.lean` retains its 25 headline theorem audits. The new
89 modules in `formal/` extend it; the original source and historical seal are
preserved unchanged.

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
- It is a **mathematical-foundations and bounded-execution** result. Specified
  institutional rules are modeled, but empirical institutional performance,
  legal enforceability and Shariah (jurisprudential) approval are not established.
- It establishes **existence and coherence**, with conditional uniqueness and
  sensitivity in additional specified classes. The bounded funding/protection/
  ledger applications now address selected accounting and control rules, not
  the complete safe-claim, liquidity, screening, monitoring or distress functions
  of debt. Equilibrium existence alone does not establish those functions.
- Full payoff rank is not the same as ruling out a certain portfolio. The broad
  class needs no supplied lending benchmark; narrower risky controls and trading
  restrictions retain their own assumptions. Discount weights, time preference
  and potentially implied safe returns are not abolished.
- Still open: the full Sonnenschein–Mantel–Debreu *surjectivity* result (realizing
  an arbitrary continuous Walras `z` as the aggregate of rational households; the
  non-uniqueness *upshot* is witnessed above, and both formalizable directions —
  function-level realizability and the rational-demand aggregate excess demand —
  are machine-checked in Stages 233/239, but the multi-household ray construction
  is a separate, genuinely hard program). *Incomplete-market* (GEI) sequential
  equilibrium also remains open. Decreasing-returns production with profit-share
  distribution and a money object are now closed in Stages 232/236/238/248;
  *monetary* time value beyond the money-object premium needs further modeling.

## Verify it yourself

Requires Lean 4 (`v4.35.0`). Exact dependency revisions are pinned in
`lake-manifest.json`; see `NOTICE.md` for attribution. The source/log audit uses
only Python 3.11 or newer and does not install tools or rebuild accepted proofs:

```sh
python3 scripts/verify_release.py
```

This checks source/log hashes, import closure, declaration/axiom correspondence,
package pins and the independent exact escrow controls. A fresh kernel build,
when you choose to run one with sufficient disk/memory, is separate:

```sh
lake exe cache get              # fetch the Mathlib build cache
lake build                      # build foundation and extension libraries
```

- `GEOverlap.lean` — the full development.
- `AXIOM_AUDIT.txt` — the axiom audit (every theorem: `[propext, Classical.choice, Quot.sound]`).
- `SEAL_GND.json` — historical foundations snapshot, not the latest gap ledger.
- `formal/` — accepted productive-ownership extension sources.
- `evidence/verification-manifest.json` — portable module/stage/hash inventory.
- `evidence/axioms/` — clean retained extension compiler/axiom logs.
- `tests/primary_escrow_controls.py` — independent exact specification controls,
  not a proof of implementation refinement or observed economic performance.
- `runtime/` — original-byte SQLite adapter, Lean transport and backend controls;
  portable launch helpers are separate from the kernel-checked proof core.
- `evidence/controls/connected_witness.json` — exact complete economic-example
  initial/final records and requests, with retained execution receipts.

## Author

Shehzad Ahmed — ORCID [0009-0007-3538-6811](https://orcid.org/0009-0007-3538-6811).
