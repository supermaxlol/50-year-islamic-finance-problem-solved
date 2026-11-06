# Production, welfare and frontier note — Stages 228–249

Sealed 2026-11-06. Repository release: **90 Lean modules, 918 retained
declaration-audit endpoints** (previous: 70 modules, 871 endpoints). All retained
logs are clean and use only `propext`, `Classical.choice`, `Quot.sound`.
SHA-pinned sources and clean audit logs are verified by
`scripts/verify_release.py` (retained evidence, not a fresh cold rebuild).

## What is machine-checked

- **Production capstones (228–232, 236, 238, 245, 248).** Endogenous
  profit-maximizing production joined to clearing equilibrium with profit income
  in household budgets (228); production-price fixed point and micro-founded
  production equilibrium (230); decreasing returns and a money object (232);
  profit-income production capstone — budget lower-hemicontinuity at general
  wealth, demand from utility maximization over profit-augmented budgets, and
  clearing with production (236); endogenous scale firm `η(p) = max(0, p·v)·v`
  (238, folded into stage 239's file — see ledger note below); a reusable
  `ProductionEconomy` structure folding `z − η` into Gale–Nikaido–Debreu (245);
  continuous firm supply over a production set via the general Berge engine
  (248). The general production-set firm (248) is the proper completion of the
  one-parameter scale firm (238).
- **Welfare theorems (234, 235, 237, 246).** Micro-founded multi-household
  equilibrium (234); first welfare theorem, core/coalition-proofness, uniqueness
  (WARP) and money premium (235); second welfare separating-hyperplane core —
  a nonzero supporting price for an efficient aggregate (237); and the economic
  wrapper from preferences — convex/open aggregate better set, efficiency to
  exterior point (246).
- **Upstream engines (240–244).** Aggregate-set lemmas (convex/open under finite
  Minkowski sum, 240); Walras' law from local non-satiation (241); set-valued
  Gale–Nikaido–Debreu for convex-valued demand correspondences (242); general
  Berge maximum theorem (243); price-vector extraction and separating price
  (244). These remove the strict-concavity crutch across the stack.
- **Demand theory (233, 239, 247, 249).** Function-level SMD realizability
  (233); rational SMD — utility-maximizing households generate continuous Walras
  excess demand with a clearing price (239); Nash bargaining existence and
  uniqueness (247); expenditure minimization / Hicksian demand (249).
- **Formation (229, 231).** Simultaneous primary formation (229); interacting
  multi-issue formation (231).

## Boundaries (what is NOT claimed)

- **Full Mantel surjectivity is open.** Stages 233 and 239 bracket the
  formalizable directions; realizing an arbitrary continuous Walras `z` as the
  aggregate of rational households needs the multi-household ray construction
  (integrability / Slutsky symmetry) and is not closed.
- **Genuinely sequential incomplete-market (GEI) equilibrium is open.**
- Stages 246/248 re-prove the stage-244/243 engine lemmas locally (self-
  contained files; engine object files could not be produced outside the
  `harfe/` root). The proofs are identical.
- **Ledger note:** stage 238's theorem lives inside stage 239's five-theorem
  file (`BudgetLHCGeneral.lean`); the sealed module is `BudgetLHCGeneral`
  (stage 239). A separate 238 folder records the four-theorem snapshot for
  audit history.

## Verify

```
python3 scripts/verify_release.py
```

Expect `PASS: 90 source-identical modules; 918 retained declaration audits`.
