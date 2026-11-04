# What has been constructed, proved and tested

As of 4 November 2026. The project has progressed from benchmark-independent
valuation to a connected, conditional theory of ownership markets and selected
funding institutions. It is not merely a proposal to set an interest-rate symbol
to zero. It also is not a completed operating financial system.

## The wider picture

The book asks how an economy organized around productive participation could
provide the useful functions bundled inside debt. The focused mathematical paper
constructs valuation and equilibrium mechanisms. The seven ESC papers address
institutional design; simulations test specified rules and trade-offs. The
formal applications begin connecting economic rights to resource-conserving
execution. Each contributes something different.

The resulting architecture makes four questions explicit: **who can act, on what
evidence, with whose resources, and who bears the consequences**. Its potential
is to make ownership finance inspectable and testable, not to make real losses,
conflicting interests or institutional power disappear.

## Completed mathematical results

“Verified” below refers to the stated formal theorem under its assumptions, not
an approval of an entire institution. Only the 4.35 foundation and Stages
183–220 accepted dependency chain, Stage 222 frontier and Stage 224 strict/stress/reserve extension are included in this repository release. Earlier
benchmark/diffusion results are described as programme context, not newly
released or independently rebuilt by this package.

| Part | Established achievement | Boundary / what does not follow | Evidence route |
|---|---|---|---|
| Valuation mechanism | Productive payoffs and probabilities enter household valuation; resources, preferences, supply and permitted trades determine equilibrium. No externally supplied lending benchmark is necessary in these constructions. | Time preference, state weights and discounting remain. A valuation identity alone does not determine all untraded claims. | Focused paper; original foundations and ownership extension. |
| Fixed-date example | The specified one-share economy clears at about 17.073872, distinct from its expected payoff of 13.7. Actual household optimization supports the holdings. | A solved model, not an estimated market price or every economy. | Current focused manuscript; not exported in this release. |
| Timing dependence | Changing which outcomes settle earlier/later can change prices and holdings while preserving both marginal distributions. Benchmark global ordering and broader local comparisons are established. | No universal sign; price-neutral reallocations can occur. | Earlier benchmark/comparative-statics programme, including final Stage 109 bridge. |
| Continuous-time construction | A positive valuation deflator and a scoped literal-holdings, process-level self-financing bridge are established. | Supplied dynamics, integrability and strategy domains; shorting and implied safe returns differ from the restricted household example. Not all semimartingale markets. | Accepted Stage 92; current supplement, not copied into this release. |
| Classical GE machinery | Fixed-point, maximum and equilibrium machinery supports specified preference, asset-market and date-event constructions. | Classical economic existence is not a new discovery; the original bounded and CRS constructions retain their conditions. | `GEOverlap.lean`, 25 original headline audits. |
| Actual broad ownership existence | Heterogeneous finite CRRA households, nonnegative overlapping payoffs, actual global optimization, positive prices/current consumption, exact clearing, and zero initial asset holdings are connected. Artificial portfolio caps and initial-share floors are removed. | Positive current resources and future income/weights/curvatures, positive supply and full column rank remain; technology/payoffs are supplied. | Stages 183–189; `CRRAOwnershipLimit`. |
| Actual multiplicity | A heterogeneous full-rank ownership economy has equilibria at `(2,1)` and `(3,1)`, with global optimization checked. | Universal price uniqueness for the broad class is false, not an unfinished proof. | Stage 191; `OverlapMultipleEquilibria`. |
| Conditional actual uniqueness | Around a supported no-net-trade reference, sufficiently small admissible joint primitive changes have exactly one actual equilibrium, excluding alternative actual equilibria of each admitted economy. | Local in primitive/reference data; not arbitrary remote or net-trading reference economies. | Stages 192–201; `NonlinearPhysicalBoundary`. |
| Boundary sensitivity | Unique tangent responses and a tangent-input Lipschitz bound connect to actual one-sided Hadamard price/holding responses, including simultaneous weak ownership corners. | Genuine kinks need not have ordinary derivatives. No universal global nonlinear two-shock Lipschitz or numerical-radius certificate. | Stages 199–201; `TangentMarketExistence`, `TangentSolverStability`. |
| Joint primitive changes | Resources, independent incomes, state weights, productive payoffs, ownership/supply and curvature enter the connected local response theory. | Changes must remain admissible; zero payoff entries impose relative/tangent restrictions. | Stages 195–201. |
| Proportional ownership certificates | Positive denomination preserves affordable competitors, optimality, equilibrium and statewise distributions. | A bounded certificate/sukuk application, not every sukuk contract, title, liquidity or legal/religious approval. | Stage 203; `OwnershipCertificates`, 29 endpoints. |
| Funded mutual protection | Explicit benefit caps, proportional exhaustion, residual ownership, productive backing and current-cost allocation conserve available resources. | Does not prove actual contribution demand, joint pool/ownership clearing or complete catastrophe coverage. | Stage 204; `FundedProtection`, 25 endpoints. |
| Supplied compute enterprise | Physical bottlenecks bound output; funded costs generate net receipts connected to actual ownership valuation and settlement. | Inputs, demand and operating policy supplied; no automatic fundraising, optimal scale or profitability. | Stage 205; `EnergyComputeOwnership`, 21 endpoints. |
| Dated funding | Construction plus the exact prefix-deficit buffer is necessary and sufficient for affordability along each supplied operating path. Terminal cash reconciles. | Positive terminal profit alone is insufficient. Omitted shocks/costs or delayed receipts can invalidate the cashflow premise. | Stage 207; `FormationLedgerCore`, `FormationLedgerBridge`. |
| Distribution ledger | Eight admitted operation types preserve stock/cap, funded claims, reservations and recorded cash through finite histories. | Abstract rules, not source refinement, authenticated wallets, durable storage or custody truth. Allocation policy is a premise. | Stage 207, part of its 39 endpoints. |
| Integer-lot inheritance | A divisible optimum/equilibrium inherits grid optimality/clearing when actual endowments, supply and holdings are already commensurate. | No costless rounding or general discrete-market existence theorem. | Stage 207. |
| Primary escrow lifecycle | Consented settled subscriptions fund a fixed issue; close covers construction plus reserve; gates control release; active ownership reconciles; cancellation refunds remain affordable and cannot repay the same entitlement twice; disputes pause named actions. Released operating cash meets the imported buffer criterion. | Stage 209 alone supplies price/plan, with no fees/partial draws or custody/title/liveness proof. Later formation/executable extensions are listed below. | Stage 209; `PrimaryEscrow`, `EscrowFundingBridge`, 32 endpoints. |
| Voluntary primary formation | Actual household demand and price-taking issuer participation support funded formation iff demand at the cost-covering floor covers supply; formed price and holdings are unique in the stated class. | One fresh fixed-scale issue and supplied operating plan. Independent positive future incomes and arbitrary positive CRRA curvatures are covered; not every project can raise money. | Stages 211/213; 103 endpoints across six modules. |
| Actual choices to reached escrow | Actual optimal holdings/consumption and supplier participation connect to a reached funded/released state for arbitrarily many finite buyers when the actual holdings fit natural lots. | Evidence supplied; exact compatibility, not arbitrary rounding or a general discrete-market equilibrium. | Stages 212/214; 24 endpoints. |
| Financeability frontier and safe reserve window | Same-supply formed plans have identical actual prices and holdings when household primitives/payoffs are fixed. Formation and dated affordability hold iff required buffer <= reserve <= issue proceeds minus construction and outside option. | Supplied plan and paths; changing payoffs or scale is a new economy. Cash-path safety alone does not establish terminal distribution compatibility. | Stage 222; `FinanceabilityFrontier`, seven endpoints. |
| Strict voluntary participation | Strict issuer entry iff actual demand at the funding floor strictly exceeds supply. Each subscriber strictly gains over zero investment iff its actual holding is positive; some positive subscriber exists. A supplied construction-six variant strictly benefits its issuer and both subscribers. | Specified outside options and fixed-scale plan, not universal welfare. The original construction-seven persistent fixture remains unchanged. | Stage 224; `StrictPrimaryParticipation`, seven endpoints in the joint module. |
| Cashflow stress tolerance | An adverse cumulative-receipt gap bounded by epsilon raises minimum reserve by at most epsilon; a two-sided bound gives a reserve Lipschitz bound. Stress reserves combine with the actual funding ceiling. | Supplied aligned dates/paths; conservative stress window is sufficient, not necessary for a loose bound. Payoff or settlement changes require revaluation. | Stage 224; `CashflowStressReserve`, seven endpoints in the same module. |
| Exact executable reserve certificate | Signed-integer functions return the least affordable budget and first negative prefix. Any positive currency quantum decodes exactly to real cash safety. Successful certificates compose with strict actual formation. | Exact representation, not rounding, truthful forecasts or real custody. Parser/IO remain tested. | Stage 224; `ReserveCalculator`, nine endpoints; 566 exact runtime comparisons and seven malformed rejections. |
| Integer money | Accepted natural-number money operations decode to the real-valued lifecycle under a positive currency quantum. | Forward refinement under exact representation; no general rounding or fee allocation theorem. | Stage 215; 25 endpoints. |
| Executable dispatcher | The same Lean function used by runtime controls implements admitted steps, preserves full state on economic refusal, and inherits finite-history safety. | Typed pure execution with sound external-check assumptions; role labels are not signatures. | Stage 216; 10 endpoints; 20,053 tested requests. |
| Complete state codec | Full terms, resources, balances, ownership, evidence, time and pauses survive exact numeric encoding; context is bound. | Canonical representation is not authenticity. | Stage 217; 15 endpoints. |
| Atomic API protocol | Version checks, exact payload binding, retained journal/cache, retry/conflict/stale behavior and coherent result/state are proved. | A linearized protocol theorem does not prove a database or distributed consensus. | Stage 218; 25 endpoints; 2,281 requests in retained controls. |
| Complete envelope and recovery | Requests, all journal entries/cached outcomes, stores and results round-trip; serialized execution equals the accepted core; admitted recovery equals fixed-policy replay. | Trusted genesis/check policy; cannot detect a self-consistent replacement history or valid-prefix rollback without external freshness/authentication. | Stage 219; 18 endpoints. |
| Concrete SQLite adapter | Actual version-conditioned all-or-nothing updates, reopening, competing writers and process-exit/lost-response cases pass exact controls. | Tested Python/SQLite, not a kernel proof of database, filesystem, hardware or power-loss durability. Mock evidence; no real funds. | Stage 219; 150 comparisons/reopens, eight writer schedules, six process exits, 13 corruption rejections. |
| Connected economic execution | Two households' unique global optima support the specified formed issue; the actual computed request history preserves their consumption/rights and funded operating paths. Its entire final store is recovered and matched in SQLite. | One exact risky synthetic example; issuer accepts break-even equality. Operating paths are supplied, not actual telemetry or implemented operating-payment event types. | Stage 220; 18 endpoints; five actual commits, five reopens, five cached retries. |

The newer broad existence class does not exclude every certain portfolio merely
by assuming full column rank. Absence of an externally supplied lending
benchmark, absence of a primitive loan, and absence of every synthetic safe
return are different propositions.

## Writing, design, experiments and observation

| Programme part | Completed contribution | Evidence level and remaining boundary |
|---|---|---|
| The Economy We Could Own | Integrated sixteen-chapter reading draft connects ownership, protection, custody, claims, governance and distribution. | Explanatory institutional synthesis; not a theorem that every proposed institution works or final publication production. |
| Seven canonical ESC papers | A connected architecture decomposes valuation, protection, ownership, payments, liquidity, monetary incidence and constitutional integrity. | Substantial design/theory drafts; not a fully deployed replacement for every debt function. |
| Legacy 17-paper corpus | Preserved exploration, model development and evidence. | Historical material includes superseded universal scalar-kappa claims; these are not revived. |
| Four-stage study | Organized research programme and retained empirical diagnostics; a versioned WP1B merge/coding repair is complete. | Corrected associations remain descriptive; WP1C identification is separate. Data volume does not certify an entire system. |
| Connected ESC simulations | Specified custody/investment/protection/liquidity mechanisms were tested together, with explicit trade-offs. | Synthetic, supplied rules and parameters; not observed welfare effects or universal superiority. |
| Contract-comparison cadCAD work | Twelve scenarios and 1,200 terminal paths compare allocations under paired physical shocks. | Uncalibrated comparison; ownership reallocates loss rather than preventing physical loss. |
| Tested ledger reference | Stage 206 has 24 unit tests and 48 application checks, including fees/rounding, two-phase withdrawals and replay. | Offline tested code, not formally refined to the published abstract transition system. |
| SpringFish / evidence architecture | Claims-admission states, authority and contestability make evidence and incidence inspectable. | Versions, recorded observations and simulations remain distinct; no universal truth oracle or end-to-end deployment certification. |
| HAMBA | Livestock identity, evidence, marketplace and partner workflow design, prototype and prospective field protocol. | Pre-pilot; simulated paths are not observed farmers, financed animals or measured poverty effects. |
| Bangladesh infrastructure work | A dated case distinguishes installed/usable capacity, accounts and missing contractual evidence. | Does not by itself identify the entire causal loss-to-currency chain or validate every model equation. |

The mathematical manuscript and its existing supplement now explicitly include
selected formation, financeability, strict-participation and reserve results
(Stages 223/225 document revisions). The public source update does not publish
the manuscripts, private data or a new journal upload package. A matching
Word/replication/submission package remains a separate document task.

## The present affirmative claim

> We have constructed and machine-checked defined productive-ownership markets
> and connected valuation, equilibrium, sensitivity, backing, dated funding and
> settlement mechanisms without supplying a lending benchmark. We have also
> developed institutional designs and specified simulations that make the
> allocation of authority, resources and loss explicit. The completed results
> provide a substantial conditional foundation for ownership finance. Actual
> voluntary cost-covering formation and a proved pure executable funding core
> are now included, with a bounded persistent demonstration tested against the
> same results. Authentication, real-world custody and demonstrated social
> outcomes remain distinct achievements to establish.

This is a mathematical and structural contribution to the valuation/benchmark
part of the longstanding Islamic-finance challenge. “The 50-year problem” is
not a single historically established theorem with a single agreed solution
criterion. Classical state-price and general-equilibrium predecessors prevent
treating all non-loan valuation as a first-ever discovery.
