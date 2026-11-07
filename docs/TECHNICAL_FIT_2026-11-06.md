# Where this mechanism fits in the real world — evidence map

This is the evidence that makes the bigger picture more than romance; read the memos to see the failure modes, not the success stories.

Companion to *One maths for the last 50 and the next 50* (`README.md` top, and `BIGGER_PICTURE_2026-11-06.md`). The thesis says mechanism is proved; this file says where that mechanism plugs in.

Each memo keeps the same honest boundary: the math closes the *settlement/allocation/conservation* sub-problem; law, custody, legitimacy, fiqh, and geopolitics stay outside the proof.

- A. Bhutan through H. Post-wage households: the place-specific fit memos.
- 17–37: systemic arrears, payment rails, cross-border settlement.
- 38–69: climate, pensions, healthcare, food, shipping, water, spectrum, housing, and related arrears family — same certificate+escrow+reserve shape, same external gaps.
- Z: cross-memo failure matrix + honest bounds (oracle truth, timing, capital source, governance trigger) — read Z first if you have 2 minutes.

## Executive tables — read these first

These three tables compress the 69 memos into a checkable picture. Everything below repeats them as evidence; these tables are the claim.

### Table 1 — Place mapping: real problem → does the math solve it? → still missing

| Case | Their real problem | Does your math solve it? | What's still missing |
|---|---|---|---|
| Bhutan (DHI, hydro→crypto) | Surplus energy liquid in BTC, volatile, treasury-concentrated, no household leg | **Yes, settlement leg** — certificate/ownership-payout encodes "nation consumes from compute yield"; budget binds | Political will, custody, volatility governance, statute |
| Iran (energy→mining, sanctions) | SWIFT cut off, no offshore asset for imports | **Partial** — internal clearing in BTC/compute credit in defined domains | Sanctions law, counterparties, confiscation/enforcement — not a cloak |
| Norway SWF / Alaska Permanent Fund | Oil fund huge, no direct citizen dividend; AK dividend political | **Yes, mechanism** — generalises permanent-fund logic to compute/energy stack; dividend = pro-rata certificate | Constitutional/statutory fund protection + custody |
| Web4 / agentic economies | Agents trade at machine speed, no bank loop; debt leverage loops | **Strongly** — escrow/dispatcher/integer protocol + conservation are the machine-checkable primitives | Trust, consensus, MEV, oracle, legal standing of agents — component, not constitution |
| Russia (frozen reserves) | USD/EUR access blocked; needs alternate settlement | **Indirect** — conserved ownership clearing, no external benchmark anchor | Compliance, counterparties, trade capacity — not created by math |
| Islamic finance | Riba ban; murabaha/tawarruq reproduce cash-flow shape, PLS marginal | **Directly (technical)** — proved escrow/payout/conservation/formation with no interest benchmark anywhere | AAOIFI/IFSB certification + counsel wrapper — not a fatwa |
| Afghanistan (riba ban) | Ban declared; no trusted clearing rail | **In principle** — same settlement engine for no-riba | Banking access, enforcement, sanctions, ledger capacity — political |
| "When AI does all work, who owns?" | $Y=f(K,L)$, if $L\to 0$ then wages $\to 0$; textbook breaks | **Directly (theory)** — overlapping-payoff + certificates + profit-share + clearing with zero labor input demonstrated | Legislature, sovereign-dividend design, capture mitigation |

**Unified:** conserved asset-linked value; no external benchmark dependency; machine-enforceable/auditable settlement primitives. **Not:** a statute, sanctions immunity, fatwa, bank, constitution, demand-side module, or allocation/monopoly fix.

### Table 2 — High-tractability fits (ranked)

| Domain | Pain | Missing piece | Math fit |
|---|---|---|---|
| U.S. Treasury clearing T+1 | Collateral, credit-extension | Strict atomic swap | High — integer conservation |
| Energy OTC (power/gas/carbon) | Fails, disputes, buffers | Stress reserve for shortfalls | High — built-for-this |
| Carbon credits | Double-counting | Single-use retirement proof | High |
| Supply-chain finance | Duplicate financing, doc fraud | Integer pledge, escrow FSM | High |
| Reinsurance / cat | Claim disputes, solvency | Reserve adequacy proof | High |
| Digital-asset post-trade | Exchange blow-ups, finality gaps | No state creates tokens | Med-high |
| Municipal/SME bonds | Small-issuer cost | Atomic clearing at scale | Med-high |
| Shariah sukuk (smart) | Council discretion, custody | Conservation + profit/loss rule | High — policy, not math |
| Edge compute (Akash/iExec) | Trustless slot bank | Provable escrow with citizen cap | High |

### Table 3 — 14 research + 6 named additional fits (one-line match)

| # | Domain | Exact pain | Why the math is the piece |
|---|---|---|---|
| 1 | Intl. arbitration (seat) | Contestable awards, fragmented enforcement | Audit trail from award → payable claim |
| 2 | Islamic tahkim | Tamperable evidence PDFs | Verified step certificates; kills double-claim |
| 3 | Gulf SWF crisis transfers | Opaque cross-border pooling | Net-settled DvP certificates |
| 4 | BRI project finance | Multi-jurisdiction reconciliation chaos | Single conserved ledger; law still external |
| 5 | SDR-linked bonds | SDRs trapped, conversion costs | Tokenised SDR certificates; IMF consent external |
| 6 | CLS FX (PvP) | Pre-funding haircut, liquidity strain | Atomic PvP without parallel pre-fund — research stage |
| 7 | Nigeria e-Naira | Fragmented ledgers | Single-clearing invariant via conservation |
| 8 | Kenya M-Pesa↔interbank | 36–48h lag vs instant mobile | Real-time dual-rail match |
| 9 | EU wholesale digital euro | TARGET2 latency, dual-track noise | Programmable wholesale settlement state; governance external |
| 10 | Brazil Pix cross-border | Domestic-only, FX chaos | Pix-compatible certificate bridge |
| 11 | MAS Singapore secure bonds | Proprietary code, post-audit | Protocol-level conservation replaces post-hoc audit |
| 12 | APAC green-bond rail | Dual-escrow netting inconsistency | Cross-border netting, same invariant |
| 13 | mBridge (CBDC interop) | Desynchronised rails, bridge drain | Atomic multi-currency settlement; states hold keys |
| 14 | SWIFT GPI PvP | Visibility without atomicity | Real-time PvP netting; Swift/CLS participation external |
| 15–20 | BD HIES, Ringgit Waqf, PK IMF tranche, PK export, AFDL corridor, AFR sick-funds | Leakage/ghost, waqf misallocation, tranche leaks, hawala split, drought triggers | Conservation + escrow + stress acts — regulator/fatwa/ID/fraud-response external |

**Highest-upside cluster by invariant strength:** CLS-style atomic PvP + mBridge (big dollar flow, clean invariant win) — still needs the institutions to adopt them.

## A. Bhutan (DHI, hydro→compute)
**Case (public view).** Bhutan routes surplus monsoon hydro through Druk Holding & Investment into computing/mining contracts; public reporting shows a sovereign BTC reserve and drawdown to fund Gelephu and payroll. Volatility is real; income is concentrated in the treasury; households see no proportional claim.
**Missing piece.** A distributive leg that binds citizen equity (or certificates) to the automated yield, with conservation and stress reserves.
**Problem.** Sovereign surplus must become a citizen-stream without fiscal leakage or policy blow-ups.
**Math mechanism.** Ownership-certificate layer over the autonomous compute/energy stack; ordered-quota payout; strict participation check; financeability-frontier reserve window (Stages 222/224/226). State sells compute → receipts enter enterprise pool → certificates pay out pro-rata → national budget binds.
**Does it solve it?** At the *mechanism* level — yes. Distribution rule + conservation + no held-liability. Does **not** manage market volatility or custodial risk or create the legal corporate/fund wrapper.
**Still missing.** Political will; sovereign compute custody; distribution statute; volatility governance; backup balancing.
**Success metric.** Representational pilot ("$1 of verified compute yield → 1/N certificate dividend") audited by external $3rd party; zero conservation deltas; distribution reach matches parliamentary mandate; treasury audit clean.

---

## B. Iran (energy→compute under sanctions)
**Case (public view).** Endowed with oil/gas and subsidized electricity; attempts compute-settlement under U.S./EU/EMR sanctions; uses offshore vehicles and BTC for import settlement. Sanctions block banking, not physics.
**Missing piece.** A complete internal clearing economy that settles imports through conserved asset claims without SWIFT.
**Problem.** Access to external credit/banking cut; need internal asset that clears.
**Math mechanism.** Connected conserved clearing, profit-augmented household budgets, no external benchmark; escrow + dispatcher can authenticate and move claims internally; certificate-bounded settlement.
**Does it solve it?** Partially — internal settlement rails close. It contains **no tools** for evasion compliance, counterparty trust, or confiscation risk. Use only as "defined-economy settlement layer," never as cloak.
**Still missing.** Counterparties; legal standing; sanctions exposure; exchange capacity; internal task demand.
**Success metric.** Pilot in defined *domestic* market (state compute consumers buying capacity) with audited conservation; zero unresolved predicates; counsel-signed risk disclaimer.

---

## C. Norway SWF / Alaska Permanent Fund
**Case.** Norway's GPFP invests oil royalties, ~7% budget rule, citizens see no direct dividend; Alaska pays annual dividend (POMV ~5% of fund income) — politically contested each session.
**Missing piece.** Verifiable automated-dividend pipeline replacing political votes with self-executing, auditable claims.
**Problem.** Dividend politically fragile; citizens own diluted stakes but link is weak.
**Math mechanism.** Same architecture as (A) — certificate claim over autonomous productive stack with conservation; stress-reserve keeps dividend reliable through shocks.
**Does it solve it?** Mechanism — yes; **substitute for law — no**. Norway's protection is constitutional budget rule, not math.
**Still missing.** Statutory + constitutional text; allocation advisory board; custody; tax treatment.
**Success metric.** Legislation piloting certified "compute dividend" certificate; auditable distribution; survival across a legislative cycle; fund governance intact.

---

## D. Web4 / agentic economies
**Case.** Autonomous agents move value at machine speed using MCP/x402/etc.; risk: leverage/loop/attack at sub-human latency with no bank in the loop.
**Missing piece.** Hard invariant that conservation holds even for hostile agents + provable single-use obligations.
**Problem.** Machine agents can create unbounded pseudo-debt and slip rounding under latency stress.
**Math mechanism.** Conservation + ordered cumulative-quota payout + stress reserves + binding-budget clearing. Machine rules cannot authorize non-conserved state transitions.
**Does it solve it?** Partially — halts *accounting layer* failures and many leverage abuses. It does **not** stop front-running, oracle corruption, or social engineering of agents.
**Still missing.** Consensus, MEV mitigation, oracle construction, indemnity, legal standing of agents.
**Success metric.** Zero unexplained drift in production agent traffic; invariant-violating transactions rejected at mempool/assembly; auditor sign-off on stress-file.

---

## E. Russia (sanctions, frozen reserves)
**Case.** Foreign-exchange reserves frozen; payment rails blocked for exports/imports. Search for gold/renminbi settlement.
**Missing piece.** Internal clearing and alternative asset claims for domestic/commodity settlement.
**Problem.** Cut off from global bank settlement; needs closed-flow internal claims.
**Math mechanism.** Conserved ownership clearing with productive payoffs + profit-share; no external numeraire; escrow/dispatch for internal commodity-asset flows.
**Does it solve it?** Indirect/partial — internal settlement leg only; exports, imports, counterparty, enforcement outside scope.
**Still missing.** Partners, logistics, law, foreign trade, compliance.
**Success metric.** Pilot commodity↔compute↔certificate in a closed defined economy; audit trail matches conservation; no reliance on external rails for audit subset.

---

## F. Islamic finance (riba prohibition)
**Case.** Classical riba banned; conventional sukuk synthetic-interest-laden; Islamic banks use murabaha/tawarruq workarounds.
**Missing piece.** An interest-free, asset-backed, executable instrument that actual enforcement can deploy.
**Problem.** Market demand for no-riba instruments; no audited, machine-executable compliant vehicle.
**Math mechanism.** Formation + escrow + conservation/payout (no interest benchmark anywhere); certificates are equity/profit-share, exactly mudarabah/musharakah formalized.
**Does it solve it?** Technical — yes. **Jurisprudential — no**; fiqh-body sign-off is external.
**Still missing.** AAOIFI/IFSB certification; scholar endorsement; legal wrapper.
**Success metric.** Pilot sukuk certified by recognized sharia board; conservation audit published; zero ribawi states in certificate ledger.

---

## G. Afghanistan (state-level riba ban)
**Case.** 2021 decree banning interest; no operational non-riba financial infrastructure; sanctions make it acute.
**Missing piece.** Working no-riba clearing engine acceptable to local authorities and religious legitimacy.
**Problem.** Ban declared, but no execution rail; liquidity dry; yuan lacks rails.
**Math mechanism.** Same as (F) — integral escrow/contract protocol; settlement in conserved asset-linked units.
**Does it solve it?** In principle yes — a no-benchmark clearing economy. **Power decides**: whoever runs the ledger decides legitimacy, not proof.
**Still missing.** Enforcement engine; operator; legitimacy; banking access; telecom/electricity.
**Success metric.** Municipal pilot with audited distribution; conservation invariant held; local authority sign-off (math cannot supply this).

---

## H. "When AI does all work, who owns?"
**Case.** Production function Y = f(K, L) with L → 0 ⇒ MP_L → 0 ⇒ wages collapse; entire share shifts to K. Demand side collapses with it; classic paradox of abundance.
**Missing piece.** A distribution law *within* the model where ownership of automated production sustains households.
**Problem.** Classical framework cannot express non-labor subsistence equilibrium.
**Math mechanism.** Heterogeneous overlapping payoffs + ownership certificates + CRRA households surviving on asset yields; clearing with zero labor input demonstrated.
**Does it solve it?** Yes — at the *model* level this is exactly the question asked: **it closes the equation**. Implementation/legitimacy outstanding.
**Still missing.** Statute for citizen dividend; political mandate; capture mitigation; sovereignty governance.
**Success metric.** Formal demonstration in a defined economy: presence of households with zero labor income, positive consumption, conserved certificates
 and equals back to real production yields — reviewed by a trained economist/philosopher at board-of-governors level.

## Appendix B — additional case memos (14 research + 6 named)

Every entry keeps the same rule: math closes the settlement/conservation leg; law, custody, legitimacy and geopolitics stay external.

### 17. International arbitration awards (UNCITRAL-based)
**Painter gap.** Awards can be challenged for set-aside on narrow procedural grounds; enforcement is fragmented across seats; debtors re-litigate payment.
**Problem.** Certainty that the award is owed, and when, without a court standing in the way of actual cash movement.
**Math mechanism.** Atomic, immutable award-recording certificate; enforcement becomes conservation-preserving transfer from debtor escrow to creditor. Audited pipeline proves funds never move or split illegitimately.
**Does it solve it?** Settlement leg — yes. Merips and seat-law — no.
**Adoption barrier.** New York Convention party acceptance; seat courts; arbitral institution cooperation.
**Success metric.** Pilot at a leading institution; zero conservation deltas across 500 awards; enforceability sign-off by counsel.

### 18. Islamic tahkim (sharia-compliant arbitration)
**Painter gap.** Tahkim evidentiary standards demand chain of custody; manual notarized PDFs are forgeable.
**Problem.** Trusted evidential chain across private religious adjudication.
**Math mechanism.** Certified evidentiary step certificates — each decision event binds funds/performances atomically; conservation prevents double-use of an evidentiary claim.
**Does it solve it?** Evidence-binding leg — yes. Walāyah authority and fatwa granting — external.
**Adoption barrier.** Sharia council endorsement; court recognition; party consent.
**Success metric.** Pilot tribunal sign-off; zero contested conservation states; council certification.

### 19. Gulf SWF inter-fund crisis transfers
**Painter gap.** Cross-border repo/pooling opacity under stress; delayed notice; bilateral risk.
**Problem.** Portable, net-settled inter-fund liquidity across Abu Dhabi / Riyadh funds with no settlement-cycle drag.
**Math mechanism.** Net-settled inter-fund certificate transfer with atomic delivery-versus-payment; conservation ensures total assets conserved across funds; no external benchmark required.
**Does it solve it?** Netting leg — yes. Crisis policy — no (irreversible asset provision still discretionary).
**Adoption barrier.** Fund governance boards; regulator consent; custody provider.
**Success metric.** Pilot crisis-sim: two funds, net-settle in <1 hour with zero conservation delta; external audit sign-off.

### 20. BRI cross-border project finance
**Painter gap.** Dozens of jurisdictions, incompatible dispute regimes, reconciliation chaos across layers of escrow.
**Problem.** Single source of payment truth across the corridor.
**Math mechanism.** One conserved ledger across all payment certificates; conservation/global sum invariant identical in all currencies; no external rim-benchmark required.
**Does it solve it?** Multicurrency payment leg — yes. Legal enforcement, corridor disputes — external.
**Adoption barrier.** Host-country acceptance; preferred-lender concordat; cross-border FX conservancy.
**Success metric.** Pilot section (e.g., China→Gwadar) reconciles 100% of payment certificates; external audit confirms invariant; legal review clears bankability.

### 21. SDR-linked world-bank bond settlement
**Painter gap.** SDRs sit in IMF trust; cannot directly fund; conversion costs are punitive.
**Problem.** Turning SDR allocations into productive project funding without loss of value or traceability.
**Math mechanism.** Tokenized SDR certificate with strict conservation; IMF and borrower ledger share one invariant; settlement without conversion bottlenecks.
**Does it solve it?** Unit-integrity leg — yes. IMF consent and quotas — external.
**Adoption barrier.** IMF amendment/approval and custodian; FX risk treatment; board sign-off.
**Success metric.** Pilot commitment; zero SDR creation/destruction in audit; IMF staff sign-off on pilot.

### 22. CLS FX settlement (delegated PvP)
**Painter gap.** Banks lock enormous pre-fund balances; exposure pre-settlement; settlement-capacity constraint.
**Problem.** Risk-free PvP settlement without parallel funding.
**Math mechanism.** Provable atomic PvP netting across PvP set; conservation across legs; no external liquidity benchmark required.
**Does it solve it?** Payment-leg atomicity — yes. Liquidity, bank solvency — no.
**Adoption barrier.** CLS/SWIFT integration; systemic-risk sign-off; prudential rules.
**Success metric.** Internal sandbox: 100k matched trades, atomic settlement, zero unmatched inventory; CLS legal-risk review clear.

### 23. Nigeria e-Naira intrabank clearing
**Painter gap.** Fragmented per-bank ledgers; switching requires post-mortem reconciliation; delay and double-spend disputes.
**Problem.** Single, immutable settlement record for a national digital currency.
**Math mechanism.** Conservation ledger as single clearing source; ordered fee/payout; atomic debit/credit interbank.
**Does it solve it?** Clearing leg — yes. Firewall/runtime integrity, court authority — external.
**Adoption barrier.** NIBSS/CBN integration; bank-side hot swap; ISO 20022 routing.
**Success metric.** 1M simulated clears; zero mismatch; CBN approval for pilot phase-2.

### 24. Kenya M-Pesa ↔ interbank
**Painter gap.** Instant mobile money vs 36–48h interbank settlement; SME liquidity gaps.
**Problem.** Real-time same-value clearing across rails.
**Math mechanism.** Conservation-preserving dual-rail registry; payout certificate matched 1:1 in real time; no manual reconciliation.
**Does it solve it?** Rail-matching leg — yes. Bank charter, Central-Bank of Kenya authorisation — external.
**Adoption barrier.** Safaricom + CBK + bank consortium; ISO 20022 cert.
**Success metric.** Live capture: 1,000 cross-rail transfers settled <500ms with conservation audit; CBK certificate-of-pilot.

### 25. EU wholesale digital euro settlement
**Painter gap.** TARGET2 latency; commercial-bank money dual-track causes reconciliation noise.
**Problem.** Programmable, universal, wholesale settlement in euros.
**Math mechanism.** Conservation invariant embedded in digital-euro wholesale state machine; atomic multi-party PvP/PvP across Eurosystem.
**Does it solve it?** Settlement integrity — yes. Design authority, legal status of digital euro — external.
**Adoption barrier.** ECB Governing Council; legal framework; member-state ratification.
**Success metric.** Successful run in Eurosystem sandbox; full reconciliation; no value-path drift; legal sign-off.

### 26. Brazil Pix cross-border
**Painter gap.** Instant domestic Pix; but cross-border forced into correspondent-banking FX chaos.
**Problem.** Extending instant settlement across borders preserving value.
**Math mechanism.** Pix-compatible cross-border settlement certificate; value-invariant conservation bypassing correspondent banks.
**Does it solve it?** Rail extension — yes. Múltiplas FX and BCB authorisation — external.
**Adoption barrier.** BCB approval; counterparties; correspondent-bank agreement.
**Success metric.** Pilot Pix-LVO at border: 500 cross-border pairs settled; conservation audit; BCB sign-off.

### 27. Singapore MAS secure-bond clearing
**Painter gap.** Proprietary settlement code; periodic reconciliation post-audit; legal dispute over mismatch.
**Problem.** Provably-correct bond settlement under MAS code policy.
**Math mechanism.** Conservation proof embedded in settlement protocol; all cash/securities legs atomic and checksum-audited.
**Does it solve it?** Settlement leg — yes. MAS approval, contract law — external.
**Adoption barrier.** MAS code accreditation; legal recognition of proof-as-evidence; exchange operator.
**Success metric.** Sandbox run: 100k bond pairs settle; zero states with conservation violation; MAS audit sign-off.

### 28. APAC green-bond rail-to-rail settlement
**Painter gap.** Escrow fragmentation; manual netting in multi-jurisdiction green-bond corridors.
**Problem.** Single auditable reconciled corridor for climate finance.
**Math mechanism.** Bond certificate netting across borders with invariant conservation; stress-buffered reserves for project delays.
**Does it solve it?** Netting accounting — yes. MRV of climate impact, referee validation — external.
**Adoption barrier.** Issuers/trust; cross-border FX; accreditation of climate credits.
**Success metric.** Pilot rail VC fund ↔ APAC green bond; zero conservation deltas; external audit clean; ESG verifier signs.

### 29. mBridge — sovereign digital CBDC interoperability
**Painter gap.** Four+ CBDCs with different rails; bridges drain liquidity; settlement timestamps desync.
**Problem.** Atomic, liquidity-preserving multi-CBDC settlement across borders.
**Math mechanism.** Protocol-level atomic net settlement across sovereign ledgers; conservation in all legs simultaneously; no exchange-of-funds required at any point.
**Does it solve it?** Settlement leg — yes. Sovereign authority, FX rails, legal status — external.
**Adoption barrier.** BIS consortium governance; signing HSMs; FX conversion policy.
**Success metric.** mBridge production pilot; multi-CBDC atomic epochs; BIS final report clean on conservation.

### 30. SWIFT GPI PvP settlement
**Painter gap.** GPI provides visibility but not atomic PvP; pre-settlement exposure remains.
**Problem.** Provably safe PvP with no hidden exposure.
**Math mechanism.** Required invariant: no final recording unless both legs settled; conservation on FX leg pairs; no external bank benchmark needed.
**Does it solve it?** PvP atomicity — yes. Liquidity limits, bank solvency, SWIFT deal — external.
**Adoption barrier.** CLS participation rules; SWIFT consortium approval; FX banks.
**Success metric.** Model runs on 1M FX pairs; PvP 100% safe; zero failed-but-booked states; CLS + SWIFT legal opinion.

### 31. Bangladesh HIES cash distribution (internal hook)
**Painter gap.** Government cash-transfer programs leave gaps and ghost recipients.
**Problem.** Auditable, conserved household allocations for domestic subsidy programs.
**Math mechanism.** Escrow FSM + conservation per household; ordered quota; prefix-loss reserve against reported shortfalls; certificate audited against IDs.
**Does it solve it?** Distribution leg — yes. Legitimacy, ID system, fraud response — external.
**Adoption barrier.** Bangladesh Treasury approval; ground ID validation; ministries sign.
**Success metric.** Live pilot with 50k households; conservation invariant held; audit delta <0; Treasury sign-off.

### 32. Pakistan IMF-tranche cash-fare / SFDP
**Painter gap.** IMF tranche disbursement to provinces leaks in transit.
**Problem.** Provably conservation-preserving transfer from IMF release to sub-national spending.
**Math mechanism.** Escrow + conservation ledger; trigger-based release only if countersigned attestation and stress-reserve satisfied.
**Does it solve it?** Settlement/conservation leg — yes. Policy conditionality, governance — external.
**Adoption barrier.** IMF + State Bank + provincial councils; legal authority.
**Success metric.** Audited tranche flow 100% conserved; zero leakage flagged; IMF/Bounsert approval.

### 33. Ringgit Waqf-Sukuk (sharia hook)
**Painter gap.** Waqf principal misallocated; trust-deeds unenforced.
**Problem.** Enforceable, conserved use of awqaf principal in productive Muslim endowments.
**Math mechanism.** Ownership-certificate conservation for waqf assets; ordered allocation; reserve for stress; no external bond rigging.
**Does it solve it?** Custody leg — yes. Fatwa, waqif, trustee law — external.
**Adoption barrier.** Malaysia SC/Labuan/court; Islamic finance council.
**Success metric.** Pilot seed certificate; zero non-zero-balance states; council certified fatwa; trust audit clean.

### 34. Afr agricultural sick-funds (BEMSF)
**Painter gap.** Farmer payout delays; drought trigger disputes.
**Problem.** Conserved, triggered payout for collective climate insurance.
**Math mechanism.** Escrow + prefix-deficit stress-trigger payout; conservation; ordered claim allocation; reserve adequacy.
**Does it solve it?** Fault-contingent payout — yes. Actuary design, drought-trigger truth — external.
**Adoption barrier.** Local insurer/regulator; data sources; consent.
**Success metric.** 500k-claim local pilot in defined season; payout conservation 100%; regulatory approval.

### 35. Pakistan/PCG export settlement (internal hook)
**Painter gap.** Export remittance split between formal banks and hawala; leakage and shadow pricing.
**Problem.** Conservation-preserving export settlement that beats grey channels legitimately.
**Math mechanism.** Public ledger for certified export settlement; FX conserved within state/bank corridor; no external benchmark required.
**Does it solve it?** Payment leg — yes. KYC, SBP approval, hawala politics — external.
**Adoption barrier.** State Bank; PTA/AML; exporter participation.
**Success metric.** Pilot corridor with 1,000 exporters; conservation audit; SBP sign-off; FX leakage down.

### 36. China "One Belt" interbank netting (BRI + RMB hook)
**Painter gap.** Multiple legal regimes and RMB-convertibility friction across corridor banks.
**Problem.** Settled, conserved netting across RMB/local currency legs.
**Math mechanism.** Single invariant ledger; atomic multibank net-settlement; conservation in both currencies; no external conversion fee.
**Does it solve it?** Net-settlement leg — yes. Capital-controls, corridor politics — external.
**Adoption barrier.** PBOC + corridor regulators; FX line authorization.
**Success metric.** Corridor pilot reconciles 100%; conservation clean; regulator sign-off for scale-up.

### 37. World Bank/AfDB climate-fund disbursement
**Painter gap.** Adaptation funds stall; half-spent project receipts; auditor doubt.
**Problem.** Provable conservation of adaptation/mitigation dollars across borders.
**Math mechanism.** Escrow conservation + certificate proof; milestone-triggered release; stress reserve for delivery.
**Does it solve it?** Fund-integrity leg — yes. Project legitimacy, local politics — external.
**Adoption barrier.** Board trustee; host ministry; procurement rules.
**Success metric.** Pilot DM/project; funds conserved 100%; auditor sign-off; impact verifier accepts.


### 38. Climate-debt arrears
**Pain.** Low-income nations pay climate-mitigation and adaptation loans they cannot service; IMF and bilateral swap politics shape relief.
**Workaround.** Ad-hoc debt-for-nature/climate swaps; Paris alignment reform; piecemeal rescheduling.
**Verified-settlement match.** Escrowed climate-finance credits + stress reserve; conservation proves no double-footing of pledges; settlement cannot exist on zero proof.

### 39. Colonialreparations arrears
**Pain.** No enforcement mechanism for historic reparations beyond voluntary donor pledges.
**Workaround.** Grants and bilateral settlements; symbolic apologies; selective programs.
**Verified-settlement match.** Obligation-certificate ledger + escrowed endowment + reserve pool; donor leg cannot cite zero once certified.

### 40. Sovereign-debt distress
**Pain.** Fiscal space collapse; unsustainable external service; market shutdown.
**Workaround.** IMF programmes, restructuring, moratoria, Paris/London Club flows.
**Verified-settlement match.** Sovereign-obligation tokens + escrowed servicing + multilateral reserve absorbs shocks; conservation proves no hidden dilution.

### 41. Healthcare revenue cycle
**Pain.** Billions lost to claim denials, coding errors, late payments, and manual fixes.
**Workaround.** Claims clearinghouses; third-party billing; manual appeals.
**Verified-settlement match.** Conserved patient-service credits; escrowed insurer payments; reserve smooths denial recovery. **Clearing integrity only; medical judgement external.**

### 42. Education-financing arrears
**Pain.** Students default; institutions stall; cross-subsidy collapses.
**Workaround.** Government subsidies; income-contingent repayment; loan servicing.
**Verified-settlement match.** Obligation tokens + escrowed scholarship disbursement + stress reserve for cycles.

### 43. Watershed-service arrears
**Pain.** Upstream free-ride degrades downstream water quality; payments never happen.
**Workaround.** Water trusts; NGO-monitored agreements; voluntary transfers.
**Verified-settlement match.** Ecosystem-service certificate + escrowed upstream payments + restoration reserve.

### 44. Endangered-species offset shortfalls
**Pain.** Developers promise habitat offset; delivery lags; species decline.
**Workaround.** Conditional permits; post-project audits; ecological bonds rarely enforced.
**Verified-settlement match.** Biodiversity certificate + escrowed offset + remediation reserve triggered on late release.

### 45. Migration-quota non-fulfilment
**Pain.** States accept fewer refugees than pledged; displacement limbo.
**Workaround.** UN-managed resettlement pools; unilateral suspensions.
**Verified-settlement match.** Obligation tokens + escrowed donor contributions + interim-shelter reserve.

### 46. Treaty-implementation lags
**Pain.** Signature does not equal compliance; monitoring weak; enforcement late.
**Workaround.** Diplomatic pressure; reporting bodies; soft leagues.
**Verified-settlement match.** Treaty-commitment tokens + escrowed compliance bonds + penalty-release reserve with milestones.

### 47. Common-pool fishery over-exploitation
**Pain.** Race-to-fish; stocks collapse; quotas unenforced.
**Workaround.** Seasonal closures; ITQs; surveillance.
**Verified-settlement match.** Catch-credit tokens + escrowed quota fees + stock-rebuild reserve.

### 48. Fishery-restoration funding lags
**Pain.** Habitat restoration underfunded; grant cycles stall.
**Workaround.** Grant-based funding; NGO campaigns.
**Verified-settlement match.** Restoration-credit ledger + escrowed donor flow + continuous-cash-flow reserve.

### 49. Ocean sulfur-credit defaults (IMO)
**Pain.** Vessels fail to retire required scrubber/carbon offsets; enforcement at ports inconsistent.
**Workaround.** Market-based compliance; flag registry leniency.
**Verified-settlement match.** Sulfur-credit certificate + escrowed purchase guarantee + non-compliance fine reserve.

### 50. Arctic sea-ice finance gaps
**Pain.** Adaptation underfunded; ice-loss response untimed.
**Workaround.** Research grants; incremental adaptation budgets.
**Verified-settlement match.** Resilience token + escrowed climate finance + rapid-response reserve.

### 51. Orbital-debris liability gaps
**Pain.** Operators evade debris-removal duty; costs socialized.
**Workaround.** Insurance pools; ad-hoc settlements.
**Verified-settlement match.** Debris-liability token + escrowed insurance + active-removal reserve.

### 52. Space-traffic-management coordination failures
**Pain.** Conjunction-avoidance fees missed; collision risk rises.
**Workaround.** ICAO-like committees; voluntary coordination.
**Verified-settlement match.** Priority token + escrowed coordination bond + monitoring reserve.

### 53. Semiconductor-export-queue bottlenecks
**Pain.** Export controls create backlog; allocation opacity; corruption.
**Workaround.** Licensing waivers; diplomatic negotiation.
**Verified-settlement match.** Export-credit tokens + tariff deposit escrow + supply-smoothing reserve.

### 54. Rare-earth-supply-chain credit risk
**Pain.** Buyers can't lock down supply; price spikes; arrears.
**Workaround.** Trade-credit insurance; factoring; long-term contracts.
**Verified-settlement match.** Rare-earth-credit certificate + payment escrow + supplier default reserve.

### 55. FDA drug-approval user-fee arrears
**Pain.** Fee delays slow review; sponsors stretch authorisation.
**Workaround.** Statutory fee schedules; waivers.
**Verified-settlement match.** Approval-fee certificate + escrowed payment + accelerated-review reserve.

### 56. Food-aid corruption shortfalls
**Pain.** Aid siphoned; beneficiaries go hungry; audits weak.
**Workaround.** Third-party monitoring; donor appeals; WFP audit.
**Verified-settlement match.** Food-credit tokens + escrowed donor funds + reimbursement reserve.

### 57. Refugee-camp service deficits
**Pain.** NGOs miss shelter/water/health delivery; limbo deepens.
**Workaround.** Emergency draws; appended appeals.
**Verified-settlement match.** Camp-service tokens + escrowed humanitarian pledges + metric-trigger reserve.

### 58. Intergenerational pension shortfalls
**Pain.** Aging vs contributions; payout risk rises.
**Workaround.** Parametric reform; actuarial changes.
**Verified-settlement match.** Pension-obligation token + escrowed contribution pool + smoothing reserve.

### 59. Social-security insolvency
**Pain.** Trust fund depletion looms; benefits cut.
**Workaround.** Tax hikes; benefit trims; Trust Fund acrobatics.
**Verified-settlement match.** Contribution-credit token + response reserve; conservation audit of inflows/outflows.

### 60. Urban informal housing finance gaps
**Pain.** Slum dwellers locked out; rent-to-own collapses.
**Workaround.** Informal settlements; micro-lenders; rental pacts.
**Verified-settlement match.** Housing-credit token + escrowed rent deposit + legal-aid reserve.

### 61. University endowment volatility
**Pain.** Disbursement risk in drawdowns; campuses under-fund equity.
**Workaround.** Spending caps; diversification; borrowing.
**Verified-settlement match.** Endowment-credit certificate + stabilizing reserve; conservation of scholarship flow.

### 62. PPP default (public-private partnership)
**Pain.** Private partner underproduces; renegotiation spirals; service drops.
**Workaround.** Sovereign guarantee; step-in rights.
**Verified-settlement match.** Obligation token + performance escrow + service-gap reserve.

### 63. Water-utility tariff arrears
**Pain.** Mass non-payment; supply continuity threatened.
**Workaround.** Disconnections; subsidies; restructuring.
**Verified-settlement match.** Prepaid balance token + escrowed service-purchase reserve.

### 64. Post-disaster reconstruction payment delays
**Pain.** Governments slow on reimbursements; rebuild stalls.
**Workaround.** Emergency loans; ad-hoc grants.
**Verified-settlement match.** Reconstruction certificate + escrowed relief + damage-assessment-triggered reserve.

### 65. Mangrove/carbon-loss credit gaps
**Pain.** Carbon stock erosion uncompensated; poor audit.
**Workaround.** Carbon market; REDD+ audit; voluntary deals.
**Verified-settlement match.** Mangrove-credit certificate + escrowed buyer deposit + replanting reserve.

### 66. Protected-area in-place financing
**Pain.** Conservation budget chronic shortfall; poaching/drain.
**Workaround.** NGO fundraising; earmarks.
**Verified-settlement match.** Conservation-credit certificate + baseline-funding reserve.

### 67. Public-contract arrears
**Pain.** Government delays crushing suppliers; lawsuits; stall.
**Workaround.** Retainage schedules; progress payments; emergency injections.
**Verified-settlement match.** Milestone-obligation certificate + escrowed payment + late-release reserve.

### 68. Public-transit budget gaps
**Pain.** Fare shortfalls push service cuts; spiral.
**Workaround.** Subsidies; fare hikes; corridor segregation.
**Verified-settlement match.** Service-credit token + fare-box escrow + operations-reserve.

### 69. Child-care subsidy settlement failures
**Pain.** Providers wait months for state payments; families locked out.
**Workaround.** Retroactive reimbursements; state grants.
**Verified-settlement match.** Childcare-credit certificate + provider escrow + release-timing reserve.


## Z — Cross-memo failure matrix & honest bounds

Every memo keeps the same rule: **math closes the settlement/conservation/allocation leg; everything else is external.**

| Case(s) | Timing (when value clears) | Oracle trust needed | Capital source — does it pass Stage 222 frontier? | Governance / authority risk | Fails if |
|---|---|---|---|---|---|
| A. Bhutan hydro→compute | Monthly royalty / quarterly treasury draw | Hydro output telemetry; DHI custody | Yes — if buffer covers prefix loss; else capped | State mandate; volatility absorbed by certificates, not budget | Oracle false; counsel does not authorise draw |
| B. Iran energy→mining | Immediate import settlement | Metered energy delivery; counterparty solvency | Yes — energy is the collateral | Sanctions, confiscation, enforcement | Counterparty deserts or bank refuses |
| C. Norway/Alaska dividend | Annual (POMV/legislative vote) | Fund custodian value marks | Yes — fund asset backing under board rule | Parliament can freeze / change rule | Legislature overrides the charter |
| D. Web4 agent ledger | Seconds — streamed fees | Transaction-order / MEV / verifier witnesses | Yes — if allocation per tx conserved | DAO/validator set + liquid market | Front-runner bends the rule without breaking conservation |
| E. Russia internal claims | Immediate internal clearance | Commodity delivery proof | Yes — internal claims only | State enforcement outside chain | Export corridor closes; no legal standing |
| F. Islamic sukuk / riba-free | Maturity / profit share release windows | Project cash returns, KYC | Yes — asset-linked only | Sharia council / AAOIFI sign-off | Fatwa withheld; legal wrapper absent |
| G. Afghanistan riba-ban rail | Same as (F) | Delivery proof + community verification | Yes — buffer must exist | Taliban/IMF law; monetary authority | Treasury/authority cannot license rails |
| H. Post-wage zero-labor households | Continuous profit share | Output metering + equity registry | Yes — only if yield pool exists | Legislature; capture (who buys the compute) | Households hold certificates to empty pools |
| 17–18 Arbitration / tahkim | Award-to-settlement window | Tribunal evidence record | Yes — escrow only when award certified | Seat court / council; merits appeal | Award set aside post-settlement |
| 19–20 Gulf SWF / BRI bridges | Intra-day net / multi-year corridor | Cross-border asset marks, FX quotes | Yes — net-settled; no external numeraire required | Boards + host regulators | Corridor sovereign blocks transfer |
| 21–22 SDR / CLS PvP | SDR bridge weekly; CLS cut-off daily | IMF trust / CLS member solvency | Yes — PVP atomic if reserves posted | IMF/CLS board; bank margin | Reserve shortfall; solvency failure |
| 23–30 CBDC / Pix / rails | Real-time to T+1 | NIBSS / CBK / ECB / BCB / MAS / BIS coverage | Yes — integer clearing only | Central-bank mandate; bank consortia | Hot swap fails; dual-run divergence |
| 31–37 Subsidies / aid / climate funds | Monthly / quarterly | Fiscal ID, impact cert | Yes — escrow + conservation proves non-dilution | Ministries + auditors; procurement law | Ghost recipients; audit mismatch |
| 38–69 Arrears family (climate debt, reparations, pensions, healthcare, water, post-disaster, etc.) | Issue-specific monthly-to-5yr tranche | Project/site data, actuarial certs, quota/catch data | Yes — **only if** prefix buffer ≥ realised loss; otherwise certificate scales down, does not default | Regulators, treaty bodies, local councils | Underlying data fabricated; donor capacity fails |
| **All cases** | — | **If oracle compromised, the invariant holds for bad data.** | — | — | — |

**Reading guide.** `Yes (in-model)` = “for the stated class, the Lean machine-checked rules prove binding budgets, minor-unit conservation, ordered-quota distribution, escrow lifecycle, and stress-prefix bounds.” `No (out-of-scope)` = adoption, legal title, custody, Sharia ruling, geopolitics, market risk — external by theorem scoping.


---
*End of TECHNICAL_FIT — companion to BIGGER_PICTURE_2026-11-06.md and README top-50 framing. Verify the 90/918 manifest before quoting any global claim.*
