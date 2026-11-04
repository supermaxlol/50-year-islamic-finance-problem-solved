# Strict execution, integer distributions and actual-price certificates

Stage 226 contributes two source-identical accepted modules and 30 clean retained
declaration audits, using standard foundations only. This release copies the
accepted evidence; it is not a fresh kernel build or a new database run.

## Strict choices and the same recovered funding record

The construction-six plan retains the existing example's price two, six-unit
cap, reserve five and supplier quote seven. Both households actually choose
three units and strictly gain over zero investment. The same complete recovered
record pays the supplier seven; supplied physical cost six leaves surplus one
above outside zero. Recovery, household gains, dated operating affordability and
terminal productive receipts are proved together.

The earlier SQLite controls concern that unchanged exact record. There is no
new database run or independent evidence of physical construction cost. The
original construction-seven plan remains issuer-indifferent. The result is a
new formal composition, not endogenous technology discovery.

## A declared ordered integer payout rule

For gross integer cash G, fee basis points b<=10000, ordered natural ownership
weights w_i, total W>0 and preceding weight U_i, use

```text
fee = floor(G*b/10000)
A = G-fee
payment_i = floor(A*(U_i+w_i)/W) - floor(A*U_i/W)
```

The proved function preserves account order/list length, pays zero to zero
ownership, and gives nonnegative payments with exact total
`fee + sum(payments) = G`. Every payment differs from its exact net proportional
quota `A*w_i/W` by strictly less than one minor unit. Positive currency scaling
preserves budget conservation. Zero net cash permits empty/all-zero ownership;
positive net cash with zero total ownership is rejected by the transport.

For G=101, b=250 and weights [1,2,0,3], fee two plus payments [16,33,0,50]
equals 101 exactly. This is **not** a verification of the earlier Python
largest-remainder allocator, nor an amendment to the persistent funding protocol.
Account order, splitting and repeated-round bias can matter. Cumulative fairness,
general discrete-market equilibrium and real payment completion are not proved.
Fees must be declared in the contract and valuation; do not deduct operating
costs twice or assume unchanged prices after changing household receipts.

## Price brackets derived from actual optimization

For the accepted fresh-issue CRRA class, take q_min<=lo<=hi. Supply each buyer's
feasible lower holding at lo and feasible upper holding at hi. A zero lower
holding needs no score sign; otherwise require its marginal score nonnegative.
The upper holding's score must be nonpositive. If lower holdings sum to at least
supply and upper holdings to at most supply, the actual formed equilibrium exists
and its unique price lies in [lo,hi]. Midpoint error is at most (hi-lo)/2.
If lo>q_min, issuer participation is strict. A nonpositive score at feasible zero
certifies zero actual demand, including strictly inactive households.

The construction-six fixture has floor 11/6 and certified interval [1.99,2.01].
At holding three the two lower scores are 8/5015 and 10/9821; the upper scores
are -8/4985 and -10/9779. Thus midpoint two has error at most 0.01 without using
the already known clearing price as the premise for the endpoint signs.

This is a conditional certificate theorem, not an arbitrary-CRRA real-power
evaluator, a complete convergent executable solver or decentralized trading
convergence. Retaining a halved interval requires a new valid demand sign.

## Inspectable evidence

- [Joint accepted source](../formal/ConnectedPayoutPrice.lean), 27 audit endpoints,
  and [clean retained log](../evidence/axioms/ConnectedPayoutPrice.txt).
- [Corner adapter](../formal/PriceCornerCertificates.lean), three audit endpoints,
  and [clean retained log](../evidence/axioms/PriceCornerCertificates.txt).
- [Same-source payout worker](../runtime/PayoutWorker.lean) calls the proved pure
  functions. Parser/IO remain tested, not kernel-verified.
- [Retained replies](../evidence/controls/payout_worker.ndjson) and
  [sanitized original receipt](../evidence/controls/payout_calculator.json) contain
  508 exact comparisons and eleven malformed rejections. Four rational Euler
  endpoint controls and one invalid-certificate control check the example.
- [Portable audit](../tests/payout_controls.py) retains the original deterministic
  cases, expected replies and economic controls; its read-only wrapper is new.
  It checks existing replies, not a fresh runtime run.

No real money, authenticated external settlement, observed construction costs,
legal title or institution-wide safety is established by these results.
