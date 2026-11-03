# One primary-subscription constitution

Stage 209 is a fixed-price, fixed-supply, fee-free enterprise funding machine.
Natural-number units coexist with real-valued cash. The issue price, plan,
deadlines and actor identities are supplied; role names do not authenticate a
person or establish institutional independence.

```text
collecting → full and budgeted close → funded → attested release → released
     └──────── permitted cancellation ────────┘ → cancelled → refunds
```

| Action | Conditions and authority | Resource/rights effect |
|---|---|---|
| Post subscription | Custodian, subscriber consent and settled-transfer predicates; affordable positive units; fresh receipt; cap/deadline and subscriptions pause checked. | Debit subscriber wallet; credit escrow and paid entitlements. No active ownership yet. |
| Funding close | Issuer; full cap subscribed; construction plus reserve covered; deadline and funding pause checked. | Reserve the raise; no payment or active ownership. |
| Capital release | Custodian; all named evidence gates; deadline; release unpaused. | Pay construction once, segregate operating cash, empty escrow, activate subscribed ownership and snapshot admitted evidence/time. |
| Cancellation | Issuer before release, or custodian after the appropriate timeout. | Leave funds in escrow and open exact refunds. |
| Refund | Custodian to the recorded subscriber; cancelled phase and positive unpaid entitlement. | Return its original subscription amount and zero the entitlement. Refunds are not pauseable in this constitution. |
| Evidence/disputes | Verifier attests/revokes or pauses a named action; resolver clears a pause. | No transfer of funds or ownership. Later changes do not rewrite historical release evidence. |

For price `p`, units `u_a`, wallets `w_a`, escrow `E`, operating cash `O`,
builder payments `K`, and initial cash `w_a^0`, every reachable state satisfies:

```text
w_a + p u_a = w_a^0
E + O + K = p Σu_a
Σw_a + E + O + K = Σw_a^0
all cash compartments are nonnegative; Σu_a ≤ the cap
```

In cancelled states, operating cash and builder payments are zero. Hence each
refund is already affordable from escrow; it is not conditional on new borrowing.
Receipt IDs remain consumed, and a refunded positive entitlement cannot be paid
again. At release, full active ownership matches the authorized supply.

If the supplied reserve dominates Stage 207's exact prefix-deficit buffer in
every supplied state, the released operating cash pays every dated operating
obligation. A positive final payoff alone would not establish this.

Activated units initialize the separate distribution ledger with zero declared
distributable cash: retained operating capital is not simultaneously investor
yield. Actual future distributable receipts require separate posting/allocation.

The Stage 209 theorem is serial abstract safety, not liveness or bank integration.
Later stages now supply actual voluntary formation, exact integer execution,
the proved dispatcher/API protocol and a tested persistent adapter. See
[the connected demonstration](CONNECTED_DEMO.md) and [storage contract](../runtime/README.md).
Actual asynchronous payments still need pending/confirmed/failed reconciliation,
authentication and independently checked settlement. Evidence predicates do not prove
physical truth, and the visible issuer cancellation right need not be the fairest
possible constitution. Those choices must be negotiated and evaluated explicitly.
