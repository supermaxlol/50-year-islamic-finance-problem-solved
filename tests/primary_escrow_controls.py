#!/usr/bin/env python3
"""Independent exact controls of the escrow specification, NOT code refinement."""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
import json
from pathlib import Path
import random

STAGE = Path(__file__).resolve().parent
GATES = frozenset(range(6))
INITIAL = (Q(10), Q(8), Q(2))
PRICE, CAP, CONSTRUCTION, RESERVE = Q(2), 6, Q(7), Q(5)
SUBSCRIBE_DEADLINE, RELEASE_DEADLINE = 10, 20
ISSUER, CUSTODIAN, VERIFIER, RESOLVER = 0, 1, 2, 0


@dataclass(frozen=True)
class State:
    wallet: tuple = INITIAL
    units: tuple = (0, 0, 0)
    escrow: Q = Q(0)
    operating: Q = Q(0)
    builder_paid: Q = Q(0)
    phase: str = 'collecting'
    approved: frozenset = frozenset()
    release_evidence: frozenset = frozenset()
    release_time: int = 0
    paused: frozenset = frozenset()
    receipts: frozenset = frozenset()
    now: int = 0


def update(xs, i, x):
    return tuple(x if j == i else v for j, v in enumerate(xs))


def transition(s, kind, actor=0, a=0, n=1, receipt=0, consent=True,
               settled=True, action='release', gates=GATES, gate=0, time=0):
    def require(h):
        if not h:
            raise ValueError('Guard rejected')

    if kind == 'subscribe':
        require(actor == CUSTODIAN and s.phase == 'collecting' and n > 0)
        require(sum(s.units) + n <= CAP and PRICE*n <= s.wallet[a])
        require(receipt not in s.receipts and s.now <= SUBSCRIBE_DEADLINE)
        require('subscriptions' not in s.paused and consent and settled)
        return replace(s, wallet=update(s.wallet, a, s.wallet[a]-PRICE*n),
                       units=update(s.units, a, s.units[a]+n),
                       escrow=s.escrow+PRICE*n, receipts=s.receipts | {receipt})
    if kind == 'fund':
        require(actor == ISSUER and s.phase == 'collecting' and sum(s.units) == CAP)
        require(CONSTRUCTION+RESERVE <= s.escrow and s.now <= SUBSCRIBE_DEADLINE)
        require('funding' not in s.paused)
        return replace(s, phase='funded')
    if kind == 'release':
        require(actor == CUSTODIAN and s.phase == 'funded')
        require(GATES <= s.approved and s.now <= RELEASE_DEADLINE)
        require('release' not in s.paused)
        return replace(s, phase='released', escrow=Q(0), operating=s.escrow-CONSTRUCTION,
                       builder_paid=CONSTRUCTION, release_evidence=s.approved,
                       release_time=s.now)
    if kind == 'cancel':
        require(s.phase in ('collecting', 'funded'))
        timeout = ((s.phase == 'collecting' and s.now > SUBSCRIBE_DEADLINE)
                   or (s.phase == 'funded' and s.now > RELEASE_DEADLINE))
        require(actor == ISSUER or (actor == CUSTODIAN and timeout))
        return replace(s, phase='cancelled')
    if kind == 'refund':
        require(actor == CUSTODIAN and s.phase == 'cancelled' and s.units[a] > 0)
        amount = PRICE*s.units[a]
        # Affordability is NOT an extra acceptance guard: it follows from the invariant.
        return replace(s, wallet=update(s.wallet, a, s.wallet[a]+amount),
                       units=update(s.units, a, 0), escrow=s.escrow-amount)
    if kind == 'attest':
        require(actor == VERIFIER)
        return replace(s, approved=s.approved | gates)
    if kind == 'revoke':
        require(actor == VERIFIER)
        return replace(s, approved=s.approved - {gate})
    if kind == 'pause':
        require(actor == VERIFIER and action in ('subscriptions', 'funding', 'release'))
        return replace(s, paused=s.paused | {action})
    if kind == 'resolve':
        require(actor == RESOLVER)
        return replace(s, paused=s.paused - {action})
    if kind == 'tick':
        require(s.now <= time)
        return replace(s, now=time)
    raise ValueError('Unknown operation')


def invariant(s):
    assert all(x >= 0 for x in s.wallet)
    assert all(isinstance(x, int) and x >= 0 for x in s.units)
    assert sum(s.units) <= CAP
    assert all(s.wallet[i]+PRICE*s.units[i] == INITIAL[i] for i in range(3))
    assert s.escrow >= 0 and s.operating >= 0 and s.builder_paid >= 0
    assert s.escrow+s.operating+s.builder_paid == PRICE*sum(s.units)
    assert sum(s.wallet)+s.escrow+s.operating+s.builder_paid == sum(INITIAL)
    if s.phase in ('collecting', 'cancelled'):
        assert s.operating == s.builder_paid == 0
    elif s.phase == 'funded':
        assert sum(s.units) == CAP and s.operating == s.builder_paid == 0
        assert CONSTRUCTION+RESERVE <= s.escrow
    elif s.phase == 'released':
        assert s.escrow == 0 and sum(s.units) == CAP and s.builder_paid == CONSTRUCTION
        assert s.operating == PRICE*CAP-CONSTRUCTION and RESERVE <= s.operating
        assert GATES <= s.release_evidence and s.release_time <= RELEASE_DEADLINE
    else:
        raise AssertionError('Invalid phase')


def buffer_needed(xs):
    balance, needed = Q(0), Q(0)
    for x in xs:
        balance += x
        needed = max(needed, -balance)
    return needed


def check():
    checks = []

    def ok(name, condition=True):
        assert condition, name
        checks.append(name)

    def admitted(s, kind, **args):
        t = transition(s, kind, **args)
        invariant(t)
        assert s.receipts <= t.receipts
        return t

    def rejected(name, s, kind, **args):
        try:
            transition(s, kind, **args)
        except ValueError:
            ok(name)
        else:
            raise AssertionError('Unexpected acceptance: '+name)

    s = State()
    invariant(s)
    ok('Initial nonnegative cash and zero claims')
    rejected('Pledge without settled transfer rejected', s, 'subscribe', actor=1, settled=False)
    rejected('No subscriber consent rejected', s, 'subscribe', actor=1, consent=False)
    rejected('Unattested actor cannot post cash', s, 'subscribe', actor=0)
    rejected('Zero subscription rejected', s, 'subscribe', actor=1, n=0)
    rejected('Subscription over wallet rejected', s, 'subscribe', actor=1, a=2, n=2)
    rejected('Funding before full rights subscribed rejected', s, 'fund')
    rejected('Release before funding rejected', s, 'release', actor=1)
    rejected('Refund before cancellation rejected', s, 'refund', actor=1)
    first = admitted(s, 'subscribe', actor=1, a=0, n=3, receipt=11)
    ok('Only settled subscription increases escrow', first.escrow == 6 and first.wallet[0] == 4)
    ok('Paid entitlements do not activate ownership before release', first.phase != 'released')
    rejected('Receipt replay by another subscriber rejected', first, 'subscribe', actor=1, a=1, receipt=11)
    rejected('Subscription exceeding cap rejected', first, 'subscribe', actor=1, a=1, n=4, receipt=12)
    full = admitted(first, 'subscribe', actor=1, a=1, n=3, receipt=12)
    funded = admitted(full, 'fund')
    ok('Collected cash covers construction plus buffer exactly', funded.escrow == 12)
    rejected('Repeated funding close rejected', funded, 'fund')
    rejected('Post-close subscription rejected', funded, 'subscribe', actor=1, receipt=13)
    rejected('No approvals cannot release', funded, 'release', actor=1)
    approved = admitted(funded, 'attest', actor=2)
    missing = admitted(approved, 'revoke', actor=2, gate=5)
    rejected('One missing gate blocks release', missing, 'release', actor=1)
    paused = admitted(approved, 'pause', actor=2)
    ok('Dispute does not mutate cash or entitlement', paused.escrow == approved.escrow and paused.units == approved.units)
    rejected('Named release dispute blocks release', paused, 'release', actor=1)
    rejected('Wrong actor cannot resolve dispute', paused, 'resolve', actor=1)
    unpaused = admitted(paused, 'resolve', actor=0)
    live = admitted(unpaused, 'release', actor=1)
    ok('Construction paid once and operating cash segregated', live.builder_paid == 7 and live.operating == 5 and live.escrow == 0)
    ok('Active ownership reconciles to authorized supply', sum(live.units) == CAP)
    rejected('Second capital release rejected', live, 'release', actor=1)
    rejected('Released capital cannot be refunded', live, 'cancel')
    rejected('Released ownership cannot use cancellation refund', live, 'refund', actor=1)
    later = admitted(live, 'tick', time=100)
    later = admitted(later, 'revoke', actor=2, gate=0)
    ok('Historical release evidence survives later revocation and time', later.release_evidence == GATES and later.release_time == 0)

    cancelled = admitted(first, 'cancel')
    for action in ('subscriptions', 'funding', 'release'):
        cancelled = admitted(cancelled, 'pause', actor=2, action=action)
    back = admitted(cancelled, 'refund', actor=1, a=0)
    ok('Refund ignores unrelated pause scopes and returns original cash', back.wallet == INITIAL and back.escrow == 0)
    rejected('Second refund rejected', back, 'refund', actor=1, a=0)
    rejected('Refund does not reopen subscription', back, 'subscribe', actor=1, receipt=19)
    ok('Receipt remains consumed after refund', 11 in back.receipts)
    timeout = admitted(funded, 'tick', time=21)
    rejected('Late release rejected', timeout, 'release', actor=1)
    timeout = admitted(timeout, 'cancel', actor=1)
    timeout = admitted(timeout, 'refund', actor=1, a=1)
    timeout = admitted(timeout, 'refund', actor=1, a=0)
    ok('Funded timeout cancellation preserves complete refunds', timeout.wallet == INITIAL and timeout.escrow == 0)
    p = admitted(State(), 'pause', actor=2, action='release')
    admitted(p, 'subscribe', actor=1, n=1)
    ok('Release dispute does not freeze subscription action')
    p = admitted(State(), 'tick', time=11)
    rejected('Late subscription rejected', p, 'subscribe', actor=1)
    admitted(p, 'cancel', actor=1)
    ok('Collecting timeout cancellation available')
    rejected('Clock cannot move backwards', p, 'tick', time=5)

    paths = [tuple(map(Q, xs)) for xs in [(-4, 2, -3, 8), (-2, -3, 1, 8), (0, 0), (3, -7, 5)]]
    for i, xs in enumerate(paths):
        assert buffer_needed(xs) <= RESERVE
        balance = live.operating
        for x in xs:
            assert balance >= 0
            balance += x
            assert balance >= 0
        ok(f'Dated path {i}: every payment affordable and terminal identity exact', balance == PRICE*CAP-CONSTRUCTION+sum(xs))

    # Exact exhaustive accounting controls, not an equilibrium/rounding result.
    refund_cases = 0
    for u0 in range(6):
        for u1 in range(5):
            for u2 in range(2):
                units = (u0, u1, u2)
                if sum(units) > CAP:
                    continue
                q = State(wallet=tuple(INITIAL[i]-PRICE*units[i] for i in range(3)),
                          units=units, escrow=PRICE*sum(units), phase='cancelled')
                invariant(q)
                for a in range(3):
                    if q.units[a]:
                        t = admitted(q, 'refund', actor=1, a=a)
                        assert t.units[a] == 0 and t.wallet[a] == INITIAL[a]
                        refund_cases += 1
    ok('All small affordable entitlement/refund cases preserve accounting', refund_cases > 0)

    rng = random.Random(209)
    accepted = rejected_count = 0
    s = State()
    kinds = ('subscribe', 'fund', 'release', 'cancel', 'refund', 'attest', 'revoke', 'pause', 'resolve', 'tick')
    for k in range(6000):
        if k % 40 == 0:
            s = State()
        op = rng.choice(kinds)
        kw = dict(actor=rng.randrange(3), a=rng.randrange(3), n=rng.randrange(5),
                  receipt=rng.randrange(10), consent=rng.choice((True, True, False)),
                  settled=rng.choice((True, True, False)), gate=rng.randrange(6),
                  action=rng.choice(('subscriptions', 'funding', 'release')), time=rng.randrange(25))
        try:
            t = transition(s, op, **kw)
        except ValueError:
            rejected_count += 1
        else:
            invariant(t)
            assert s.receipts <= t.receipts
            s = t
            accepted += 1
    ok('6000 generated guarded attempts preserve every invariant', accepted > 0 and rejected_count > 0)
    return dict(stage=209, passed=True, named_controls=len(checks), checks=checks,
                exact_refund_cases=refund_cases, generated_attempts=6000,
                generated_accepted=accepted, generated_rejected=rejected_count,
                supplied_cashflow_paths=len(paths), arithmetic='fractions.Fraction',
                evidence_type='independent specification controls, not refinement or empirical validation')


if __name__ == '__main__':
    result = check()
    (STAGE/'CONTROL_CHECKS.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))
