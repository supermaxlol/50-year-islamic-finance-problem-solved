#!/usr/bin/env python3
"""Portable audit of retained payout replies; no worker launch or writes.

The original cases, expected and economic_controls functions are unchanged.
The surrounding retained-evidence checker is new and not kernel-verified.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parents[1]
def cases():
    named=[(101,250,[1,2,0,3]),(10,10000,[3,3]),(0,0,[0,0]),(0,0,[]),
        (5,10000,[]),(1,0,[0,1,0]),(1,0,[1,1,1]),(10**90+3,1,[1,10**40,7,0])]
    rng=random.Random(226)
    for _ in range(500):
        ws=[rng.randrange(1000) for _ in range(rng.randrange(1,30))]
        if not any(ws):ws[0]=1
        named.append((rng.randrange(10**18),rng.randrange(10001),ws))
    return named
def expected(g,b,ws):
    fee=g*b//10000;net=g-fee;total=sum(ws);prefix=0;paid=[]
    for w in ws:
        before=0 if not total else int(F(net*prefix,total))
        prefix+=w
        after=0 if not total else int(F(net*prefix,total))
        paid.append(after-before)
    return dict(ok=True,fee=str(fee),net=str(net),payments=list(map(str,paid)),total=str(g))
def economic_controls():
    # Independent exact Euler certificates, not supplied numerical demands.
    records=[]
    for e,beta in [(16,F(7,9)),(20,F(5,9))]:
        for q in [F(199,100),F(201,100)]:
            current=e-q*3
            score=beta*F(9,10)*2/7-q/current
            assert current>0
            assert (score>0 if q<2 else score<0)
            records.append(dict(cash=e,price=str(q),holding=3,score=str(score)))
    assert 12-5-6==1>0 and 12-5-7==0
    assert F(6+5,6)<F(199,100)<2<F(201,100)
    # A narrow interval excluding 2 is not valid merely because its midpoint looks plausible.
    q=F(201,100);bad_score=F(7,9)*F(9,10)*2/7-q/(16-q*3)
    assert bad_score<0
    return dict(euler_certificates=records,strict_supplier_surplus=1,
        lower_price='199/100',upper_price='201/100',midpoint='2',error_bound='1/100',
        incorrect_lower_certificate_rejected=True)
def check():
    receipt=json.loads((ROOT/'evidence/controls/payout_calculator.json').read_text())
    replies=[json.loads(x) for x in (ROOT/receipt['retained_reply_log']).read_text().splitlines()]
    examples=cases();counts=receipt['counts']
    assert receipt['passed'] and receipt['exit_code']==0
    assert len(examples)==counts['exact_payout_comparisons']==508
    assert len(replies)==len(examples)+counts['malformed_rejections']==519
    for (g,b,ws),reply in zip(examples,replies):
        assert reply==expected(g,b,ws),(g,b,ws,reply)
        fee=int(reply['fee']);paid=list(map(int,reply['payments']));net=g-fee
        assert 0<=fee<=g and fee+sum(paid)==g and len(ws)==len(paid)
        for w,p in zip(ws,paid):
            assert p>=0 and (w!=0 or p==0)
            if sum(ws):assert abs(F(p)-F(net*w,sum(ws)))<1
    for reply in replies[len(examples):]:assert reply['ok'] is False and isinstance(reply['error'],str)
    assert economic_controls()==receipt['economic']
    assert counts['euler_endpoint_certificates']==4 and counts['negative_price_certificate_controls']==1
    return dict(exact_comparisons=508,malformed_rejections=11,euler_certificates=4,
        negative_certificate_controls=1,retained_replies_only=True,passed=True)
if __name__=='__main__':print(json.dumps(check(),indent=2))
