#!/usr/bin/env python3
"""Check retained replies with the original independent deterministic oracle.

The oracle and cases are unchanged from the accepted runtime controls. This
portable wrapper reads evidence only; it does not rerun the Lean worker.
"""
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parents[1]
def oracle(b,xs):
    running=0;minimum=0;first=0 if b<0 else None;balance=b if b<0 else None
    for n,x in enumerate(xs,1):
        running+=x;minimum=min(minimum,running)
        if first is None and b+running<0:first=n;balance=b+running
    return dict(ok=True,required=str(-minimum),affordable=b>=-minimum,
        shortfall_prefix=first,shortfall_balance=None if balance is None else str(balance),
        terminal_balance=str(b+running))
def cases():
    rng=random.Random(224)
    base=[[],[0],[5,2],[-5,12],[-5,0],[3,-5,12],[0,-5,15],[-10,5,-2,100],
        [10**90,-10**90-7,20],[-10**90,10**90],[1,-1]*64]
    allcases=[]
    for xs in base:
        need=int(oracle(0,xs)['required'])
        allcases.extend((b,xs) for b in [-1,0,need-1,need,need+1,10**100])
    for _ in range(500):
        xs=[rng.randrange(-10000,10001) for _ in range(rng.randrange(65))]
        need=int(oracle(0,xs)['required']);b=rng.choice([-1,0,need-1,need,need+1,rng.randrange(100000)])
        allcases.append((b,xs))
    return allcases
def check():
    receipt=json.loads((ROOT/'evidence/controls/reserve_calculator.json').read_text())
    replies=[json.loads(x) for x in (ROOT/receipt['retained_reply_log']).read_text().splitlines()]
    examples=cases()
    assert receipt['passed'] and receipt['exit_code']==0
    assert len(examples)==receipt['exact_comparisons']==566
    assert len(replies)==len(examples)+receipt['malformed_rejections']==573
    for (b,xs),reply in zip(examples,replies):assert reply==oracle(b,xs),(b,xs,reply)
    for reply in replies[len(examples):]:assert reply['ok'] is False and isinstance(reply['error'],str)
    return dict(exact_comparisons=566,malformed_rejections=7,retained_replies_only=True,passed=True)
if __name__=='__main__':print(json.dumps(check(),indent=2))
