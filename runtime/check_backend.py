#!/usr/bin/env python3
"""Exercise the real Lean transformation through a bounded SQLite adapter.

No economic guard is reimplemented here. Crash tests terminate a newly created
test child, never a user process. All databases are newly created test outputs.
"""
import copy
import json
import multiprocessing as mp
import os
from pathlib import Path
import random
import selectors
import sqlite3
import subprocess
import tempfile
import threading
import time
from collections import Counter

from sqlite_adapter import SQLiteLedger, canonical
from verify import STAGE, core_command


class CoreWorker:
    def __init__(self):
        command,env,cwd=core_command()
        self.logpath=STAGE/'logs/bridge-1.log'
        self.log=self.logpath.open('wb')
        self.process=subprocess.Popen(command,cwd=cwd,env=env,stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=self.log,text=True,bufsize=1)
        self.lock=threading.Lock()
        self.calls=0

    def raw(self,line):
        with self.lock:
            if self.process.poll() is not None:
                raise RuntimeError('Lean worker terminated: '+self.logpath.read_text())
            self.process.stdin.write(line+'\n');self.process.stdin.flush()
            with selectors.DefaultSelector() as sel:
                sel.register(self.process.stdout,selectors.EVENT_READ)
                if not sel.select(180): raise TimeoutError('Lean response deadline')
            output=self.process.stdout.readline()
            self.calls+=1
            if not output: raise RuntimeError('Unexpected Lean EOF: '+self.logpath.read_text())
            try: return json.loads(output)
            except json.JSONDecodeError as exc: raise RuntimeError('Unexpected Lean stdout: '+output) from exc

    def __call__(self,command):
        return self.raw(canonical(command))

    def close(self):
        if self.process.poll() is None:
            self.process.stdin.close()
            try: self.process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                self.process.terminate();self.process.wait(timeout=15)
        self.log.close()
        if self.process.returncode!=0:
            raise RuntimeError('Lean worker exit: '+str(self.process.returncode))
        if self.logpath.read_text().strip():
            raise RuntimeError('Unexpected bridge diagnostics: '+self.logpath.read_text())


def request(identity,revision,event):
    return [[identity,revision],event]


def rows(path):
    with sqlite3.connect(str(path)) as c:
        return c.execute('SELECT revision,store,last_result FROM ledger WHERE id=1').fetchone()


def integrity(path):
    with sqlite3.connect(str(path)) as c:
        assert c.execute('PRAGMA integrity_check').fetchall()==[('ok',)]


def crash_child(path,connection,unused,point,req):
    unused.close()
    def rpc(command):
        connection.send(command)
        return connection.recv()
    def hook(where):
        if where==point: os._exit(91)
    try:
        SQLiteLedger(path,rpc).submit(req,hook)
        connection.send({'unexpected_return':True})
    except BaseException as exc:
        connection.send({'child_failure':repr(exc)})
    finally:
        connection.close()


def crash_once(path,core,point,req):
    context=mp.get_context('fork')
    parent,child=context.Pipe()
    process=context.Process(target=crash_child,args=(path,child,parent,point,req))
    process.start();child.close()
    deadline=time.monotonic()+60
    try:
        while True:
            if time.monotonic()>deadline: raise TimeoutError('Crash-child deadline')
            if parent.poll(0.1):
                try: command=parent.recv()
                except EOFError: break
                if isinstance(command,dict): raise AssertionError(command)
                parent.send(core(command))
            elif not process.is_alive(): break
        process.join(timeout=5)
        assert process.exitcode==91,process.exitcode
    finally:
        parent.close()
        if process.is_alive():
            process.terminate();process.join(timeout=5)


def main():
    root=Path(tempfile.mkdtemp(prefix='backend-',dir=STAGE/'logs'))
    core=CoreWorker()
    counts=Counter()
    modes=Counter()
    def new(name):
        path=root/(name+'.sqlite')
        ledger=SQLiteLedger(path,core,initialize=True)
        assert ledger.read()['revision']=='0'
        counts['initialized_databases']+=1
        return ledger
    def checked(ledger,req,mode=0,accepted=None):
        before=ledger.read()['store']
        expected=core([2,before,req])
        actual=ledger.submit(req)
        assert expected==actual,(expected,actual)
        assert actual['mode']==mode,actual
        if accepted is not None:
            assert bool(actual['outcome'][0][2]) is accepted,actual
        modes[str(mode)]+=1
        counts['exact_lean_result_comparisons']+=1
        reopened=SQLiteLedger(ledger.path,core).read()
        assert reopened['store']==actual['store']
        counts['reopen_checks']+=1
        return actual
    try:
        first=core([0,[],[]]);assert first['ok'] and first['revision']=='0'
        print('Lean bridge started; complete envelopes and SQLite settings active.',flush=True)
        ledger=new('funded-lifecycle')
        a=request(10,0,[0,1,4,3,100])
        b=request(11,1,[0,1,5,3,101])
        initial_out=checked(ledger,a,accepted=True)
        checked(ledger,b,accepted=True)
        refused=request(12,2,[0,1,4,1,100])
        checked(ledger,refused,accepted=False)
        checked(ledger,request(13,3,[1,0]),accepted=True)
        checked(ledger,request(14,4,[5,2,1,1,1,1,1,1]),accepted=True)
        checked(ledger,request(15,5,[2,1]),accepted=True)
        stable=rows(ledger.path)
        replay=checked(ledger,a,mode=1,accepted=True)
        assert replay['outcome']==initial_out['outcome']
        assert replay['store']!=initial_out['store']
        checked(ledger,refused,mode=1,accepted=False)
        checked(ledger,request(10,0,[0,1,4,2,100]),mode=2)
        checked(ledger,request(99,0,[9,0]),mode=3)
        assert rows(ledger.path)==stable
        counts['old_reply_not_current_state_checks']+=1
        ledger=new('cancel-refund')
        events=[[0,1,4,2,200],[1,5],[7,2,0],[0,1,5,1,201],
                [8,3,0],[3,0],[4,1,4],[4,1,4],[6,2,0],[9,30]]
        expected_accept=[True,False,True,False,True,True,True,False,True,True]
        for i,(event,ok) in enumerate(zip(events,expected_accept)):
            checked(ledger,request(100+i,i,event),accepted=ok)
        assert ledger.read()['store'][1][3]==[0,0,0,0,16,20]
        counts['refund_no_double_payment_checks']+=1

        # Terminate only a fresh child at three precise storage boundaries.
        for point in ['before_update','after_update','after_commit']:
            for refused_event in [False,True]:
                ledger=new('crash-'+point+str(int(refused_event)))
                req=request(900,0,[0,1,4,2,900] if not refused_event else [1,5])
                old=rows(ledger.path)
                prediction=core([2,ledger.read()['store'],req])
                newrow=(prediction['revision'],canonical(prediction['store']),canonical(prediction['packet']))
                crash_once(ledger.path,core,point,req)
                integrity(ledger.path)
                assert rows(ledger.path)==(newrow if point=='after_commit' else old)
                SQLiteLedger(ledger.path,core).read()
                retry=checked(ledger,req,mode=1 if point=='after_commit' else 0,
                              accepted=not refused_event)
                assert retry['outcome']==prediction['outcome']
                assert rows(ledger.path)==newrow
                checked(ledger,req,mode=1,accepted=not refused_event)
                counts['process_exit_faults']+=1
                counts['atomic_old_or_new_full_row_checks']+=1

        # Two independent connections, fixed winning orders, real writer locking.
        for schedule in range(8):
            ledger=new('concurrency-'+str(schedule))
            requests=[request(700,0,[0,1,4,1,700]),request(701,0,[0,1,5,1,701])]
            first_index=schedule%2
            locked=threading.Event();release=threading.Event();attempted=threading.Event()
            responses={};failures=[]
            def first_hook(where):
                if where=='after_begin':
                    locked.set()
                    if not release.wait(10): raise TimeoutError('First-writer gate')
            def writer(index,hook=None):
                try:
                    if hook is None:
                        probe=SQLiteLedger(ledger.path,core).connect()
                        try:
                            probe.execute('PRAGMA busy_timeout=0')
                            try: probe.execute('BEGIN IMMEDIATE')
                            except sqlite3.OperationalError as exc:
                                assert 'locked' in str(exc)
                            else: raise AssertionError('Competing writer lock not enforced')
                        finally: probe.close()
                        attempted.set()
                    responses[index]=SQLiteLedger(ledger.path,core).submit(requests[index],hook)
                except BaseException as exc: failures.append(repr(exc))
            t1=threading.Thread(target=writer,args=(first_index,first_hook))
            t2=threading.Thread(target=writer,args=(1-first_index,))
            t1.start();assert locked.wait(10)
            t2.start();assert attempted.wait(10)
            # The contender has its own connection and attempts while writer holds lock.
            release.set();t1.join(20);t2.join(20)
            assert not t1.is_alive() and not t2.is_alive() and not failures,failures
            assert responses[first_index]['mode']==0
            assert responses[1-first_index]['mode']==3
            assert ledger.read()['revision']=='1'
            checked(ledger,requests[first_index],mode=1,accepted=True)
            checked(ledger,requests[1-first_index],mode=3)
            integrity(ledger.path)
            counts['actual_two_connection_schedules']+=1
            modes['0']+=1;modes['3']+=1

        # Independent corruption fixtures; no test resets or overwrites another run.
        seed=new('corruption-source')
        checked(seed,request(1,0,[0,1,4,2,600]),accepted=True)
        checked(seed,request(2,1,[9,1]),accepted=True)
        seedrow=rows(seed.path)
        corruptions=[]
        def packet_change(label,edit):
            packet=json.loads(seedrow[1]);edit(packet)
            corruptions.append((label,seedrow[0],canonical(packet),seedrow[2]))
        packet_change('balance',lambda p:p[1][3].__setitem__(4,999))
        packet_change('journal-truncation',lambda p:p.pop())
        packet_change('journal-duplicate',lambda p:p.append(copy.deepcopy(p[-1])))
        packet_change('journal-order',lambda p:p.__setitem__(slice(2,None),list(reversed(p[2:]))))
        packet_change('context',lambda p:p[1][0].__setitem__(2,740))
        packet_change('schema',lambda p:p[0][0].__setitem__(0,220))
        packet_change('actor',lambda p:p[-1][1].__setitem__(1,6))
        packet_change('approval-flag',lambda p:p[1][6].__setitem__(0,2))
        corruptions += [('sql-revision','3',seedrow[1],seedrow[2]),
                        ('revision-leading-zero','02',seedrow[1],seedrow[2]),
                        ('missing-result',seedrow[0],seedrow[1],'[]'),
                        ('non-finite',seedrow[0],'[NaN]',seedrow[2])]
        wrong_result=json.loads(seedrow[2]);wrong_result[0][0][3]=1
        corruptions.append(('wrong-result-mode',seedrow[0],seedrow[1],canonical(wrong_result)))
        for label,rev,body,last in corruptions:
            path=root/('corrupt-'+label+'.sqlite')
            with sqlite3.connect(str(seed.path)) as src,sqlite3.connect(str(path)) as dst:
                src.backup(dst)
                dst.execute('UPDATE ledger SET revision=?,store=?,last_result=? WHERE id=1',(rev,body,last))
            before=rows(path)
            try: SQLiteLedger(path,core).read()
            except (ValueError,RuntimeError): pass
            else: raise AssertionError('Corruption accepted: '+label)
            assert rows(path)==before
            counts['corruption_rejections_without_reset']+=1

        # JSON transport rejects non-Nat/malformed wires, without touching the DB.
        for bad in ['-1','1.5','true','null','{}','[]','[0,4,1]','[5,2,1,1,2,1,1,1]']:
            command='[2,'+canonical(seed.read()['store'])+',[[300,2],'+bad+']]'
            before=rows(seed.path)
            assert core.raw(command)['ok'] is False
            assert rows(seed.path)==before
            counts['malformed_transport_rejections']+=1
        try: SQLiteLedger(seed.path,core,initialize=True)
        except FileExistsError: counts['existing_database_not_reinitialized']+=1
        else: raise AssertionError('Existing database overwritten')
        missing=root/'missing.sqlite'
        try: SQLiteLedger(missing,core).read()
        except FileNotFoundError: counts['missing_database_not_created']+=1
        else: raise AssertionError('Missing database silently created')
        assert not missing.exists()

        # Short generated histories keep full replay cost bounded and inspectable.
        rng=random.Random(219)
        for fixture in range(5):
            ledger=new('generated-'+str(fixture))
            for index in range(20):
                tag=rng.randrange(10)
                if tag==0: event=[0,rng.randrange(6),rng.randrange(6),rng.randrange(5),rng.randrange(8)]
                elif tag in [1,2,3]: event=[tag,rng.randrange(6)]
                elif tag==4: event=[tag,rng.randrange(6),rng.randrange(6)]
                elif tag==5: event=[tag,rng.randrange(6)]+[rng.randrange(2) for _ in range(6)]
                elif tag in [6,7,8]: event=[tag,rng.randrange(6),rng.randrange(6) if tag==6 else rng.randrange(3)]
                else: event=[9,rng.randrange(30)]
                checked(ledger,request(1000+index,index,event))
                counts['generated_requests']+=1
            integrity(ledger.path)
        summary=dict(stage=219,passed=True,counts=dict(counts),observed_modes=dict(modes),
            core_calls=core.calls,python=os.sys.version.split()[0],sqlite=sqlite3.sqlite_version,
            settings=dict(journal_mode='delete',synchronous=3,fullfsync=1),
            output_directory=str(root),same_proved_lean_transformation=True,
            fixed_mock_evidence=True,python_sqlite_kernel_verified=False,
            process_exit_faults_tested=True,power_loss_tested=False,
            authentication_real_custody_or_legal_title_verified=False)
        core.close();core=None
        (STAGE/'BACKEND_CONTROLS.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps(summary,indent=2),flush=True)
    finally:
        if core is not None: core.close()


if __name__=='__main__': main()
