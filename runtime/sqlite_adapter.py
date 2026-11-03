"""Bounded persistence harness. Economic guards are executed only in Lean.

This Python/SQLite driver is tested, not kernel-verified. No real funds or
external evidence providers are connected. Full envelopes are exact JSON text.
"""
import json
import sqlite3
from pathlib import Path


def canonical(value):
    return json.dumps(value,separators=(',',':'),ensure_ascii=True,allow_nan=False)


def strict_json(text):
    def bad(_):
        raise ValueError('Non-finite JSON constant')
    return json.loads(text,parse_constant=bad)


class SQLiteLedger:
    def __init__(self,path,core,initialize=False):
        self.path=Path(path)
        self.core=core
        if initialize:
            if self.path.exists():
                raise FileExistsError('Refusing to replace an existing ledger')
            self.path.parent.mkdir(parents=True,exist_ok=True)
            c=sqlite3.connect(str(self.path),isolation_level=None,
                              autocommit=sqlite3.LEGACY_TRANSACTION_CONTROL,timeout=10)
            try:
                if c.execute('PRAGMA journal_mode=DELETE').fetchone()[0]!='delete':
                    raise RuntimeError('Rollback-journal mode unavailable')
                self._settings(c)
                c.execute('CREATE TABLE ledger (id INTEGER PRIMARY KEY CHECK(id=1), revision TEXT NOT NULL, store TEXT NOT NULL, last_result TEXT NOT NULL)')
                initial=self._call([0,[],[]])
                c.execute('BEGIN IMMEDIATE')
                c.execute('INSERT INTO ledger VALUES(1,?,?,?)',
                          (initial['revision'],canonical(initial['store']),'[]'))
                c.execute('COMMIT')
            finally:
                c.close()

    @staticmethod
    def _settings(c):
        c.execute('PRAGMA synchronous=EXTRA')
        c.execute('PRAGMA fullfsync=ON')
        if c.execute('PRAGMA synchronous').fetchone()[0]!=3:
            raise RuntimeError('Required synchronous setting not active')
        if c.execute('PRAGMA fullfsync').fetchone()[0]!=1:
            raise RuntimeError('Required fullfsync setting not active')
        if c.execute('PRAGMA journal_mode').fetchone()[0]!='delete':
            raise RuntimeError('Unexpected journal mode')

    def connect(self):
        if not self.path.is_file():
            raise FileNotFoundError(self.path)
        c=sqlite3.connect(str(self.path),isolation_level=None,
                          autocommit=sqlite3.LEGACY_TRANSACTION_CONTROL,timeout=10)
        try:
            self._settings(c)
        except BaseException:
            c.close()
            raise
        return c

    def _call(self,command):
        response=self.core(command)
        if response.get('ok') is not True:
            raise ValueError(response.get('error','Lean bridge rejected command'))
        return response

    def _row(self,c):
        row=c.execute('SELECT revision,store,last_result FROM ledger WHERE id=1').fetchone()
        if row is None:
            raise ValueError('Missing ledger row; no implicit reset')
        revision,body,last=row
        if not revision.isascii() or not revision.isdecimal() or str(int(revision))!=revision:
            raise ValueError('Noncanonical revision text')
        packet=strict_json(body)
        checked=self._call([3,packet,strict_json(last)])
        if checked['revision']!=revision or canonical(checked['store'])!=body:
            raise ValueError('Database revision/envelope mismatch')
        return revision,body,last,checked

    def read(self):
        c=self.connect()
        try:
            c.execute('BEGIN')
            _,_,_,checked=self._row(c)
            c.execute('COMMIT')
            return checked
        except BaseException:
            if c.in_transaction: c.execute('ROLLBACK')
            raise
        finally:
            c.close()

    def submit(self,request,hook=None):
        hook=hook or (lambda _:None)
        c=self.connect()
        try:
            c.execute('BEGIN IMMEDIATE')
            hook('after_begin')
            revision,body,_,checked=self._row(c)
            response=self._call([2,checked['store'],request])
            hook('before_update')
            if response['mode']==0:
                if int(response['revision'])!=int(revision)+1:
                    raise ValueError('Unexpected model revision')
                result=c.execute('UPDATE ledger SET revision=?,store=?,last_result=? WHERE id=1 AND revision=? AND store=?',
                    (response['revision'],canonical(response['store']),canonical(response['packet']),revision,body))
                if result.rowcount!=1: raise RuntimeError('Conditional update lost race')
                hook('after_update')
                c.execute('COMMIT')
                hook('after_commit')
            else:
                if response['revision']!=revision or canonical(response['store'])!=body:
                    raise ValueError('Noncommit changed durable store')
                c.execute('ROLLBACK')
            # A successful response is never exposed before COMMIT above.
            return response
        except BaseException:
            if c.in_transaction: c.execute('ROLLBACK')
            raise
        finally:
            c.close()
