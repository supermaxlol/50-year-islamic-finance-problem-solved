#!/usr/bin/env python3
"""Portable launch configuration for the retained backend control source."""
import os
from pathlib import Path
import runpy
import shutil

STAGE=Path(__file__).resolve().parent
ROOT=STAGE.parent
def core_command():
    return ['lake','env','lean','--run',str(STAGE/'PersistentBridge.lean')],dict(os.environ),str(ROOT)

if __name__=='__main__':
    if shutil.disk_usage(STAGE).free<2*1024**3:raise RuntimeError('At least 2 GiB free space required.')
    (STAGE/'logs').mkdir(exist_ok=True)
    runpy.run_path(str(STAGE/'check_backend.py'),run_name='__main__')
