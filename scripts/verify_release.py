#!/usr/bin/env python3
"""Portable retained-evidence audit. No installation, compilation or writes."""
import hashlib
import json
from pathlib import Path
import re
import runpy
import tomllib

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((ROOT/'evidence/verification-manifest.json').read_text())
    modules = manifest['modules']
    total = 0
    for module, info in modules.items():
        source, audit = ROOT/info['source'], ROOT/info['audit_log']
        assert sha(source) == info['source_sha256'], ('Source changed', module)
        assert sha(audit) == info['audit_log_sha256'], ('Log changed', module)
        code, log = source.read_text(), audit.read_text()
        body = re.sub(r'/-.*?-/', '', code, flags=re.S)
        body = re.sub(r'--[^\n]*|#print axioms[^\n]*', '', body)
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', body), module
        assert not re.search(r'\b(error|warning)\b|sorryAx', log), module
        names = re.findall(r'#print axioms ([\w.]+)', code)
        audited = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", log, re.S)
        assert names == info['audited_declarations'] == [n for n, _ in audited], module
        assert names, module
        for name, axioms in audited:
            assert not set(x.strip() for x in axioms.split(',') if x.strip())-STANDARD, name
        for line in re.findall(r'^import\s+([^\n]+)', code, re.M):
            for imported in line.split():
                assert imported.startswith(('Mathlib', 'Lean.', 'FixedPointTheorems')) or imported in modules, (module, imported)
        total += len(names)
    assert len(modules) == manifest['module_count']
    assert total == manifest['audited_endpoints']
    config = tomllib.loads((ROOT/'lakefile.toml').read_text())
    deps = json.loads((ROOT/'lake-manifest.json').read_text())
    revisions = {p['name']:p['rev'] for p in deps['packages']}
    assert revisions == manifest['dependency_revisions']
    for required in config['require']:
        assert required['rev'] == revisions[required['name']]
    library = next(x for x in config['lean_lib'] if x['name'] == 'ProductiveOwnership')
    assert set(library['roots']) == set(modules)-{'GEOverlap'}
    assert (ROOT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
    control = manifest['controls']
    assert sha(ROOT/control['source']) == control['source_sha256']
    assert sha(ROOT/control['receipt']) == control['receipt_sha256']
    result = runpy.run_path(str(ROOT/control['source']))['check']()
    assert result == json.loads((ROOT/control['receipt']).read_text())
    assert result['passed']
    for relative, info in manifest.get('runtime_artifacts', {}).items():
        assert sha(ROOT/relative) == info['sha256'], ('Runtime/evidence changed', relative)
    backend = json.loads((ROOT/'evidence/controls/sqlite_backend.json').read_text())
    demo = json.loads((ROOT/'evidence/controls/connected_demo.json').read_text())
    assert backend['passed'] and demo['passed']
    assert backend['counts']['process_exit_faults'] == 6
    assert backend['counts']['actual_two_connection_schedules'] == 8
    assert demo['witness_sha256'] == sha(ROOT/'evidence/controls/connected_witness.json')
    print(f'PASS: {len(modules)} source-identical modules; {total} retained declaration audits; standard foundations only.')
    print(f"PASS: {result['named_controls']} controls, {result['exact_refund_cases']} exact refund cases, {result['generated_attempts']} generated attempts.")
    print('PASS: import closure, pinned dependencies and configured library roots. No Lean module rebuilt.')
    print('PASS: retained SQLite and connected-demo source/evidence bindings; these runtime controls were not rerun.')
    print('This audits retained evidence; run lake build separately for a fresh kernel build.')


if __name__ == '__main__':
    main()
