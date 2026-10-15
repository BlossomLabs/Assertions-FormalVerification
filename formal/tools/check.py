"""Check the selected claim proof packages without running a solver."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LIBRARY = ROOT / 'formal'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(*, verbose=True):
    from generate import bindings
    from evm_dependency import closure, external_sources
    from declarations import declarations
    from declaration_body import mask_literals_and_comments
    for name in bindings():
        assert (ROOT / name).is_file(), 'Missing generated proof; run formal/tools/generate.py: ' + name
    external = external_sources()
    registry = json.loads((LIBRARY / 'registry.json').read_text())
    catalog = json.loads((ROOT / 'claims.json').read_text())
    packages, local = {}, {}
    for record in registry['packages']:
        descriptor = ROOT / record['canonicalDescriptor']
        package = json.loads(descriptor.read_text())
        assert package['id'] == record['id'] and package['id'] not in packages
        assert closure([ROOT / p for p in package['verificationEntries']]) == package['closureSha256'], 'Closure drift: ' + package['id']
        for name, value in package['closureSha256'].items():
            if name.startswith('formal/'):
                local[name] = value
            else:
                assert external.get(name) == value, 'Unpinned semantics: ' + name
        packages[package['id']] = package
    actual = {str(p.relative_to(ROOT)) for base in ['source', 'bridges', 'bytecode'] for p in (LIBRARY / base).rglob('*.dfy')}
    assert actual == set(local), 'Orphan or missing proof source'
    parsed = {}
    for name in local:
        path = ROOT / name
        assert not path.is_symlink() and path.resolve() == path
        assert not re.search(r'\bassume\b|\{:axiom\b|\{:verify\s+false\b', mask_literals_and_comments(path.read_text())), 'Admission: ' + name
        parsed[name] = declarations(path)
    used = set()
    for claim in catalog['claims'].values():
        for kind in ['sourceProofs', 'bytecodeProofs']:
            for proof in claim.get(kind, []):
                used.add(proof['package'])
                assert proof['package'] in packages
                for theorem in proof['theorems']:
                    name, symbol = theorem['declaration'].rsplit('::', 1)
                    assert name in packages[proof['package']]['closureSha256']
                    assert hashlib.sha256(parsed[name][symbol]['full'].encode()).hexdigest() == theorem['fullSha256'], 'Theorem drift'
    assert used == set(packages), 'Package without a supporting claim'
    project = json.loads((ROOT / 'project.json').read_text())
    for name, expected in project['overlaySha256'].items():
        assert digest(ROOT / 'halmos' / name) == expected, 'Harness drift: ' + name
    assert digest(ROOT / 'halmos/verify-claims.py') == project['halmos']['runnerSha256']
    if verbose:
        print(f'PASS: {len(packages)} packages, {len(local)} local Dafny sources, {len(project["halmosSources"])} Halmos harnesses. Hash consistency is not new proof acceptance.')
    return {'packages': packages}


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    check()
