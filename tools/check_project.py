"""Identify the validated contract versions and optionally compare local sources."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check(source=None, *, verbose=True):
    project = json.loads((ROOT / 'project.json').read_text())
    catalog = json.loads((ROOT / 'claims.json').read_text())
    assert re.fullmatch('[0-9a-f]{40}', project['revision']), 'Use an exact Assertions revision'
    assert catalog['projectRevision'] == project['revision'], 'Claims target a different source revision'
    production = {name: value for name, value in project['sourceSha256'].items()
                  if 'tests' not in Path(name).parts}
    versions = project['contractVersions']
    assert {f'contracts/{name}.sol' for name in versions} == {
        name for name in production if Path(name).parent == Path('contracts')}, 'Incomplete contract version inventory'
    assert project['packageVersion'] and all(versions.values())
    if source is not None:
        actual = {str(p.relative_to(source)): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (source / 'contracts').rglob('*.sol') if 'tests' not in p.parts}
        assert actual == production, 'Local contracts differ from the validated source snapshot'
        assert json.loads((source / 'package.json').read_text())['version'] == project['packageVersion'], 'Package version drift'
        for name, version in versions.items():
            declaration = re.search(r'@custom:version\s+(\S+)', (source / f'contracts/{name}.sol').read_text())
            assert declaration and declaration[1] == version, 'Contract version drift: ' + name
    if verbose:
        print(f'Assertions {project["packageVersion"]} at {project["revision"]}; ' +
              ', '.join(f'{name} {version}' for name, version in versions.items()))
        if source is not None:
            print('PASS: local contract versions and sources match the validated snapshot')
    return project


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, help='Optional Assertions checkout to compare with the validated contracts')
    check(parser.parse_args().source)
