"""Check imported receipt bytes, native results and source identity without reproving."""
import csv
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def audit():
    index = json.loads((ROOT / 'evidence-index.json').read_text())
    native_seen = set()
    for name, expected in json.loads((ROOT / 'review-gates/index.json').read_text()).items():
        assert sha(ROOT / 'review-gates' / name) == expected, 'Frozen acceptance gate drift: ' + name
    for kind in ['source', 'bytecode']:
        for identifier, record in index[kind].items():
            project_root = ROOT / record.get('projectRoot', 'evidence/imported/project')
            path = ROOT / record['review']
            assert sha(path) == record['sha256'], 'Receipt changed: ' + identifier
            receipt = json.loads(path.read_text())
            for support in record.get('supportingReceipts', []):
                assert sha(project_root / support['path']) == support['sha256'], 'Supporting receipt drift'
            for attempt in record.get('retainedAttempts', []):
                path = project_root / attempt['manifest']
                assert sha(path) == attempt['sha256'], 'Retained incomplete attempt drift'
                incomplete = json.loads(path.read_text())
                assert incomplete['status'] == attempt['status'] == 'failed'
                assert not all(r['passed'] for r in incomplete['results']), 'Incomplete attempt cannot grant proof credit'
                for name, expected in incomplete['evidenceSha256'].items():
                    assert sha(path.parent / name) == expected, 'Retained attempt artifact drift'
            if 'nativeManifest' not in receipt:
                continue
            native_path = project_root / receipt['nativeManifest']
            assert sha(native_path) == receipt['nativeManifestSha256']
            if native_path in native_seen:
                continue
            native_seen.add(native_path)
            native = json.loads(native_path.read_text())
            assert native['status'] == 'native-gates-passed'
            assert all(r['passed'] and r['exitCode'] == 0 for r in native['results'])
            for name, expected in native['sources'].items():
                assert sha(ROOT / name) == expected, 'Imported proof source drift: ' + name
            for name, expected in native['evidenceSha256'].items():
                assert sha(native_path.parent / name) == expected, 'Imported artifact drift'
            for result in native['results']:
                if result['gate'].startswith('proof-'):
                    rows = list(csv.DictReader((native_path.parent / (result['gate'] + '.csv')).open()))
                    assert len(rows) == result['nativeRows'] and all(r['TestResult.Outcome'] == 'Passed' for r in rows)
    halmos = index['halmos']
    assert sha(ROOT / halmos['manifest']) == halmos['manifestSha256']
    assert sha(ROOT / halmos['review']) == halmos['reviewSha256']
    manifest = json.loads((ROOT / halmos['manifest']).read_text())
    assert manifest['summary'] == {'passed': 382, 'failed': 0, 'incomplete': 0}
    assert len(manifest['results']) == manifest['inventoryCount'] == 382
    base = (ROOT / halmos['manifest']).parent
    for result in manifest['results']:
        assert result['status'] == 'passed' and result['exitCode'] == 0 and not result.get('warnings')
        assert result['halmos']['num_models'] == result['halmos']['num_bounded_loops'] == 0
        assert (base / result['log']).is_file() and (base / result['json']).is_file()
    pilot = ROOT / 'evidence/imported/kontrol-proofs/gas-pilot-draft'
    manifest = json.loads((pilot / 'generated/oog-manifest-20261013T212000.704751Z.json').read_text())
    for name, expected in manifest['artifactSha256'].items():
        assert sha(pilot / name) == expected, 'Kontrol imported artifact drift: ' + name
    catalog = json.loads((ROOT / 'claims.json').read_text())
    for identifier, row in {**catalog['claims'], **catalog['historicalClaims']}.items():
        statement = row.get('statement', row.get('recordedClaim'))
        assert hashlib.sha256(statement.encode()).hexdigest() == catalog['statementSha256'][identifier]
    print(f'PASS: immutable imported evidence, {len(native_seen)} native closures, 382 Halmos results and finite-gas packet. No new proof run.')


if __name__ == '__main__':
    audit()
