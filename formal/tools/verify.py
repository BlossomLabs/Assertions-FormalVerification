"""Verify a complete claim-linked Dafny package and retain fresh native evidence."""
import argparse
import csv
import datetime
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from check import ROOT, LIBRARY, check, digest

TIMEOUT = '/usr/bin/timeout'
LIMIT = ['--signal=TERM', '--kill-after=5s', '900s']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('package')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--wall-seconds', type=int, default=14400)
    parser.add_argument('--run', action='store_true', help='Execute; otherwise print the bound plan.')
    args = parser.parse_args()
    assert args.wall_seconds > 0
    global LIMIT
    LIMIT = ['--signal=TERM', '--kill-after=5s', str(args.wall_seconds) + 's']
    data = check(verbose=args.run)
    if args.package not in data['packages']:
        parser.error('Unknown package')
    package = data['packages'][args.package]
    output = args.output.resolve()
    assert not output.exists(), 'Evidence output must be fresh'
    tools = {'dafny': ROOT / 'proof-tools/assertions/dafny/dafny',
             'Dafny.dll': ROOT / 'proof-tools/assertions/dafny/Dafny.dll',
             'z3': ROOT / 'proof-tools/assertions/dafny/z3/bin/z3-4.12.1',
             'timeout': Path(TIMEOUT)}
    descriptor = next(p['canonicalDescriptor'] for p in json.loads((LIBRARY / 'registry.json').read_text())['packages'] if p['id'] == args.package)
    producer_paths = list((LIBRARY / 'tools').glob('*.py')) + list((LIBRARY / 'dependencies/dafnyevm').glob('*'))
    recipe_manifest = LIBRARY / 'generators/manifest.json'
    producer_paths += [recipe_manifest] + [ROOT / p for p in json.loads(recipe_manifest.read_text())['inputs']]
    producer_paths += [ROOT / descriptor, LIBRARY / 'registry.json', ROOT / 'claims.json', ROOT / 'project.json']
    producer_inputs = {str(p.relative_to(ROOT)): digest(p) for p in producer_paths if p.is_file()}
    commands = []
    for i, entry in enumerate(package['verificationEntries']):
        snapshot = output / 'snapshot' / entry
        commands += [
            (f'proof-{i:03d}', [TIMEOUT] + LIMIT + [str(tools['dafny']), 'verify', str(snapshot),
              '--verify-included-files', '--manual-lemma-induction', '--isolate-assertions',
              '--cores', str(package['resourcePolicy']['cores']), '--verification-time-limit', str(package['resourcePolicy']['secondsPerObligation']), '--solver-path', str(tools['z3']),
              '--log-format', 'csv;LogFileName=' + str(output / f'proof-{i:03d}.csv'), '--progress', 'Symbol']),
            (f'audit-{i:03d}', [TIMEOUT] + LIMIT + [str(tools['dafny']), 'audit', str(snapshot), '--cores', str(package['resourcePolicy']['cores'])])]
    commands.append(('format', [TIMEOUT] + LIMIT + [str(tools['dafny']), 'format', '--check'] +
                     [str(output / 'snapshot' / p) for p in package['closureSha256']]))
    plan = {'package': args.package, 'scope': package['verificationScope'], 'sources': package['closureSha256'],
            'tools': {name: digest(path) for name, path in tools.items()}, 'producerInputs': producer_inputs,
            'pythonVersion': sys.version, 'pythonExecutableSha256': digest(Path(sys.executable).resolve()),
            'commands': [{'gate': label, 'command': command} for label, command in commands],
            'sourceAcceptance': False, 'bytecodeCredit': False}
    if not args.run:
        print(json.dumps(plan, indent=2))
        return
    output.mkdir(parents=True, exist_ok=False)
    for prefix, bindings in [('producer', producer_inputs), ('snapshot', package['closureSha256'])]:
        for relative in bindings:
            target = output / prefix / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, target)
    receipt = dict(plan, status='running', startedAt=datetime.datetime.now(datetime.timezone.utc).isoformat(), results=[])

    def save():
        (output / 'manifest.json').write_text(json.dumps(receipt, indent=2) + '\n')

    save()
    try:
        for label, command in commands:
            with (output / (label + '.log')).open('w') as log:
                process = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, cwd=ROOT)
            text = (output / (label + '.log')).read_text()
            passed = process.returncode == 0 and not re.search(r'Warning:|Error:|timed out|inconclusive', text, re.I)
            result = {'gate': label, 'exitCode': process.returncode}
            if label.startswith('proof-'):
                csv_path = output / (label + '.csv')
                rows = list(csv.DictReader(csv_path.open())) if csv_path.exists() else []
                summary = re.search(r'finished with (\d+) verified, (\d+) errors', text)
                passed &= bool(rows) and all(r['TestResult.Outcome'] == 'Passed' for r in rows)
                passed &= bool(summary) and int(summary[1]) == len(rows) and int(summary[2]) == 0
                result['nativeRows'] = len(rows)
            elif label.startswith('audit-'):
                passed &= 'auditor completed with 0 findings' in text
            else:
                passed &= text.strip() == 'All files are correctly formatted'
            result['passed'] = bool(passed)
            receipt['results'].append(result)
            save()
            if not passed:
                break
        receipt['sourceHashesUnchanged'] = all(digest(ROOT / p) == h for p, h in package['closureSha256'].items())
        receipt['snapshotHashesMatch'] = all(digest(output / 'snapshot' / p) == h for p, h in package['closureSha256'].items())
        receipt['toolHashesUnchanged'] = all(digest(tools[k]) == h for k, h in plan['tools'].items())
        receipt['producerInputsUnchanged'] = all(digest(ROOT / p) == h == digest(output / 'producer' / p) for p, h in producer_inputs.items())
        passed = len(receipt['results']) == len(commands) and all(r['passed'] for r in receipt['results']) and all(receipt[k] for k in ['sourceHashesUnchanged', 'snapshotHashesMatch', 'toolHashesUnchanged', 'producerInputsUnchanged'])
        receipt['status'] = 'native-gates-passed' if passed else 'failed'
    except BaseException as error:
        receipt.update(status='interrupted-or-error', error=str(error))
        raise
    finally:
        receipt['completedAt'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        receipt['evidenceSha256'] = {str(p.relative_to(output)): digest(p) for p in output.rglob('*') if p.is_file() and p.name != 'manifest.json'}
        save()
    print(json.dumps({'status': receipt['status'], 'evidence': str(output), 'results': receipt['results']}))
    if receipt['status'] != 'native-gates-passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
