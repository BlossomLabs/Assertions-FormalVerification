"""Native negative controls for O79's size theorem in fresh isolated snapshots."""
import argparse
import csv
import json
from pathlib import Path
import re
import subprocess

from check import ROOT, LIBRARY, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    assert not output.exists(), 'Fault output must be fresh'
    output.mkdir(parents=True)
    source = LIBRARY / 'bytecode/o79/Size.dfy'
    original = source.read_text()
    results = []
    for name, old, new in [('oversized-runtime', '20894', '24577'),
                           ('limit-below-runtime', '24576', '20893')]:
        trial = output / name
        trial.mkdir()
        mutated = original.replace(old, new)
        assert mutated != original
        path = trial / 'Size.dfy'
        path.write_text(mutated)
        command = [str(ROOT / 'proof-tools/assertions/dafny/dafny'), 'verify', str(path),
                   '--verify-included-files', '--manual-lemma-induction', '--isolate-assertions',
                   '--cores', '2', '--verification-time-limit', '30', '--solver-path',
                   str(ROOT / 'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'),
                   '--log-format', 'csv;LogFileName=' + str(trial / 'native.csv')]
        result = subprocess.run(command, capture_output=True, text=True, cwd=ROOT)
        log = result.stdout + result.stderr
        (trial / 'native.log').write_text(log)
        with (trial / 'native.csv').open() as stream:
            rows = list(csv.DictReader(stream))
        summary = re.search(r'finished with (\d+) verified, (\d+) errors?', log)
        killed = (result.returncode != 0 and summary is not None and int(summary[2]) > 0
                  and any(row['TestResult.Outcome'] == 'Failed' for row in rows)
                  and not re.search(r'timed out|inconclusive', log, re.I))
        results.append({'name': name, 'command': command, 'exitCode': result.returncode,
                        'killedByNativeProof': bool(killed),
                        'evidenceSha256': {file: digest(trial / file)
                                          for file in ['Size.dfy', 'native.log', 'native.csv']}})
        assert killed, name + ': ' + log
    (output / 'manifest.json').write_text(json.dumps({
        'status': 'passed', 'scriptSha256': digest(Path(__file__)),
        'originalSourceSha256': digest(source), 'results': results}, indent=2) + '\n')
    print('Passed', len(results), 'native size faults with verification failures and no timeouts')


if __name__ == '__main__':
    main()
