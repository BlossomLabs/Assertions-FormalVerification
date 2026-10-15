#!/usr/bin/env python3
"""Append-only finite-gas pilot runner; earlier proof trees are read-only."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'
IMAGE = json.loads((ROOT / 'toolchain.json').read_text())['dockerImage']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('name')
    parser.add_argument('--seconds', type=int, default=600)
    boundary = sys.argv.index('--')
    args = parser.parse_args(sys.argv[1:boundary])
    command = sys.argv[boundary + 1:]
    assert command and 0 < args.seconds <= 1200
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    stem = stamp + '-' + args.name
    log = DRAFT / 'receipts' / (stem + '.log')
    receipt = log.with_suffix('.json')
    container = 'assertions-kontrol-gas-' + re.sub('[^a-z0-9_.-]', '-', stem.lower())
    argv = ['timeout', '--verbose', '--signal=TERM', '--kill-after=10', str(args.seconds),
            'docker', 'run', '--rm', '--network', 'none', '--cpus', '2', '--name', container,
            '--memory', '6g', '--memory-swap', '6g', '--group-add', str(os.getgid()),
            '--cap-drop', 'ALL', '--security-opt', 'no-new-privileges',
            '-e', 'KPROFILE_TELEMETRY_DISABLED=true',
            '-v', f'{ROOT}:/workspace:ro', '-v', f'{DRAFT}:/workspace/gas-pilot-draft:rw',
            '-w', '/workspace', IMAGE, 'bash', '-c',
            'umask 0002; "$@"; pilot_code=$?; chmod -R g+rwx gas-pilot-draft 2>/dev/null; exit "$pilot_code"',
            'pilot', *command]
    paths = [*DRAFT.rglob('*'), *(ROOT / 'out/kompiled').rglob('*')]
    paths += [ROOT / name for name in ['toolchain.json', 'target/runtime.bin', 'target/binding.json',
              'target/compile-binding.json', '.generated/specs/jump-map.bin',
              '.generated/exact-artifact.json', '.generated/compiler-input.json',
              '.generated/compiler-output.json', '.generated/audit-final-3/imports.json']]
    inputs = {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths) if p.is_file()}
    started = time.monotonic()
    cleanup = []
    with log.open('x') as output:
        interruption = None
        try:
            process_code = subprocess.run(argv, stdout=output, stderr=subprocess.STDOUT).returncode
        except (KeyboardInterrupt, OSError) as error:
            interruption = {'type': type(error).__name__, 'message': str(error)}
            process_code = 130 if isinstance(error, KeyboardInterrupt) else 1
            output.write(json.dumps({'runnerInterruption': interruption}) + '\n')
        finally:
            if subprocess.run(['docker', 'inspect', container], stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL).returncode == 0:
                for cleanup_argv in [['docker', 'stop', '--timeout', '5', container],
                                     ['docker', 'rm', '-f', container]]:
                    result = subprocess.run(cleanup_argv, stdout=output, stderr=subprocess.STDOUT)
                    cleanup.append({'argv': cleanup_argv, 'exitCode': result.returncode})
    elapsed = time.monotonic() - started
    record = {'name': args.name, 'timestampUtc': stamp, 'argv': argv, 'elapsedSeconds': elapsed,
              'exitCode': process_code, 'interruption': interruption,
              'timedOut': process_code == 124 or (process_code == 137 and elapsed >= args.seconds),
              'inputSha256': inputs, 'containerName': container, 'cleanup': cleanup,
              'log': log.name, 'logSha256': sha(log)}
    with receipt.open('x') as output:
        json.dump(record, output, indent=2)
        output.write('\n')
    print(json.dumps({k: record[k] for k in ['name', 'elapsedSeconds', 'exitCode', 'timedOut', 'log']}), flush=True)
    print(log.read_text()[-18000:], flush=True)
    sys.exit(process_code)


if __name__ == '__main__':
    main()
