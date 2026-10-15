"""Build an isolated Assertions workspace with the frozen verification sources."""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path
from check_project import check

ROOT = Path(__file__).resolve().parents[1]


def prepare(source, output, candidate=None):
    project = check(verbose=False)
    assert not output.exists(), 'Workspace must be fresh'
    revision = candidate or project['revision']
    assert re.fullmatch('[0-9a-f]{40}', revision), 'Use an exact Assertions commit'
    subprocess.run(['git', 'clone', '--no-hardlinks', '--no-checkout', str(source), str(output)], check=True)
    subprocess.run(['git', '-C', str(output), 'checkout', '--detach', revision], check=True)
    for name, expected in project['overlaySha256'].items():
        path = ROOT / 'halmos' / name
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
    for name in ['verify-claims.py']:
        shutil.copy2(ROOT / 'halmos' / name, output / 'scripts' / name)
    if not candidate:
        for name, expected in {**project['sourceSha256'], **project['configurationSha256']}.items():
            assert hashlib.sha256((output / name).read_bytes()).hexdigest() == expected, 'Frozen workspace drift: ' + name
        check(output, verbose=False)
    print('Prepared', output, 'at', revision)
    if candidate:
        print('Candidate runs are new regression checks; historical acceptance does not transfer.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, help='Assertions Git repository path or URL')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--candidate', help='Test another exact revision without granting it historical proof credit')
    args = parser.parse_args()
    prepare(args.source, args.output.resolve(), args.candidate)
