#!/usr/bin/env python3
"""Verify all earlier frozen artifacts; never rewrite earlier manifests."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DRAFT = ROOT / 'gas-pilot-draft'
MANIFESTS = [
    (ROOT, '.generated/final-manifest-20261013T042649.158919Z.json'),
    (ROOT / 'initializer-memory-draft', 'generated/final-manifest-20261013T051650.320681Z.json'),
    (ROOT / 'initializer-algebra-draft', 'generated/final-manifest-20261013T121025.513202Z.json'),
    (ROOT / 'initializer-matching-draft', 'generated/final-manifest-20261013T124403.899473Z.json'),
    (ROOT / 'initializer-growing-draft', 'generated/final-manifest-20261013T152849.660344Z.json'),
    (ROOT / 'initializer-matching-diagnosis', 'manifest.json'),
    (ROOT / 'initializer-normalized-implication', 'generated/final-manifest-20261013T175841.452161Z.json'),
    (ROOT / 'initializer-extent-decomposition', 'generated/final-manifest-20261013T192443.791658Z.json'),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    records = []
    for base, name in MANIFESTS:
        manifest = base / name
        data = json.loads(manifest.read_text())
        hashes = data['artifactSha256']
        for relative, digest in hashes.items():
            assert sha(base / relative) == digest, str(base / relative)
        records.append({'manifest': str(manifest.relative_to(ROOT)), 'sha256': sha(manifest),
                        'unchangedArtifacts': len(hashes)})
    result = {'previousFrozenManifests': records, 'totalUnchangedArtifacts': sum(r['unchangedArtifacts'] for r in records)}
    assert result['totalUnchangedArtifacts'] == 1642
    (DRAFT / 'generated/preservation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
