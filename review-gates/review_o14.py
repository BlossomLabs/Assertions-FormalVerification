"""Review O14 as a full-domain consequence of the accepted O13 bytecode proof.

No new native run is claimed: both public-entry theorems already quantify every
u256 calldata word. In particular, 2**255 is the ABI word for int256.min, and
the unsigned-word test M > 0 includes that modulus. The dependency reader checks
the exact theorem interfaces, unrestricted decoder domain, signed specification,
complete native closure, runtime capture, concrete replay and native faults.
"""
import argparse
import hashlib
import json
from pathlib import Path

from check import ROOT, LIBRARY, digest
from declarations import declarations


STATEMENT = 'Signed `addMod`/`mulMod` support int256.min in every operand; zero modulus reverts Panic(0x12)'
DEPENDENCY = 'formal/bytecode/o13/runtime-binding.json'
BINDING = 'formal/bytecode/o14/implication.json'


def validate(dependency_review, binding=None):
    binding = binding or ROOT / BINDING
    fixed = json.loads(binding.read_text())
    ledger = json.loads((ROOT / 'docs/claim-evidence.json').read_text())['claims']['O14']
    assert fixed['schemaVersion'] == 1 and fixed['claim'] == 'O14'
    assert fixed['recordedClaim'] == ledger['recordedClaim'] == STATEMENT, 'Changed O14 statement'
    assert fixed['statementSha256'] == hashlib.sha256(STATEMENT.encode()).hexdigest()
    assert fixed['proofRule'] == 'universal-specialization', 'Unsupported implication rule'
    assert fixed['dependencyClaim'] == 'O13' and fixed['dependencyBinding'] == DEPENDENCY
    assert fixed['dependencyBindingSha256'] == digest(ROOT / DEPENDENCY), 'Dependency binding drift'
    base = json.loads((ROOT / DEPENDENCY).read_text())
    assert base['claim'] == 'O13' and fixed['package'] == base['package'] == 'o13-current-bytecode'
    assert fixed['scope'] == base['scope'], 'Changed O14 execution premises'
    assert fixed['runtimeSha256'] == base['runtimeSha256']
    assert fixed['runtimeLength'] == base['runtimeLength']
    expected = [
        {'declaration': base['proofSource'] + '::' + name,
         'fullSha256': base['declarations'][name]['fullSha256']}
        for name in ['FullAdd', 'FullMul']
    ] + [
        {'declaration': base['coreSource'] + '::RunMatchesKernel',
         'fullSha256': base['coreDeclarations']['RunMatchesKernel']['fullSha256']},
        {'declaration': base['primitivesSource'] + '::Magnitude',
         'fullSha256': base['primitiveDeclarations']['Magnitude']['fullSha256']},
        {'declaration': base['primitivesSource'] + '::RemBounds',
         'fullSha256': base['primitiveDeclarations']['RemBounds']['fullSha256']}
    ]
    assert fixed['theorems'] == expected, 'Incomplete or changed O14 theorem set'
    mapping = json.loads((LIBRARY / 'claims.json').read_text())['claims']['O14']
    assert mapping['recordedClaim'] == STATEMENT and mapping['mappingStatus'] == 'mapped'
    assert mapping['sourceProofs'] == []
    assert mapping['bytecodeProofs'] == [{
        'coverage': 'full', 'package': base['package'], 'obligation': STATEMENT,
        'assumptions': base['scope'], 'mappingReview': 'pending', 'theorems': expected
    }], 'Changed O14 implication mapping'
    # Bind the actual declarations before invoking the dependency review. Neither
    # a mapping label nor a newly rebound hash establishes the implication.
    for theorem in expected:
        relative, symbol = theorem['declaration'].rsplit('::', 1)
        item = declarations(ROOT / relative)[symbol]
        assert hashlib.sha256(item['full'].encode()).hexdigest() == theorem['fullSha256']

    receipt = json.loads(dependency_review.read_text())
    assert receipt['status'] == 'independently-reviewed-exact-bytecode'
    assert receipt['claim'] == 'O13' and receipt['coverage'] == 'full' and receipt['bytecodeCredit']
    assert receipt['binding'] == DEPENDENCY and receipt['bindingSha256'] == digest(ROOT / DEPENDENCY)
    assert receipt['runtimeSha256'] == base['runtimeSha256']
    from review_o13 import validate as validate_o13
    fresh = validate_o13(
        (ROOT / receipt['captureManifest']).parent,
        (ROOT / receipt['nativeManifest']).parent,
        ROOT / receipt['nativeReview'],
        (ROOT / receipt['concrete']).parent,
        (ROOT / receipt['nativeFaults']).parent)
    assert fresh == receipt, 'O13 dependency acceptance changed'
    return {
        'status': 'independently-reviewed-exact-bytecode', 'claim': 'O14',
        'coverage': 'full', 'bytecodeCredit': True, 'recordedClaim': STATEMENT,
        'statementSha256': fixed['statementSha256'], 'package': base['package'],
        'runtimeSha256': base['runtimeSha256'], 'runtimeLength': base['runtimeLength'],
        'proofRule': fixed['proofRule'],
        'dependencyClaim': 'O13',
        'dependencyReview': str(dependency_review.relative_to(ROOT)),
        'dependencyReviewSha256': digest(dependency_review),
        'dependencyNativeRows': fresh['nativeRows'],
        'binding': str(binding.relative_to(ROOT)), 'bindingSha256': digest(binding),
        'theorems': expected, 'scope': fixed['scope'],
        'reviewerSha256': digest(Path(__file__))
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dependency-review', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Review receipt must be fresh'
    result = validate(args.dependency_review.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS exact current O14 bytecode: reviewed implication from',
          result['dependencyNativeRows'], 'O13 native batches; no new native run claimed')


if __name__ == '__main__':
    main()
