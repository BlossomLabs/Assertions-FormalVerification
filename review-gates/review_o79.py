"""Independently connect O79's native size theorem to the complete current runtime."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check import ROOT, LIBRARY, digest
from declarations import declarations

STATEMENT = "Operations' runtime bytecode fits EIP-170 (24,576 bytes)"
SCOPE = ('Size of the complete current compiler-produced Operations deployed runtime, '
         'including metadata: 20,894 <= 24,576 bytes, with 3,682 bytes of headroom. '
         'Bound to solc 0.8.36, Cancun, optimizer enabled with 200 runs and the complete '
         'captured compiler request. Static artifact-size property; no execution or '
         'deployment-success claim.')
PACKAGE = 'o79-current-bytecode-size'
PROOF = 'formal/bytecode/o79/Size.dfy'
BINDING = 'formal/bytecode/o79/runtime-binding.json'
REFERENCE = 'formal/bytecode/o13/runtime-binding.json'
compact = lambda value: re.sub(r'\s+', '', value)


def native_results(directory, label, success=True):
    log = (directory / (label + '.log')).read_text()
    with (directory / (label + '.csv')).open() as stream:
        rows = list(csv.DictReader(stream))
    summary = re.search(r'finished with (\d+) verified, (\d+) errors?', log)
    assert rows and summary and not re.search(r'timed out|inconclusive', log, re.I), 'Invalid native result'
    if success:
        assert not re.search(r'Error:', log), 'Native verification error'
        assert int(summary[1]) == len(rows) and int(summary[2]) == 0
        assert all(row['TestResult.Outcome'] == 'Passed' for row in rows)
    else:
        assert int(summary[2]) > 0 and any(row['TestResult.Outcome'] == 'Failed' for row in rows)
    return rows


def validate(capture_dir, native_dir, native_review, native_faults, binding=None):
    binding = binding or ROOT / BINDING
    fixed = json.loads(binding.read_text())
    ledger = json.loads((ROOT / 'docs/claim-evidence.json').read_text())['claims']['O79']
    assert fixed['schemaVersion'] == 1 and fixed['claim'] == 'O79'
    assert fixed['recordedClaim'] == ledger['recordedClaim'] == STATEMENT, 'Changed O79 statement'
    assert fixed['statementSha256'] == hashlib.sha256(STATEMENT.encode()).hexdigest()
    assert fixed['package'] == PACKAGE and fixed['scope'] == SCOPE, 'Changed O79 scope'
    assert fixed['eip170Limit'] == 24576, 'Changed EIP-170 limit'
    assert fixed['runtimeBinding'] == REFERENCE
    assert fixed['runtimeBindingSha256'] == digest(ROOT / REFERENCE), 'Runtime binding drift'
    reference = json.loads((ROOT / REFERENCE).read_text())
    assert reference['claim'] == 'O13'
    for key in ['runtimeSha256', 'runtimeLength']:
        assert fixed[key] == reference[key], 'Changed runtime identity: ' + key
    assert fixed['headroom'] == 24576 - fixed['runtimeLength'] == 3682
    assert fixed['proofSource'] == PROOF and fixed['proofSourceSha256'] == digest(ROOT / PROOF)
    items = declarations(ROOT / PROOF)
    assert set(items) == {'Eip170Limit', 'RuntimeLength', 'FitsEip170'}, 'Changed proof inventory'
    assert re.search(r'^module O79Bytecode \{', (ROOT / PROOF).read_text(), re.M)
    assert not re.search(r'^\s*include\b', (ROOT / PROOF).read_text(), re.M)
    assert compact(items['Eip170Limit']['interface']) == compact('function Eip170Limit(): nat')
    assert compact(items['Eip170Limit']['body']) == '{24576}', 'Changed mathematical size limit'
    assert compact(items['RuntimeLength']['interface']) == compact('function RuntimeLength(): nat')
    assert compact(items['RuntimeLength']['body']) == '{' + str(fixed['runtimeLength']) + '}', 'Changed length premise'
    expected_interface = '''lemma FitsEip170(code: seq<bv8>)
      requires |code| == RuntimeLength()
      ensures |code| <= Eip170Limit()
      ensures Eip170Limit() - |code| == 3682'''
    assert compact(items['FitsEip170']['interface']) == compact(expected_interface), 'Changed theorem scope or result'
    assert compact(items['FitsEip170']['body']) == '{}', 'Changed size proof body'
    for name, item in items.items():
        assert fixed['declarations'][name] == {
            'interfaceSha256': hashlib.sha256(item['interface'].encode()).hexdigest(),
            'fullSha256': hashlib.sha256(item['full'].encode()).hexdigest()}
    theorem = {'declaration': PROOF + '::FitsEip170',
               'fullSha256': fixed['declarations']['FitsEip170']['fullSha256']}
    mapping = json.loads((LIBRARY / 'claims.json').read_text())['claims']['O79']
    assert mapping == {'recordedClaim': STATEMENT, 'mappingStatus': 'mapped', 'sourceProofs': [],
                       'bytecodeProofs': [{'coverage': 'full', 'package': PACKAGE,
                       'obligation': STATEMENT, 'assumptions': SCOPE, 'mappingReview': 'pending',
                       'theorems': [theorem]}]}, 'Changed O79 mapping'

    # Measure decoded bytes of the full deployed runtime. Neither hexadecimal
    # character counts nor metadata-stripped code is the public size claim.
    cap = json.loads((capture_dir / 'manifest.json').read_text())
    assert cap['status'] == 'exact-current-runtime-captured'
    for key in ['runtimeSha256', 'runtimeLength', 'compilerSha256', 'sources', 'settings']:
        assert cap[key] == reference[key], 'Capture binding drift: ' + key
    assert cap['captureScriptSha256'] == digest(LIBRARY / 'tools/capture_o13.py')
    for name in ['input', 'output']:
        assert cap[name + 'Sha256'] == digest(capture_dir / ('solc-' + name + '.json'))
    code = bytes.fromhex((capture_dir / 'runtime.hex').read_text())
    assert len(code) == fixed['runtimeLength'], 'Complete runtime length mismatch'
    assert hashlib.sha256(code).hexdigest() == fixed['runtimeSha256'], 'Complete runtime hash mismatch'
    artifact_path = ROOT / 'artifacts/contracts/Operations.sol/Operations.json'
    artifact = json.loads(artifact_path.read_text())
    assert cap['artifactSha256'] == digest(artifact_path)
    assert artifact['deployedBytecode'] == '0x' + code.hex(), 'Captured code is not the full deployed runtime'
    info_path = ROOT / 'artifacts/build-info' / (artifact['buildInfoId'] + '.json')
    assert cap['hardhatBuildInfoSha256'] == digest(info_path)
    request = json.loads((capture_dir / 'solc-input.json').read_text())
    info = json.loads(info_path.read_text())
    assert info['solcVersion'] == '0.8.36' and info['input'] == request
    assert request['settings'] == reference['settings']
    assert request['settings']['evmVersion'] == 'cancun'
    assert request['settings']['optimizer'] == {'enabled': True, 'runs': 200}
    assert set(request['sources']) == set(reference['sources'])
    for name, source in request['sources'].items():
        expected = reference['sources'][name]
        assert hashlib.sha256(source['content'].encode()).hexdigest() == expected
        if name.startswith('project/'):
            local = ROOT / name[len('project/'):]
        else:
            assert name.startswith('npm/@openzeppelin/contracts@5.6.1/')
            local = ROOT / 'node_modules/@openzeppelin/contracts' / name[len('npm/@openzeppelin/contracts@5.6.1/'):]
        assert digest(local) == expected, 'Current source changed: ' + name
    compiler = ROOT / 'proof-tools/assertions/solc-0.8.36'
    assert digest(compiler) == reference['compilerSha256']
    replay = subprocess.run([str(compiler), '--standard-json'], input=json.dumps(request),
                            capture_output=True, text=True, cwd=ROOT)
    assert replay.returncode == 0, replay.stderr
    compiled = json.loads(replay.stdout)
    assert not any(row['severity'] == 'error' for row in compiled.get('errors', []))
    contract = compiled['contracts']['project/contracts/Operations.sol']['Operations']
    assert contract['evm']['deployedBytecode']['object'] == code.hex(), 'Independent full runtime replay differs'
    assert contract['evm']['bytecode']['object'] == artifact['bytecode'][2:]
    assert not contract['evm']['deployedBytecode']['immutableReferences']

    descriptor = json.loads((LIBRARY / 'packages' / PACKAGE / 'canonical.json').read_text())
    assert descriptor['verificationEntries'] == [PROOF]
    assert descriptor['closureSha256'] == {PROOF: digest(ROOT / PROOF)}
    assert descriptor['resourcePolicy'] == {'cores': 2, 'secondsPerObligation': 30,
                                          'manualLemmaInduction': True, 'isolateAssertions': True}
    native = json.loads((native_dir / 'manifest.json').read_text())
    reviewed = json.loads(native_review.read_text())
    assert native['status'] == 'native-gates-passed' and native['package'] == PACKAGE
    assert native['sources'] == descriptor['closureSha256']
    assert reviewed['status'] == 'independently-reviewed-native-closure' and reviewed['package'] == PACKAGE
    assert reviewed['manifestSha256'] == digest(native_dir / 'manifest.json')
    assert reviewed['declarations'] == 3 and reviewed['producerInputsBound']
    assert reviewed['sourceAcceptance'] is False and reviewed['bytecodeCredit'] is False
    tools = {'dafny': ROOT / 'proof-tools/assertions/dafny/dafny',
             'Dafny.dll': ROOT / 'proof-tools/assertions/dafny/Dafny.dll',
             'z3': ROOT / 'proof-tools/assertions/dafny/z3/bin/z3-4.12.1'}
    assert native['tools'] == {name: digest(path) for name, path in tools.items()}
    source = native_dir / 'snapshot' / PROOF
    assert digest(source) == digest(ROOT / PROOF)
    proof_command = [str(tools['dafny']), 'verify', str(source), '--verify-included-files',
                     '--manual-lemma-induction', '--isolate-assertions', '--cores', '2',
                     '--verification-time-limit', '30', '--solver-path', str(tools['z3']),
                     '--log-format', 'csv;LogFileName=' + str(native_dir / 'proof-000.csv'),
                     '--progress', 'Symbol']
    commands = [{'gate': 'proof-000', 'command': proof_command},
                {'gate': 'audit-000', 'command': [str(tools['dafny']), 'audit', str(source)]},
                {'gate': 'format', 'command': [str(tools['dafny']), 'format', '--check', str(source)]}]
    assert native['commands'] == commands, 'Native command scope or policy changed'
    assert [row['gate'] for row in native['results']] == [row['gate'] for row in commands]
    assert all(row['passed'] and row['exitCode'] == 0 for row in native['results'])
    assert all(native[key] for key in ['sourceHashesUnchanged', 'snapshotHashesMatch',
                                     'toolHashesUnchanged', 'producerInputsUnchanged'])
    for name, value in native['producerInputs'].items():
        assert digest(native_dir / 'producer' / name) == value
    descriptor_name = 'formal/packages/' + PACKAGE + '/canonical.json'
    assert native['producerInputs'][descriptor_name] == digest(ROOT / descriptor_name)
    for name, value in native['evidenceSha256'].items():
        assert digest(native_dir / name) == value
    rows = native_results(native_dir, 'proof-000')
    observed = {row['TestResult.DisplayName'].split(' (')[0] for row in rows}
    assert 'O79Bytecode.FitsEip170' in observed, 'Missing size theorem verification'
    assert observed <= {'O79Bytecode.' + name for name in items}
    assert reviewed['nativeRows'] == len(rows)
    assert 'auditor completed with 0 findings' in (native_dir / 'audit-000.log').read_text()
    assert (native_dir / 'format.log').read_text().strip() == 'All files are correctly formatted'

    faults = json.loads((native_faults / 'manifest.json').read_text())
    assert faults['status'] == 'passed' and faults['originalSourceSha256'] == digest(ROOT / PROOF)
    assert faults['scriptSha256'] == digest(LIBRARY / 'tools/fault_o79_native.py')
    mutations = [('oversized-runtime', '20894', '24577'), ('limit-below-runtime', '24576', '20893')]
    assert [row['name'] for row in faults['results']] == [name for name, _, _ in mutations]
    for row, (name, old, new) in zip(faults['results'], mutations):
        trial = native_faults / name
        assert row['exitCode'] != 0 and row['killedByNativeProof']
        assert (trial / 'Size.dfy').read_text() == (ROOT / PROOF).read_text().replace(old, new)
        for file, value in row['evidenceSha256'].items():
            assert digest(trial / file) == value
        native_results(trial, 'native', success=False)

    # Independently rerun the small complete native closure, including audit and
    # formatting. No O12/O13 execution receipt is used to supply this theorem.
    with tempfile.TemporaryDirectory(prefix='o79-review-', dir=LIBRARY / 'evidence') as temporary:
        directory = Path(temporary)
        command = proof_command.copy()
        command[command.index('--log-format') + 1] = 'csv;LogFileName=' + str(directory / 'proof.csv')
        result = subprocess.run(command, capture_output=True, text=True, cwd=ROOT)
        assert result.returncode == 0, result.stdout + result.stderr
        (directory / 'proof.log').write_text(result.stdout + result.stderr)
        assert len(native_results(directory, 'proof')) == len(rows)
        for gate in commands[1:]:
            result = subprocess.run(gate['command'], capture_output=True, text=True, cwd=ROOT)
            assert result.returncode == 0
            if gate['gate'] == 'audit-000':
                assert 'auditor completed with 0 findings' in result.stdout
            else:
                assert result.stdout.strip() == 'All files are correctly formatted'
    return {'status': 'independently-reviewed-exact-bytecode', 'claim': 'O79',
            'coverage': 'full', 'bytecodeCredit': True, 'recordedClaim': STATEMENT,
            'statementSha256': fixed['statementSha256'], 'package': PACKAGE,
            'runtimeSha256': fixed['runtimeSha256'], 'runtimeLength': len(code),
            'eip170Limit': 24576, 'headroom': 24576 - len(code), 'nativeRows': len(rows),
            'binding': str(binding.relative_to(ROOT)), 'bindingSha256': digest(binding),
            'captureManifest': str((capture_dir / 'manifest.json').relative_to(ROOT)),
            'captureManifestSha256': digest(capture_dir / 'manifest.json'),
            'nativeManifest': str((native_dir / 'manifest.json').relative_to(ROOT)),
            'nativeManifestSha256': digest(native_dir / 'manifest.json'),
            'nativeReview': str(native_review.relative_to(ROOT)), 'nativeReviewSha256': digest(native_review),
            'nativeFaults': str((native_faults / 'manifest.json').relative_to(ROOT)),
            'nativeFaultsSha256': digest(native_faults / 'manifest.json'),
            'nativeReplay': 'passed', 'compilerReplay': 'matched-complete-runtime',
            'theorems': [theorem], 'scope': SCOPE, 'reviewerSha256': digest(Path(__file__))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['capture', 'native', 'native-review', 'native-faults', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Review receipt must be fresh'
    result = validate(args.capture.resolve(), args.native.resolve(), args.native_review.resolve(), args.native_faults.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS O79:', result['runtimeLength'], '<=', result['eip170Limit'], 'bytes;',
          result['headroom'], 'bytes headroom;', result['nativeRows'], 'native batches')


if __name__ == '__main__':
    main()
