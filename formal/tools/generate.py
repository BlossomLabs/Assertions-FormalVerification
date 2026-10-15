"""Regenerate expanded proofs; require byte identity with the accepted sources."""
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RECIPES = ROOT / 'formal/generators'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bindings():
    manifest = json.loads((RECIPES / 'manifest.json').read_text())
    inputs = {str(p.relative_to(ROOT)) for p in RECIPES.rglob('*')
              if p.is_file() and '__pycache__' not in p.parts and p.name != 'manifest.json'}
    inputs.add('formal/tools/generate.py')
    assert set(manifest['inputs']) == inputs, 'Unbound generation input'
    for name, expected in manifest['inputs'].items():
        assert digest(ROOT / name) == expected, 'Generation input drift: ' + name
    outputs = json.loads((RECIPES / 'outputs.json').read_text())
    closures = {}
    for path in (ROOT / 'formal/packages').glob('*/canonical.json'):
        closures.update(json.loads(path.read_text())['closureSha256'])
    assert outputs and all(closures.get(p) == h for p, h in outputs.items()), 'Accepted output binding drift'
    for name in outputs:
        assert re.fullmatch(r'formal/bytecode/(c50|o2|o12|o13)/\w+\.dfy', name)
    return outputs


def compile_runtime(project, stage):
    compiler = ROOT / 'proof-tools/assertions/solc-0.8.36'
    bindings = {name: json.loads((ROOT / f'formal/bytecode/{name}/runtime-binding.json').read_text())
                for name in ['c50', 'o2', 'o12', 'o13']}
    binding = bindings['o13']
    assert digest(compiler) == binding['compilerSha256'], 'Compiler drift'
    sources = {}
    for name, expected in binding['sources'].items():
        if name.startswith('project/'):
            source = project / name.removeprefix('project/')
        else:
            prefix = 'npm/@openzeppelin/contracts@5.6.1/'
            assert name.startswith(prefix)
            source = project / 'node_modules/@openzeppelin/contracts' / name.removeprefix(prefix)
        assert digest(source) == expected, 'Frozen compiler source drift: ' + name
        sources[name] = {'content': source.read_text()}
    request = dict(language='Solidity', sources=sources, settings=binding['settings'])
    input_path, output_path = stage / 'compiler-input.json', stage / 'compiler-output.json'
    input_path.write_text(json.dumps(request))
    with input_path.open() as inp, output_path.open('w') as out:
        subprocess.run([str(compiler), '--standard-json'], stdin=inp, stdout=out, check=True)
    compiled = json.loads(output_path.read_text())
    assert not any(e['severity'] == 'error' for e in compiled.get('errors', []))
    for group, contract in [('c50', 'Assertions'), ('o2', 'Operations'), ('o12', 'Operations'), ('o13', 'Operations')]:
        bound = bindings[group]
        assert bound['sources'] == binding['sources'] and bound['settings'] == binding['settings']
        evm = compiled['contracts'][f'project/contracts/{contract}.sol'][contract]['evm']
        runtime = bytes.fromhex(evm['deployedBytecode']['object'])
        assert hashlib.sha256(runtime).hexdigest() == bound['runtimeSha256'], 'Runtime drift'
        assert len(runtime) == bound['runtimeLength']
        target = stage / f'artifacts/contracts/{contract}.sol/{contract}.json'
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps({'deployedBytecode': '0x' + runtime.hex()}))
        if group == 'o2':
            target = stage / 'formal/evidence/o2-runtime-capture-20261015-v1/runtime.hex'
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(runtime.hex() + '\n')
        elif group != 'c50':
            date = '20261014' if group == 'o12' else '20261015'
            for version in ['v1', 'v2']:
                target = stage / f'formal/evidence/{group}-current-capture-{date}-{version}/runtime.hex'
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(runtime.hex() + '\n')


def regenerate(project, destination):
    outputs = bindings()
    recipe_digest = digest(RECIPES / 'manifest.json')
    for name, expected in outputs.items():
        target = destination / name
        assert not target.is_symlink(), 'Generated source is a symlink: ' + name
        assert not target.exists() or digest(target) == expected, 'Refusing to overwrite changed source: ' + name
    with tempfile.TemporaryDirectory(prefix='assertions-proof-generation-') as temporary:
        stage = Path(temporary)
        shutil.copytree(ROOT / 'formal', stage / 'formal', ignore=shutil.ignore_patterns('__pycache__'))
        # Do not read a previous expansion as a generator input.
        for name in outputs:
            (stage / name).unlink(missing_ok=True)
        (stage / 'proof-tools').symlink_to(ROOT / 'proof-tools', target_is_directory=True)
        for group in ['c50', 'o2', 'o12', 'o13']:
            target = stage / f'proofs/{group}-bytecode'
            target.mkdir(parents=True)
            for script in (RECIPES / group).glob('*.py'):
                shutil.copy2(script, target / script.name)
        compile_runtime(project, stage)
        sys.path.insert(0, str(ROOT / 'proof-tools/evm-python'))
        spec = importlib.util.spec_from_file_location('replay', RECIPES / 'replay.py')
        replay = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(replay)
        replay.replay(stage, json.loads((RECIPES / 'cases.json').read_text()))

        def run(group, script):
            subprocess.run([sys.executable, '-B', str(stage / f'proofs/{group}-bytecode' / script)],
                           cwd=stage, check=True)

        for group, script in [('c50', 'generate_prototype.py'), ('o2', 'generate_entry.py'), ('o12', 'generate_entry.py')]:
            run(group, script)
            shutil.copy2(stage / f'proofs/{group}-bytecode/Entry.dfy', stage / f'formal/bytecode/{group}/Entry.dfy')
        for script in ['generate_macro.py', 'split_macro.py', 'generate_helpers.py']:
            run('o13', script)
        for name in ['Stacks', 'Helpers']:
            text = (stage / f'proofs/o13-bytecode/{name}.dfy').read_text()
            text = text.replace('include "../../formal/bytecode/o13/Core.dfy"', 'include "Core.dfy"')
            (stage / f'formal/bytecode/o13/{name}.dfy').write_text(text)
        for path in (stage / 'formal/bytecode/o13').glob('Blocks*.dfy'):
            path.write_text(path.read_text().replace('include "Core.dfy"', 'include "Helpers.dfy"'))
        dafny = ROOT / 'proof-tools/assertions/dafny/dafny'
        tools = json.loads((ROOT / 'formal/dependencies/dafnyevm/tools.json').read_text())
        for name, expected in tools['installed'].items():
            assert digest(ROOT / 'proof-tools/assertions' / name) == expected, 'Formatter tool drift'
        paths = sorted((stage / 'formal/bytecode/o13').glob('*.dfy'))
        subprocess.run([str(dafny), 'format'] + list(map(str, paths)), cwd=stage, check=True)
        run('o13', 'explicit_all_v7.py')
        entry = stage / 'formal/bytecode/o13/Entry.dfy'
        text, count = re.subn(r'^    assert next==Run\(st,\d+\);$', '', entry.read_text(), flags=re.M)
        assert count == 1397, ('Entry composition layout drift', count)
        entry.write_text(text)
        subprocess.run([str(dafny), 'format'] + list(map(str, paths)), cwd=stage, check=True)
        subprocess.run(['git', 'apply', str(RECIPES / 'o13/repairs.patch')], cwd=stage, check=True)
        for name, expected in outputs.items():
            assert digest(stage / name) == expected, 'Regenerated proof differs from accepted bytes: ' + name
        assert digest(RECIPES / 'manifest.json') == recipe_digest, 'Recipe changed during generation'
        assert bindings() == outputs  # Refuse input changes during generation.
        for name in outputs:
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            assert not target.exists() or digest(target) == outputs[name], 'Source changed during generation'
            shutil.copy2(stage / name, target)
    print(f'PASS: regenerated {len(outputs)} proof files; every byte matches the accepted closure. No new proof credit.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=ROOT / 'workspace', help='Pinned Assertions checkout with installed npm dependencies')
    parser.add_argument('--output', type=Path, default=ROOT, help='Repository-shaped destination for the regenerated sources')
    parser.add_argument('--check', action='store_true', help='Check recipes and existing expansions without regenerating')
    args = parser.parse_args()
    if args.check:
        outputs = bindings()
        for name, expected in outputs.items():
            assert (args.output / name).is_file() and digest(args.output / name) == expected, 'Run formal/tools/generate.py: ' + name
        print(f'PASS: {len(outputs)} accepted generated sources and pinned recipes')
    else:
        regenerate(args.project.resolve(), args.output.resolve())


if __name__ == '__main__':
    main()
