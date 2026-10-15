"""Render the public claim index without changing evidence or classifications."""
import argparse
import json
import re
from pathlib import Path
from check_project import check

ROOT = Path(__file__).resolve().parents[1]


def render():
    project = check(verbose=False)
    catalog = json.loads((ROOT / 'claims.json').read_text())
    lines = ['# Assertions claims', '',
             f'Statements and classifications validate Assertions package {project["packageVersion"]} at '
             f'[{project["revision"]}]({project["repository"].removesuffix(".git")}/tree/{project["revision"]}). '
             'Individual contract versions and source hashes are recorded in [project.json](project.json). '
             'Each claim links to its precise scope and evidence references in [claims.json](claims.json). '
             'Full labels retain their stated ABI, resource and execution premises.', '',
             'The retained Halmos baseline passed 382 properties. Source, native, runtime and implication evidence '
             'remain separate; see [the receipt index](evidence-index.json) and [reproduction instructions](README.md).', '',
             '| ID | Claim | Verification | Scope and named theorems |', '|---|---|---|---|']
    source = (ROOT / 'claims.json').read_text()
    for identifier, claim in catalog['claims'].items():
        match = re.search(r'^    "' + re.escape(identifier) + r'": \{', source, re.M)
        line = source.count('\n', 0, match.start()) + 1
        links = ['[Scope](claims.json#L' + str(line) + ')']
        for kind in ['sourceProofs', 'bytecodeProofs']:
            for proof in claim.get(kind, []):
                for theorem in proof['theorems']:
                    name, symbol = theorem['declaration'].rsplit('::', 1)
                    text = (ROOT / name).read_text()
                    found = re.search(r'\b(?:lemma|method)\s+(?:\{:[^}]*\}\s*)*' + re.escape(symbol) + r'\b', text)
                    assert found, theorem['declaration']
                    location = text.count('\n', 0, found.start()) + 1
                    links.append('[' + symbol + '](' + name + '#L' + str(location) + ')')
        statement = claim['statement'].replace('|', '\\|')
        label = claim['verification'].replace('|', '\\|')
        lines.append('| ' + identifier + ' | ' + statement + ' | ' + label + ' | ' + ' · '.join(dict.fromkeys(links)) + ' |')
    lines += ['', 'Retired and inactive statements remain in claims.json with their original records. '
              'The complete predecessor ledgers and immutable raw receipts are retained in the local imported evidence archive.', '']
    return '\n'.join(lines)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    text = render()
    if args.check:
        assert (ROOT / 'CLAIMS.md').read_text() == text, 'Run tools/render.py'
    else:
        (ROOT / 'CLAIMS.md').write_text(text)
    print('PASS: claim index and named theorem links')
