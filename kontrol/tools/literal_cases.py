#!/usr/bin/env python3
"""Specialize retained symbolic-content drafts to literal ordinary errors."""
from pathlib import Path

DRAFT = Path(__file__).resolve().parents[1]


def main():
    source = (DRAFT/'specs/guard4.k').read_text()
    choices=[('literal4ordinary','four-byte-ordinary-returns',0xdeadbeef),
             ('literal4threshold','four-byte-threshold-revert',0xdeadbeef)]
    combined=[]
    for name,label,value in choices:
        start=source.index('    claim ['+label+']')
        next_claim=source.find('    claim [',start+1)
        end=next_claim if next_claim>=0 else source.index('endmodule',start)
        claim=source[start:end].replace('HEAD',str(value))
        spec='requires "../../out/kompiled/foundry.k"\n\nmodule GAS-PILOT-'+name.upper()+'\n    imports KONTROL-MAIN\n\n'+claim+'endmodule\n'
        (DRAFT/'specs'/(name+'.k')).write_text(spec)
        combined.append(claim)
    (DRAFT/'specs/literal4.k').write_text('requires "../../out/kompiled/foundry.k"\n\nmodule GAS-PILOT-LITERAL4\n    imports KONTROL-MAIN\n\n'+'\n'.join(combined)+'endmodule\n')


if __name__=='__main__':
    main()
