"""Recreate the frozen discovery traces from small concrete input recipes.

These traces guide proof generation. They do not establish universal coverage;
the accepted Dafny obligations and runtime reviews remain the proof evidence.
"""
import hashlib
import json
from pathlib import Path


def replay(root, recipes):
    from eth.vm.forks.cancun import CancunVM
    from eth.vm.chain_context import ChainContext
    from eth.db.atomic import AtomicDB
    from eth.vm.message import Message
    from eth.vm.logic.invalid import InvalidOpcode
    from eth.exceptions import Halt

    state = CancunVM.build_state(AtomicDB(), CancunVM.create_genesis_header(
        difficulty=0, gas_limit=30_000_000, timestamp=1), ChainContext(1))
    address = bytes.fromhex('11' * 20)
    for group, cases in recipes.items():
        contract = 'Assertions' if group == 'c50' else 'Operations'
        artifact = root / f'artifacts/contracts/{contract}.sol/{contract}.json'
        code = bytes.fromhex(json.loads(artifact.read_text())['deployedBytecode'][2:])
        rows = []
        for seed in cases:
            data = seed.get('calldata')
            if data is None:
                data = seed['selector'] + ''.join(
                    (v % (1 << 256)).to_bytes(32, 'big').hex() for v in seed['arguments'])
            message = Message(gas=100000, to=address, sender=address, value=0,
                              data=bytes.fromhex(data), code=code, is_static=True)
            context = state.get_transaction_context_class()(gas_price=0, origin=address)
            computation = state.computation_class(state, message, context)
            trace, iterator = [], iter(computation.code)
            with computation:
                for _ in range(1000):
                    pc, op = computation.code.program_counter, next(iterator)
                    stack = [int.from_bytes(v, 'big') if isinstance(v, bytes) else v
                             for v in reversed(computation._stack.values)]
                    row = dict(pc=pc, opcode=op, stack=stack, gas=computation.get_gas_remaining())
                    if group != 'o13':
                        row['memory'] = bytes(computation._memory._bytes).hex()
                    trace.append(row)
                    try:
                        computation.opcodes.get(op, InvalidOpcode(op))(computation=computation)
                    except Halt:
                        break
                else:
                    raise AssertionError('Discovery trace did not terminate')
            encoded = json.dumps(trace, sort_keys=True, separators=(',', ':')).encode()
            assert hashlib.sha256(encoded).hexdigest() == seed['traceSha256'], 'Frozen trace drift'
            assert len(trace) == seed['steps']
            assert 100000 - computation.get_gas_remaining() == seed['gasUsed']
            assert computation.output.hex() == seed['data']
            assert computation.is_error == seed.get('error', seed.get('revert'))
            row = {k: v for k, v in seed.items() if k not in ['traceSha256', 'calldata']}
            rows.append(dict(row, trace=trace))
        target = root / f'proofs/{group}-bytecode/exploration.json'
        target.write_text(json.dumps(rows[0] if group == 'c50' else {'paths': rows}))
