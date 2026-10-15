"""Concrete cross-checks of the captured public-entry path, with byte mutants."""
import argparse,hashlib,json,random,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--capture',type=Path,required=True);parser.add_argument('--interpreter',type=Path,required=True);parser.add_argument('--python-deps',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();assert not args.output.exists();args.output.mkdir(parents=True)
sys.path[:0]=[str(args.interpreter.resolve()),str(args.python_deps.resolve())]
import _dafny,EVM,EvmFork,EvmState,Precompiled,Code,C50Bytecode
from eth.vm.forks.cancun import CancunVM
from eth.vm.chain_context import ChainContext
from eth.db.atomic import AtomicDB
from eth.vm.message import Message
from eth.vm.logic.invalid import InvalidOpcode
from eth.exceptions import Halt,Revert
from eth_utils import keccak
CODE=bytes.fromhex((args.capture/'runtime.hex').read_text())
SELECTOR=keccak(text='chain((uint8,uint8,bytes,(uint8,bytes)[]),bytes[])')[:4]
EXPECTED=keccak(text='EmptyCallChain()')[:4].hex()
def unavailable(*args):raise AssertionError('Unexpected external backend call')
BACKEND=Precompiled.T_Dispatcher(unavailable,unavailable)
HEADER=CancunVM.create_genesis_header(difficulty=0,gas_limit=30_000_000,timestamp=1)
STATE=CancunVM.build_state(AtomicDB(),HEADER,ChainContext(1));ADDRESS=bytes.fromhex('11'*20)
SCOPE={0x01,0x03,0x10,0x11,0x12,0x14,0x15,0x1b,0x1c,0x34,0x35,0x36,0x50,0x51,0x52,0x56,0x57,0x5b,0x5f,0x60,0x61,0x63,0xfd,*range(0x80,0xa0)}
def dafny(data,code=CODE,gas=100000):
 st=EVM.default__.Init(gas,BACKEND,EvmFork.default__.CANCUN,_dafny.Seq([]),_dafny.Seq(code))
 st=EvmState.State_EXECUTING(st.evm._replace(context=st.evm.context._replace(callData=_dafny.Seq(data))))
 trace=[]
 for _ in range(1000):
  if not st.is_EXECUTING:break
  pc=st.evm.pc;assert code[pc] in SCOPE,'Unexpected opcode in claimed execution path'
  trace.append(pc);st=EVM.default__.Execute(st)
 else:raise AssertionError('Concrete exploration did not terminate')
 assert st.is_ERROR,'Expected a terminated error state'
 return {'kind':'revert' if isinstance(st.error,EvmState.Error_REVERTS) else 'OutOfGas' if isinstance(st.error,EvmState.Error_INSUFFICIENT__GAS) else str(st.error),'data':bytes(st.data).hex(),'gas':st.gas,'trace':trace}
def independent(data,code=CODE,gas=100000):
 msg=Message(gas=gas,to=ADDRESS,sender=ADDRESS,value=0,data=data,code=code,is_static=True)
 ctx=STATE.get_transaction_context_class()(gas_price=0,origin=ADDRESS);comp=STATE.computation_class(STATE,msg,ctx);trace=[]
 iterator=iter(comp.code)
 with comp:
  for _ in range(1000):
   pc=comp.code.program_counter;op=next(iterator);trace.append(pc)
   try:comp.opcodes.get(op,InvalidOpcode(op))(computation=comp)
   except Halt:break
  else:raise AssertionError('Independent EVM exploration did not terminate')
 return {'kind':'revert' if comp.is_error and isinstance(comp.error,Revert) else type(comp.error).__name__ if comp.is_error else 'success','data':comp.output.hex(),'gas':comp.get_gas_remaining(),'trace':trace}
def payload(a,b,n,seed):
 rng=random.Random(seed);data=bytearray(rng.randbytes(n));data[:4]=SELECTOR
 data[4:36]=a.to_bytes(32,'big');data[36:68]=b.to_bytes(32,'big');data[b+4:b+36]=bytes(32)
 return bytes(data)
rows=[]
fixtures=[(64,192,228),(64,256,292),(0,0,132),(73,205,241),(128,64,260),(96,96,260)]
rng=random.Random(20261014)
for i in range(32):
 a=rng.randrange(64,512);b=rng.randrange(512,1024);n=max(a+132,b+36)+rng.randrange(0,256);fixtures.append((a,b,n))
for i,(a,b,n) in enumerate(fixtures):
 data=payload(a,b,n,i);d=dafny(data);p=independent(data)
 assert d==p and d['kind']=='revert' and d['data']==EXPECTED and len(d['trace'])==204 and d['gas']==100000-693,(i,d,p)
 rows.append({'a':a,'b':b,'length':n,'calldataSha256':hashlib.sha256(data).hexdigest(),'agree':True,'dafny':d,'independent':p})
for gas in [692,693,694]:
 data=payload(64,192,228,0);d=dafny(data,gas=gas);p=independent(data,gas=gas)
 assert d==p,(gas,d,p)
 assert (d['data']==EXPECTED)==(gas>=693)
 rows.append({'gasBoundary':gas,'agree':True,'dafny':d,'independent':p})
# Ground witnesses rule out vacuous fixed runtime/domain assumptions.
canonical=SELECTOR+b''.join(w.to_bytes(32,'big') for w in [64,256,0,0,128,160,0,0,0])
frame=EVM.default__.Init(100000,BACKEND,EvmFork.default__.CANCUN,_dafny.Seq([]),_dafny.Seq(CODE))
frame=EvmState.State_EXECUTING(frame.evm._replace(context=frame.evm.context._replace(callData=_dafny.Seq(canonical))))
assert C50Bytecode.default__.ValidEmptyCall(frame.evm.context) and C50Bytecode.default__.Ready(frame)
# The claimed jump facts are evaluated by the compiled, verified Code module.
targets=[15,509,523,2601,14938,16064,16080,16237,16327,16343,16365,17340,17358,17379,17391,17418]
model=Code.default__.Create(_dafny.Seq(CODE))
assert C50Bytecode.default__.Runtime(model), 'Captured full runtime must satisfy the reviewed runtime predicate'
assert all(Code.default__.IsInstructionStart(model,0,target) and CODE[target]==0x5b for target in targets)
mutants=[]
for name,pc in [('wrong-error-selector',2617),('wrong-revert-size',2624)]:
 code=bytearray(CODE);code[pc]^=1;data=payload(64,256,292,9)
 d=dafny(data,bytes(code));p=independent(data,bytes(code));assert d==p and d['data']!=EXPECTED
 mutants.append({'name':name,'pc':pc,'killed':True,'dafny':d,'independent':p})
report={'status':'passed','scope':'Concrete validation only; universal bytecode proof remains separate','runtimeSha256':hashlib.sha256(CODE).hexdigest(),'cases':rows,'mutants':mutants,'verifiedModelJumpBoundaries':targets,'backend':'Fail closed if called','canonicalWitnessSha256':hashlib.sha256(canonical).hexdigest(),'groundRuntimeAndDomainPredicates':'satisfied','scriptSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
out=args.output/'concrete.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print('Passed',len(rows),'public-entry/gas cases and',len(mutants),'byte mutants; all model/py-evm results agree')
