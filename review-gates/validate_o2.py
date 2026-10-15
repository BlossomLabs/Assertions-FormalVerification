"""Concrete cross-checks of both O2 public entries; universal proof is separate."""
import argparse,hashlib,json,random,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser(description=__doc__)
for name in ['capture','interpreter','python-deps','output']:p.add_argument('--'+name,type=Path,required=True)
a=p.parse_args();assert not a.output.exists();a.output.mkdir(parents=True)
sys.path[:0]=[str(a.interpreter.resolve()),str(a.python_deps.resolve())]
import _dafny,EVM,EvmFork,EvmState,Precompiled,Code,O2Bytecode
from eth.vm.forks.cancun import CancunVM
from eth.vm.chain_context import ChainContext
from eth.db.atomic import AtomicDB
from eth.vm.message import Message
from eth.vm.logic.invalid import InvalidOpcode
from eth.exceptions import Halt,Revert
from eth_utils import keccak
CODE=bytes.fromhex((a.capture/'runtime.hex').read_text());MAX=(1<<256)-1
PANIC=bytes.fromhex('4e487b71')+(18).to_bytes(32,'big')
BACKEND=Precompiled.T_Dispatcher(lambda *x:(_ for _ in ()).throw(AssertionError('External backend called')),lambda *x:(_ for _ in ()).throw(AssertionError('External backend called')))
HEADER=CancunVM.create_genesis_header(difficulty=0,gas_limit=30_000_000,timestamp=1)
STATE=CancunVM.build_state(AtomicDB(),HEADER,ChainContext(1));ADDRESS=bytes.fromhex('11'*20)
SCOPE={1,3,4,6,16,17,18,20,21,27,28,52,53,54,80,81,82,86,87,91,95,96,97,99,243,253,*range(128,160)}
def frame(data,code=CODE,gas=100000):
 st=EVM.default__.Init(gas,BACKEND,EvmFork.default__.CANCUN,_dafny.Seq([]),_dafny.Seq(code))
 return EvmState.State_EXECUTING(st.evm._replace(context=st.evm.context._replace(callData=_dafny.Seq(data))))
def dafny(data,code=CODE,gas=100000):
 st=frame(data,code,gas);trace=[]
 for _ in range(1000):
  if not st.is_EXECUTING:break
  pc=st.evm.pc;assert code[pc] in SCOPE,'Unsupported path opcode';trace.append(pc);st=EVM.default__.Execute(st)
 else:raise AssertionError('Step bound reached')
 if st.is_RETURNS:return {'kind':'success','data':bytes(st.data).hex(),'gas':st.gas,'trace':trace}
 assert st.is_ERROR
 return {'kind':'revert' if isinstance(st.error,EvmState.Error_REVERTS) else 'OutOfGas' if isinstance(st.error,EvmState.Error_INSUFFICIENT__GAS) else str(st.error),'data':bytes(st.data).hex(),'gas':st.gas,'trace':trace}
def independent(data,code=CODE,gas=100000):
 msg=Message(gas=gas,to=ADDRESS,sender=ADDRESS,value=0,data=data,code=code,is_static=True)
 ctx=STATE.get_transaction_context_class()(gas_price=0,origin=ADDRESS);comp=STATE.computation_class(STATE,msg,ctx);trace=[];iterator=iter(comp.code)
 with comp:
  for _ in range(1000):
   pc=comp.code.program_counter;op=next(iterator);trace.append(pc)
   try:comp.opcodes.get(op,InvalidOpcode(op))(computation=comp)
   except Halt:break
  else:raise AssertionError('Step bound reached')
 return {'kind':'revert' if comp.is_error and isinstance(comp.error,Revert) else type(comp.error).__name__ if comp.is_error else 'success','data':comp.output.hex(),'gas':comp.get_gas_remaining(),'trace':trace}
def payload(rem,x,y,tail=b''):
 return keccak(text=('mod' if rem else 'div')+'(uint256,uint256)')[:4]+b''.join(v.to_bytes(32,'big') for v in [x,y])+tail
rows=[];witnesses=[];rng=random.Random(20261015)
fixtures=[(0,0),(MAX,0),(0,1),(MAX,1),(MAX,2),(MAX,3),(MAX,97),(MAX,MAX),(MAX-1,MAX),(1<<255,(1<<255)-1),(123,789),(123,456),(123,32),(MAX,1<<255),(MAX,256)]
fixtures += [(rng.getrandbits(256),rng.getrandbits(256)) for _ in range(32)]
for rem in [False,True]:
 for i,(x,y) in enumerate(fixtures):
  data=payload(rem,x,y,rng.randbytes(i%5*17));d=dafny(data);v=independent(data)
  reference=PANIC if y==0 else ((x%y) if rem else (x//y)).to_bytes(32,'big')
  cost=(471 if rem else 428) if y==0 else (526 if rem else 483)
  steps=(127 if rem else 118) if y==0 else (142 if rem else 133)
  assert d==v and bytes.fromhex(d['data'])==reference and len(d['trace'])==steps and d['gas']==100000-cost,(rem,i,d,v)
  assert d['kind']==('revert' if y==0 else 'success')
  st=frame(data);assert O2Bytecode.default__.ValidCall(st.evm.context,rem) and O2Bytecode.default__.Ready(st,rem)
  rows.append({'rem':rem,'a':str(x),'b':str(y),'length':len(data),'calldataSha256':hashlib.sha256(data).hexdigest(),'agree':True,'reference':reference.hex(),'dafny':d,'independent':v})
  if i<2:witnesses.append(hashlib.sha256(data).hexdigest())
 for m in [0,97]:
  cost=(471 if rem else 428) if m==0 else (526 if rem else 483)
  for gas in [cost-1,cost,cost+1]:
   data=payload(rem,MAX,m);d=dafny(data,gas=gas);v=independent(data,gas=gas);assert d==v,(rem,m,gas,d,v)
   assert (d['kind']=='OutOfGas')==(gas<cost)
   rows.append({'rem':rem,'m':str(m),'gasBoundary':gas,'agree':True,'dafny':d,'independent':v})
items=(ROOT/'formal/bytecode/o2/Entry.dfy').read_text() if (ROOT/'formal/bytecode/o2/Entry.dfy').exists() else (ROOT/'proofs/o2-bytecode/Entry.dfy').read_text()
targets=sorted(set(int(x) for x in re.findall(r'Code.IsInstructionStart\(code,\s*0,\s*(\d+)\)',items)))
model=Code.default__.Create(_dafny.Seq(CODE));assert O2Bytecode.default__.Runtime(model)
assert all(Code.default__.IsInstructionStart(model,0,t) and CODE[t]==91 for t in targets)
mutants=[]
for name,pc,rem,m in [('div-to-mod',20038,False,97),('mod-to-div',19829,True,97),('wrong-panic-code',19748,False,0)]:
 code=bytearray(CODE);code[pc]=({4:6,6:4}.get(code[pc],code[pc]^1));data=payload(rem,MAX,m);d=dafny(data,bytes(code));v=independent(data,bytes(code));original=dafny(data)
 assert d==v and d['data']!=original['data'],(name,d,v)
 mutants.append({'name':name,'pc':pc,'killed':True,'dafny':d,'independent':v})
report={'status':'passed','scope':'Concrete cross-checks only','runtimeSha256':hashlib.sha256(CODE).hexdigest(),'cases':rows,'mutants':mutants,'verifiedModelJumpBoundaries':targets,'backend':'Fail closed if called','canonicalWitnesses':witnesses,'groundRuntimeAndDomainPredicates':'satisfied','scriptSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(a.output/'concrete.json').write_text(json.dumps(report,indent=2)+'\n');print('Passed',len(rows),'cases and',len(mutants),'byte mutants; DafnyEVM, py-evm and big integers agree')
