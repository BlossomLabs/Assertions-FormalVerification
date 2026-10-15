"""Concrete cross-checks of both O13 public entries; universal proof is separate."""
import argparse,hashlib,json,random,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser(description=__doc__)
for name in ['capture','interpreter','python-deps','output']:p.add_argument('--'+name,type=Path,required=True)
a=p.parse_args();assert not a.output.exists();a.output.mkdir(parents=True)
sys.path[:0]=[str(a.interpreter.resolve()),str(a.python_deps.resolve())]
import _dafny,EVM,EvmFork,EvmState,Precompiled,Code,O13Bytecode,O13Core
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
SCOPE={1,3,6,8,9,16,17,18,20,21,27,28,52,53,54,80,81,82,86,87,91,95,96,97,99,243,253,*range(128,160)}
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
def payload(mul,x,y,m,tail=b''):
 return keccak(text=('mulMod' if mul else 'addMod')+'(int256,int256,int256)')[:4]+b''.join((v%(1<<256)).to_bytes(32,'big') for v in [x,y,m])+tail
rows=[];witnesses=[];rng=random.Random(20261015)
LOW=-(1<<255);HIGH=(1<<255)-1
fixtures=[(x,y,m) for x in [LOW,-7,-1,0,1,7,HIGH] for y in [LOW,-7,-1,0,1,7,HIGH] for m in [LOW,-7,-1,0,1,7,HIGH]]
fixtures += [(rng.getrandbits(256)-(1<<255),rng.getrandbits(256)-(1<<255),rng.getrandbits(256)-(1<<255)) for _ in range(32)]
for mul in [False,True]:
 for i,(x,y,m) in enumerate(fixtures):
  data=payload(mul,x,y,m,rng.randbytes(i%5*17));d=dafny(data);v=independent(data)
  mathematical=x*y if mul else x+y
  result=0 if m==0 else (abs(mathematical)%abs(m))*(-1 if mathematical<0 else 1)
  reference=PANIC if m==0 else (result%(1<<256)).to_bytes(32,'big')
  assert d==v and bytes.fromhex(d['data'])==reference,(mul,i,d,v)
  assert d['kind']==('revert' if m==0 else 'success') and 100000-d['gas']<=1100
  st=frame(data);assert O13Core.default__.ValidCall(st.evm.context,mul)
  if i in [0,3]:assert O13Core.default__.Ready(st,mul)
  rows.append({'mul':mul,'a':str(x),'b':str(y),'m':str(m),'length':len(data),'calldataSha256':hashlib.sha256(data).hexdigest(),'agree':True,'reference':reference.hex(),'dafny':d,'independent':v})
  if i in [0,3]:witnesses.append(hashlib.sha256(data).hexdigest())
items=(ROOT/'formal/bytecode/o13/Core.dfy').read_text()
targets=sorted(set(int(x) for x in re.findall(r'Start\(code,\s*(\d+)\)',items)))
model=Code.default__.Create(_dafny.Seq(CODE));assert O13Core.default__.Runtime(model)
assert all(Code.default__.IsInstructionStart(model,0,t) and CODE[t]==91 for t in targets)
mutants=[]
for name,pc,mul,m in [('magnitude-negation-to-addition',8771,False,97),('mulmod-to-addmod',4090,True,97),('restore-negation-to-addition',9103,False,97)]:
 code=bytearray(CODE);code[pc]=(8 if pc==4090 else 1);data=payload(mul,-7,-3,m);d=dafny(data,bytes(code));v=independent(data,bytes(code));original=dafny(data)
 assert d==v and d['data']!=original['data'],(name,d,v)
 mutants.append({'name':name,'pc':pc,'killed':True,'dafny':d,'independent':v})
report={'status':'passed','scope':'Concrete cross-checks only','runtimeSha256':hashlib.sha256(CODE).hexdigest(),'cases':rows,'mutants':mutants,'verifiedModelJumpBoundaries':targets,'backend':'Fail closed if called','canonicalWitnesses':witnesses,'groundRuntimeAndDomainPredicates':'satisfied','scriptSha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(a.output/'concrete.json').write_text(json.dumps(report,indent=2)+'\n');print('Passed',len(rows),'cases and',len(mutants),'byte mutants; DafnyEVM, py-evm and big integers agree')
