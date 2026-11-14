#!/usr/bin/env python3
"""Actual Core data cases and drop versus the unified exact byte gate.
Regression evidence only: source IO fidelity, iota and native heap semantics
remain distinct from the checked typing and finite Control certificates.
"""
from __future__ import annotations
import argparse,copy,hashlib,json,shlex,tempfile
from pathlib import Path
from core_certificate_process import ROOT,command,success
from core_native_family_correspondence import Program
from core_typing_producer import require
NAT='(data Nat (z Nat) (s (pi child Nat Nat))) '
BIT='(data Bit (zero Bit) (one Bit)) '
PARAM='(data D 1 1 (base (pi0 n U64 (D n))) (step (pi0 n U64 (pi child (D n) (D n))))) '
CASES={
 'recursive-count':(NAT+'(def value U64 (induct Nat (lam v Nat U64) 0 (lam0 child Nat (lam ih U64 (uadd ih 1))) (s (s z))))',True),
 'indexed-runtime':('(data V 1 0 (nil (V 0)) (cons (pi0 n U64 (pi child (V n) (V (uadd n 1)))))) (def value U64 (induct V (lam n U64 (lam v (V n) U64)) 0 (lam0 n U64 (lam0 child (V n) (lam ih U64 (uadd ih 1)))) (cons 0 nil)))',True),
 'indexed-proposition':('(data V 1 0 (nil (V 0)) (cons (pi0 n U64 (pi child (V n) (V (uadd n 1)))))) (def value (Eq 1 1) (induct V (lam n U64 (lam v (V n) (Eq n n))) (refl 0) (lam0 n U64 (lam0 child (V n) (lam0 ih (Eq n n) (refl (uadd n 1))))) (cons 0 nil)))',True),
 'empty-family-elimination':('(data Empty 0 0) (def value (pi x Empty U64) (lam x Empty (induct Empty (lam v Empty U64) x)))',True),
 'balanced-case-owner':(NAT+'(def value (pi b (Buffer 1) U64) (lam b (Buffer 1) (case Nat (lam v Nat U64) (free b 0) (lam child Nat (drop Nat child (free b 1))) (s z))))',True),
 'flat-induct':(BIT+'(def value U64 (induct Bit (lam v Bit U64) 0 1 one))',True),
 'case-drop-child':(NAT+'(def value U64 (case Nat (lam v Nat U64) 0 (lam child Nat (drop Nat child 1)) (s z)))',True),
 'drop-recursive':(NAT+'(def value U64 (drop Nat (s (s z)) 7))',True),
 'drop-owner-function':(NAT+'(def value (pi tree Nat U64) (lam tree Nat (drop Nat tree 7)))',True),
 'family-reference-type':(NAT+'(def value (Type 0) (Ref Nat))',True),
 'ghost-family-borrow-deref':(NAT+'(def value (Eq (drop Nat (deref (borrow (s z))) 0) 0) (refl 0))',True,False),
 'parameter-recursion':(PARAM+'(def value U64 (induct D (lam v (D 3) U64) 0 (lam0 child (D 3) (lam ih U64 (uadd ih 1))) (step 3 (base 3))))',True),
 'dependent-fields':('(data Box (box (pi n U64 (pi b (Buffer n) Box)))) (def value U64 (case Box (lam v Box U64) (lam n U64 (lam b (Buffer n) (free b n))) (box 2 (alloc 2 (int 0)))))',True),
 'proof-motive':(NAT+'(def value (Eq 0 0) (induct Nat (lam v Nat (Eq 0 0)) (refl 0) (lam0 child Nat (lam0 ih (Eq 0 0) (refl 0))) (s z)))',True),
 'flat-case-rejected':(BIT+'(def value U64 (case Bit (lam v Bit U64) 0 1 zero))',False),
 'flat-drop-rejected':(BIT+'(def value U64 (drop Bit zero 7))',False),
 'wrong-family-drop':(NAT+'(data Other (o Other)) (def value U64 (drop Other (s z) 7))',False),
 'case-field-leak':(NAT+'(def value U64 (case Nat (lam v Nat U64) 0 (lam child Nat 1) (s z)))',False),
 'case-field-duplicate':(NAT+'(def value U64 (case Nat (lam v Nat U64) 0 (lam child Nat (drop Nat child (drop Nat child 1))) (s z)))',False),
 'case-missing-branch':(NAT+'(def value U64 (case Nat (lam v Nat U64) 0 (s z)))',False),
 'recursion-not-erased':(NAT+'(def value U64 (induct Nat (lam v Nat U64) 0 (lam child Nat (lam ih U64 ih)) (s z)))',False),
 'recursive-capture':(NAT+'(def value (pi b (Buffer 1) U64) (lam b (Buffer 1) (induct Nat (lam v Nat U64) (free b 0) (lam0 child Nat (lam ih U64 (free b ih))) (s z))))',False),
 'code-borrow-without-lease':(NAT+'(def value (Ref Nat) (borrow (s z)))',False),
}
def run(args):
 out=args.output;out.mkdir(parents=True,exist_ok=True)
 if args.exporter is None:
  args.exporter=out/'core-native-snapshots'
  success(command([*shlex.split(args.compiler),'build','-O2','-I','compiler',
                   'tests/core_native_snapshots.jh','-o',args.exporter]))
 retained={};observations=[];checks=[]
 def check(name,payload,expected,origin):
  (out/(name+'.snapshot')).write_bytes(payload)
  result=command([*shlex.split(args.checker),'64','128'],payload,cwd=args.proofs)
  (out/(name+'.checker.stderr')).write_bytes(result.stderr)
  (out/(name+'.checker.stdout')).write_bytes(result.stdout)
  require((result.returncode==0)==expected,f'{name}: checker differed: {result.stderr!r}')
  if expected:require(result.stdout==b'exact native unified program accepted\n',f'{name}: acknowledgement')
  checks.append({'case':name,'admitted':expected,'origin':origin,'sha256':hashlib.sha256(payload).hexdigest()})
 for name,case in CASES.items():
  source,accepted=case[:2]; gate=case[2] if len(case)>2 else accepted
  (out/(name+'.core')).write_text(source+'\n')
  result=command([args.exporter,'families'],source.encode())
  (out/(name+'.native.stderr')).write_bytes(result.stderr)
  require((result.returncode==0)==accepted,f'{name}: native result changed: {result.stderr!r}')
  observations.append({'case':name,'native':'accept' if accepted else 'reject'})
  if accepted:
   Program.read(result.stdout);retained[name]=result.stdout;check(name,result.stdout,gate,'actual Core exporter' if gate else 'explicit missing conversion boundary')
 def mutate(name,base,edit):
  p=Program.read(retained[base]);edit(p);check(name,p.encode(),False,'synthetic')
 def change_payload(p,tag,fn):
  i=next(i for i,(t,_,_) in enumerate(p.nodes) if t==tag)
  t,payload,refs=p.nodes[i];p.nodes[i]=(t,fn(payload),refs)
 mutate('mutation-drop-family','drop-recursive',lambda p:change_payload(p,32,lambda _: (99,)))
 mutate('mutation-case-count','case-drop-child',lambda p:change_payload(p,43,lambda v:(v[0],v[1]+1)))
 mutate('mutation-elim-family','recursive-count',lambda p:change_payload(p,13,lambda v:(99,v[1])))
 def bad_branch(p):
  i=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==43)
  tag,payload,refs=p.nodes[i];p.nodes[i]=(tag,payload,(refs[0],refs[-1],*refs[2:]))
 mutate('mutation-case-branch','case-drop-child',bad_branch)
 def change_erasure(p):
  i=next(i for i,(tag,payload,_) in enumerate(p.nodes) if tag==45 and payload==(1,))
  tag,_,refs=p.nodes[i];p.nodes[i]=(tag,(0,),refs)
 mutate('mutation-recursive-erasure','recursive-count',change_erasure)
 def change_parameter_count(p):p.families[0].params=0
 mutate('mutation-parameter-count','parameter-recursion',change_parameter_count)
 def scalar_owner(p):
  i=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==32)
  scalar=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==47)
  tag,payload,refs=p.nodes[i];p.nodes[i]=(tag,payload,(scalar,refs[1]))
 mutate('mutation-drop-scalar-owner','drop-recursive',scalar_owner)
 check('mutation-trailing-byte',retained['recursive-count']+b'\n',False,'synthetic')
 (out/'manifest.json').write_text(json.dumps({'claim':__doc__,'core_sha256':hashlib.sha256((ROOT/'compiler/core.jh').read_bytes()).hexdigest(),'cases':observations,'checks':checks},indent=2)+'\n')
 print(f'Native data correspondence: {len(observations)} source fixtures and {len(checks)} exact-byte checks passed')
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--compiler',default='jihoo')
 p.add_argument('--exporter',type=Path);p.add_argument('--proofs',type=Path,default=ROOT/'proofs')
 p.add_argument('--checker',default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeUnifiedProgram.lean')
 p.add_argument('--output',type=Path)
 args=p.parse_args()
 if args.output:run(args)
 else:
  with tempfile.TemporaryDirectory(prefix='native-data-correspondence-') as directory:
   args.output=Path(directory);run(args)
