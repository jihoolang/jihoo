#!/usr/bin/env python3
"""Actual Core borrowed views versus checked unified exact bytes.
This tests source checking and the verified typing/control gate. Authenticated
view iota and native loan/heap semantics remain separate obligations.
"""
from __future__ import annotations
import argparse,hashlib,json,shlex,tempfile
from pathlib import Path
from core_certificate_process import ROOT,command,success
from core_native_family_correspondence import Program
from core_typing_producer import require
NAT='(data Nat (z Nat) (s (pi child Nat Nat))) '
PARAM='(data D 1 1 (base (pi0 n U64 (D n))) (step (pi0 n U64 (pi child (D n) (D n))))) '
COUNT='(view Nat U64 0 (lam child (Ref Nat) 1) r)'
CASES={
 'one-level':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) '+COUNT+'))',True),
 'recursive':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view-rec Nat U64 0 (lam child (Ref Nat) (lam ih U64 (uadd ih 1))) r)))',True),
 'dependent-constant':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat (lam x (Ref Nat) U64) 0 (lam child (Ref Nat) 1) r)))',True),
 'parameter':(PARAM+'(def value (pi r (Ref (D 3)) U64) (lam r (Ref (D 3)) (view-rec D U64 0 (lam child (Ref (D 3)) (lam ih U64 (uadd ih 1))) r)))',True),
 'erased-parameter-context':(PARAM+'(def value (pi0 n U64 (pi r (Ref (D n)) U64)) (lam0 n U64 (lam r (Ref (D n)) (view-rec D U64 0 (lam child (Ref (D n)) (lam ih U64 (uadd ih 1))) r))))',True),
 'dependent-buffer-field':('(data Box (box (pi n U64 (pi b (Buffer n) (pi0 p (Lt 0 n) Box))))) (def value (pi r (Ref Box) I64) (lam r (Ref Box) (view Box I64 (lam n U64 (lam b (Ref (Buffer n)) (lam0 p (Lt 0 n) (index b 0 p)))) r)))',True),
 'recursive-owned-result':(NAT+'(def value (pi r (Ref Nat) (Buffer 2)) (lam r (Ref Nat) (view-rec Nat (Buffer 2) (alloc 2 (int 0)) (lam child (Ref Nat) (lam ih (Buffer 2) (free ih (alloc 2 (int 0))))) r)))',True),
 'dependent-recursive-owned-result':(NAT+'(def value (pi r (Ref Nat) (Buffer 2)) (lam r (Ref Nat) (view-rec Nat (lam x (Ref Nat) (Buffer 2)) (alloc 2 (int 0)) (lam child (Ref Nat) (lam ih (Buffer 2) (free ih (alloc 2 (int 0))))) r)))',True),
 'fixed-array':(NAT+'(def value (pi r (Ref Nat) (Array 0)) (lam r (Ref Nat) (view Nat (lam x (Ref Nat) (Array 0)) (array) (lam child (Ref Nat) (array)) r)))',True),
 'constant-borrow-result':(NAT+'(def value (pi r (Ref Nat) (Ref Nat)) (lam r (Ref Nat) (view Nat (Ref Nat) r (lam child (Ref Nat) child) r)))',True),
 'function-result':(NAT+'(def value (pi r (Ref Nat) (pi k U64 U64)) (lam r (Ref Nat) (view Nat (pi k U64 U64) (lam k U64 k) (lam child (Ref Nat) (lam k U64 k)) r)))',True),
 'balanced-outer-owner':(NAT+'(def value (pi b (Buffer 1) (pi r (Ref Nat) U64)) (lam b (Buffer 1) (lam r (Ref Nat) (view Nat U64 (free b 0) (lam child (Ref Nat) (free b 1)) r))))',True),
 'earlier-boxed-field':('(data A (a A) (nextA (pi child A A))) (data B (b (pi field A B))) (def value (pi r (Ref B) U64) (lam r (Ref B) (view-rec B U64 (lam field (Ref A) 0) r)))',True),
 'checked-global-reference-alias':(NAT+'(def Alias (Type 0) Nat) (def value (pi r (Ref Alias) U64) (lam r (Ref Alias) '+COUNT+'))',True),
 'checked-global-motive-alias':(NAT+'(def M (pi r (Ref Nat) (Type 0)) (lam r (Ref Nat) U64)) (def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat M 0 (lam child (Ref Nat) 1) r)))',True),
 'ghost-constructor-iota-boundary':(NAT+'(def value (Eq (view Nat U64 0 (lam child (Ref Nat) 1) (borrow (s z))) 1) (refl 1))',True,False),
 'dependent-value-iota-boundary':(NAT+'(def value (pi r (Ref Nat) (Buffer '+COUNT+')) (lam r (Ref Nat) (view Nat (lam r (Ref Nat) (Buffer '+COUNT+')) (alloc 0 (int 0)) (lam child (Ref Nat) (alloc 1 (int 0))) r)))',True,False),
 'dependent-layout-rejected':(NAT+'(def value (pi r (Ref Nat) (Array '+COUNT+')) (lam r (Ref Nat) (view Nat (lam r (Ref Nat) (Array '+COUNT+')) (array) (lam child (Ref Nat) (array (int 0))) r)))',False),
 'dependent-borrow-result-rejected':(NAT+'(def value (pi r (Ref Nat) (Ref Nat)) (lam r (Ref Nat) (view Nat (lam x (Ref Nat) (Ref Nat)) r (lam child (Ref Nat) child) r)))',False),
 'extra-indices':('(data V 1 0 (nil (V 0)) (cons (pi0 n U64 (pi child (V n) (V (uadd n 1)))))) (def value (pi r (Ref (V 0)) U64) (lam r (Ref (V 0)) (view V U64 0 (lam0 n U64 (lam child (Ref (V n)) 1)) r)))',False),
 'owner-instead-of-reference':(NAT+'(def value (pi r Nat U64) (lam r Nat '+COUNT+'))',False),
 'field-owner-instead-of-borrow':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat U64 0 (lam child Nat (drop Nat child 1)) r)))',False),
 'wrong-motive-domain':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat (lam x Nat U64) 0 (lam child (Ref Nat) 1) r)))',False),
 'universe-result':(NAT+'(def value (pi r (Ref Nat) (Type 0)) (lam r (Ref Nat) (view Nat (lam x (Ref Nat) (Type 0)) U64 (lam child (Ref Nat) U64) r)))',False),
 'proof-result':(NAT+'(def value (pi r (Ref Nat) (Eq 0 0)) (lam r (Ref Nat) (view Nat (lam x (Ref Nat) (Eq 0 0)) (refl 0) (lam child (Ref Nat) (refl 0)) r)))',False),
 'missing-branch':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat U64 0 r)))',False),
 'erased-recursive-result':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view-rec Nat U64 0 (lam child (Ref Nat) (lam0 ih U64 1)) r)))',False),
 'drop-borrowed-field':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat U64 0 (lam child (Ref Nat) (drop Nat child 1)) r)))',False),
 'deref-borrowed-field-in-code':(NAT+'(def value (pi r (Ref Nat) U64) (lam r (Ref Nat) (view Nat U64 0 (lam child (Ref Nat) (drop Nat (deref child) 1)) r)))',False),
 'recursive-result-leak':(NAT+'(def value (pi r (Ref Nat) (Buffer 2)) (lam r (Ref Nat) (view-rec Nat (Buffer 2) (alloc 2 (int 0)) (lam child (Ref Nat) (lam ih (Buffer 2) (alloc 2 (int 0)))) r)))',False),
 'recursive-result-duplicate':(NAT+'(def value (pi r (Ref Nat) (Buffer 2)) (lam r (Ref Nat) (view-rec Nat (Buffer 2) (alloc 2 (int 0)) (lam child (Ref Nat) (lam ih (Buffer 2) (free ih (free ih (alloc 2 (int 0)))))) r)))',False),
 'recursive-outer-owner':(NAT+'(def value (pi b (Buffer 1) (pi r (Ref Nat) U64)) (lam b (Buffer 1) (lam r (Ref Nat) (view-rec Nat U64 (free b 0) (lam child (Ref Nat) (lam ih U64 (free b ih))) r))))',False),
 'code-borrow-without-lease':(NAT+'(def value U64 (view Nat U64 0 (lam child (Ref Nat) 1) (borrow (s z))))',False),
}
def run(args):
 out=args.output;out.mkdir(parents=True,exist_ok=True)
 if args.exporter is None:
  args.exporter=out/'core-native-snapshots'
  success(command([*shlex.split(args.compiler),'build','-O2','-I','compiler','tests/core_native_snapshots.jh','-o',args.exporter]))
 retained={};observations=[];checks=[]
 def check(name,payload,accepted,origin):
  (out/(name+'.snapshot')).write_bytes(payload)
  result=command([*shlex.split(args.checker),'64','128'],payload,cwd=args.proofs)
  (out/(name+'.checker.stdout')).write_bytes(result.stdout);(out/(name+'.checker.stderr')).write_bytes(result.stderr)
  require((result.returncode==0)==accepted,f'{name}: checker differed: {(result.stdout+result.stderr)!r}')
  if accepted:require(result.stdout==b'exact native unified program accepted\n',f'{name}: missing acknowledgement')
  checks.append({'case':name,'admitted':accepted,'origin':origin,'sha256':hashlib.sha256(payload).hexdigest()})
 for name,case in CASES.items():
  source,native=case[:2];admitted=case[2] if len(case)>2 else native
  (out/(name+'.core')).write_text(source+'\n')
  result=command([args.exporter,'families'],source.encode())
  (out/(name+'.native.stderr')).write_bytes(result.stderr)
  require((result.returncode==0)==native,f'{name}: native result changed: {result.stderr!r}')
  observations.append({'case':name,'native':'accept' if native else 'reject'})
  if native:
   Program.read(result.stdout);retained[name]=result.stdout
   check(name,result.stdout,admitted,'actual Core exporter' if admitted else 'explicit missing authenticated View iota')
 def mutate(name,base,edit):
  p=Program.read(retained[base]);edit(p);check(name,p.encode(),False,'synthetic')
 def payload_change(p,fn):
  i=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==40)
  tag,payload,refs=p.nodes[i];p.nodes[i]=(tag,fn(payload),refs)
 mutate('mutation-unknown-family','one-level',lambda p:payload_change(p,lambda v:(v[0],99,v[2])))
 mutate('mutation-case-count','one-level',lambda p:payload_change(p,lambda v:(v[0],v[1],v[2]+1)))
 mutate('mutation-recursive-flag','one-level',lambda p:payload_change(p,lambda v:(1,v[1],v[2])))
 def fake_boxed(p):
  constructor=p.families[0].constructors[1];_,flags,(_,result)=p.nodes[constructor]
  scalar=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==4)
  p.nodes.append((44,flags,(scalar,result)));p.families[0].constructors[1]=len(p.nodes)-1
 mutate('mutation-boxed-layout','one-level',fake_boxed)
 def parameter_count(p):p.families[0].params=0
 mutate('mutation-parameter-count','parameter',parameter_count)
 def wrong_reference(p):
  i=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==40)
  scalar=next(i for i,(tag,_,_) in enumerate(p.nodes) if tag==47)
  tag,flags,refs=p.nodes[i];p.nodes[i]=(tag,flags,(*refs[:-1],scalar))
 mutate('mutation-scalar-scrutinee','one-level',wrong_reference)
 def erased_motive(p):
  view=next((refs for tag,_,refs in p.nodes if tag==40));i=view[0]
  tag,_,refs=p.nodes[i];require(tag==45,'expected motive lambda');p.nodes[i]=(tag,(1,),refs)
 mutate('mutation-erased-motive','dependent-constant',erased_motive)
 def append(p,tag,payload,refs):
  p.nodes.append((tag,tuple(payload),tuple(refs)));return len(p.nodes)-1
 def owned_hypothesis(p,duplicate):
  ty,root=p.definitions[-1];tag,flags,(domain,view)=p.nodes[root]
  view_tag,view_flags,refs=p.nodes[view];motive,base,branch,scrutinee=refs
  branch_tag,branch_flags,(field_domain,inner)=p.nodes[branch]
  inner_tag,inner_flags,(ih_domain,body)=p.nodes[inner]
  owner,allocation=p.nodes[body][2]
  new_body=append(p,31,(),(owner,body)) if duplicate else allocation
  inner=append(p,inner_tag,inner_flags,(ih_domain,new_body))
  branch=append(p,branch_tag,branch_flags,(field_domain,inner))
  view=append(p,view_tag,view_flags,(motive,base,branch,scrutinee))
  p.definitions[-1]=(ty,append(p,tag,flags,(domain,view)))
 mutate('mutation-typed-owned-ih-leak','recursive-owned-result',lambda p:owned_hypothesis(p,False))
 mutate('mutation-typed-owned-ih-duplicate','recursive-owned-result',lambda p:owned_hypothesis(p,True))
 def code_deref(p):
  ty,root=p.definitions[-1];root_tag,root_flags,(root_domain,view)=p.nodes[root]
  view_tag,view_flags,(motive,branch,scrutinee)=p.nodes[view]
  n_tag,n_flags,(n_domain,b_lambda)=p.nodes[branch]
  b_tag,b_flags,(b_domain,p_lambda)=p.nodes[b_lambda]
  p_tag,p_flags,(p_domain,index)=p.nodes[p_lambda]
  index_tag,index_flags,(borrow,index_value,proof)=p.nodes[index]
  borrow=append(p,39,(),(borrow,));index=append(p,index_tag,index_flags,(borrow,index_value,proof))
  p_lambda=append(p,p_tag,p_flags,(p_domain,index));b_lambda=append(p,b_tag,b_flags,(b_domain,p_lambda))
  branch=append(p,n_tag,n_flags,(n_domain,b_lambda));view=append(p,view_tag,view_flags,(motive,branch,scrutinee))
  p.definitions[-1]=(ty,append(p,root_tag,root_flags,(root_domain,view)))
 mutate('mutation-code-deref-of-borrow','dependent-buffer-field',code_deref)
 check('mutation-trailing-byte',retained['one-level']+b'\n',False,'synthetic')
 (out/'manifest.json').write_text(json.dumps({'claim':__doc__,'core_sha256':hashlib.sha256((ROOT/'compiler/core.jh').read_bytes()).hexdigest(),'cases':observations,'checks':checks},indent=2)+'\n')
 print(f'Native view correspondence: {len(observations)} source fixtures and {len(checks)} exact-byte checks passed')
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--compiler',default='jihoo');p.add_argument('--exporter',type=Path)
 p.add_argument('--checker',default='lake env lean -M 4096 -j 1 -DwarningAsError=true --run CheckNativeUnifiedProgram.lean')
 p.add_argument('--proofs',type=Path,default=ROOT/'proofs');p.add_argument('--output',type=Path);args=p.parse_args()
 if args.output:run(args)
 else:
  with tempfile.TemporaryDirectory(prefix='native-view-correspondence-') as directory:args.output=Path(directory);run(args)
