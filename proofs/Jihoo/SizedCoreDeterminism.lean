import Jihoo.SizedCoreExecution

namespace Jihoo.SizedCoreExecution
open ScopedLend SizedBufferContext

theorem Scalar.deterministic (a : Scalar g env root v) (b : Scalar g env root w) : v = w := by
  cases a with
  | literal h =>
      cases b with
      | literal h' => have eq := h.symm.trans h'; cases eq; rfl
      | var h' _ => have := h.symm.trans h'; contradiction
  | var h lookup =>
      cases b with
      | literal h' => have := h.symm.trans h'; contradiction
      | var h' lookup' =>
          have eq := h.symm.trans h'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq; rfl

theorem ReadLend.head (a : ReadLend g root owner refTy index proof ownerTy body) :
    ∃ reader cont, Graph.nodeAt g root = .lend owner reader cont := by
  cases a with | intro head _ _ _ _ _ _ => exact ⟨_, _, head⟩

theorem ReadLend.unique
    (a : ReadLend g root owner refTy index proof ownerTy body)
    (b : ReadLend g root owner' refTy' index' proof' ownerTy' body') :
    owner = owner' ∧ refTy = refTy' ∧ index = index' ∧ proof = proof' ∧ ownerTy = ownerTy' ∧ body = body' := by
  cases a with
  | intro ha hr hi ho hc hs hb =>
      cases b with
      | intro ha' hr' hi' ho' hc' hs' hb' =>
          have eq := ha.symm.trans ha'; cases eq
          have eq := hr.symm.trans hr'; cases eq
          have eq := hi.symm.trans hi'; cases eq
          have eq := hc.symm.trans hc'; cases eq
          have eq := hb.symm.trans hb'; cases eq
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem OwnedReadLend.head (a : OwnedReadLend g root owner refTy length index proof resultTy ownerTy body) :
    ∃ reader cont, Graph.nodeAt g root = .lend owner reader cont := by
  cases a with | intro h _ _ _ _ _ _ => exact ⟨_, _, h⟩

theorem OwnedReadLend.unique
    (a : OwnedReadLend g root owner refTy length index proof resultTy ownerTy body)
    (b : OwnedReadLend g root owner' refTy' length' index' proof' resultTy' ownerTy' body') :
    owner = owner' ∧ refTy = refTy' ∧ length = length' ∧ index = index' ∧
      proof = proof' ∧ resultTy = resultTy' ∧ ownerTy = ownerTy' ∧ body = body' := by
  cases a with
  | intro ha hr hl hi ho hc hb =>
    cases b with
    | intro ha' hr' hl' hi' ho' hc' hb' =>
      have eq := ha.symm.trans ha'; cases eq
      have eq := hr.symm.trans hr'; cases eq
      have eq := hl.symm.trans hl'; cases eq
      have eq := hi.symm.trans hi'; cases eq
      have eq := hc.symm.trans hc'; cases eq
      have eq := hb.symm.trans hb'; cases eq
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem OwnedReadLend.not_read
    (a : OwnedReadLend g root owner refTy length index proof resultTy ownerTy body)
    (b : ReadLend g root owner' refTy' index' proof' ownerTy' body') : False := by
  cases a with
  | intro ha hr hl hi ho hc hb =>
    cases b with
    | intro ha' hr' hi' ho' hc' hs' hb' =>
      have eq := ha.symm.trans ha'; cases eq
      have eq := hr.symm.trans hr'; cases eq
      have eq := hl.symm.trans hi'; contradiction

theorem Eval.deterministic (a : Eval g env root s v es t)
    (b : Eval g env root s v' es' t') : v = v' ∧ es = es' ∧ t = t' := by
  induction a generalizing v' es' t' with
  | scalar shape =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | natural shape =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | var shape lookup =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          exact ⟨rfl, rfl, rfl⟩
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | app shape function first second ihf ihs =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := function.symm.trans function'; cases eq
          obtain ⟨rfl, rfl, rfl⟩ := ihf first'
          obtain ⟨rfl, rfl, rfl⟩ := ihs second'
          exact ⟨rfl, rfl, rfl⟩
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | allocate shape length init =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; cases eq
          obtain rfl := length.deterministic length'
          obtain rfl := init.deterministic init'
          exact ⟨rfl, rfl, rfl⟩
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | free shape varShape lookup suffix ih =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; cases eq
          have eq := varShape.symm.trans varShape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | yes shape left right bound suffix ih =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; cases eq
          obtain rfl := left.deterministic left'
          obtain rfl := right.deterministic right'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; cases eq
          obtain rfl := left.deterministic left'
          obtain rfl := right.deterministic right'
          contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | no shape left right bound suffix ih =>
      cases b with
      | scalar shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := shape.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := shape.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := shape.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := shape.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := shape.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; cases eq
          obtain rfl := left.deterministic left'
          obtain rfl := right.deterministic right'
          contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := shape.symm.trans shape'; cases eq
          obtain rfl := left.deterministic left'
          obtain rfl := right.deterministic right'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨_, _, head'⟩ := shape'.head
          have eq := shape.symm.trans head'; contradiction
  | lend shape varShape lookup index suffix ih =>
      obtain ⟨_, _, head⟩ := shape.head
      cases b with
      | scalar shape' =>
          have eq := head.symm.trans shape'; contradiction
      | natural shape' =>
          have eq := head.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := head.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := head.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := head.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | no shape' left' right' bound' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := varShape.symm.trans varShape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          obtain rfl := index.deterministic index'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          exact False.elim (shape'.not_read shape)
  | ownedLend shape varShape lookup index length suffix ih =>
      obtain ⟨_, _, head⟩ := shape.head
      cases b with
      | scalar shape' | natural shape' =>
          have eq := head.symm.trans shape'; contradiction
      | var shape' lookup' =>
          have eq := head.symm.trans shape'; contradiction
      | app shape' function' first' second' =>
          have eq := head.symm.trans shape'; contradiction
      | allocate shape' length' init' =>
          have eq := head.symm.trans shape'; contradiction
      | free shape' varShape' lookup' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | yes shape' left' right' bound' suffix' | no shape' left' right' bound' suffix' =>
          have eq := head.symm.trans shape'; contradiction
      | lend shape' varShape' lookup' index' suffix' =>
          exact False.elim (shape.not_read shape')
      | ownedLend shape' varShape' lookup' index' length' suffix' =>
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := shape.unique shape'
          have eq := varShape.symm.trans varShape'; cases eq
          have eq := lookup.symm.trans lookup'; cases eq
          obtain rfl := index.deterministic index'
          obtain rfl := length.deterministic length'
          obtain ⟨rfl, rfl, rfl⟩ := ih suffix'
          exact ⟨rfl, rfl, rfl⟩

end Jihoo.SizedCoreExecution
