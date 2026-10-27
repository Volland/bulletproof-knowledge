import Knowledge.Memory.Axioms

/-!
# Certified memory

A `Certified` store is a store packaged with a proof that
it is consistent. The only way to add a fact is
`Certified.insert`, which returns either a new certified
store or the violated axiom. A hallucinated fact has no
path into certified memory.
-/

namespace Memory

-- ANCHOR: certified
/-- A store together with a proof of its consistency. -/
structure Certified where
  store : Store
  ok    : Consistent store

namespace Certified

/-- Try to add an event. Success carries a new proof;
    failure names the broken axiom. -/
def insert (m : Certified) (e : Event) :
    Except Violation Certified :=
  let s' := m.store.record e
  if h : Consistent s' then .ok ⟨s', h⟩
  else .error ((diagnose s').getD .uniqueIds)
-- ANCHOR_END: certified

/-- Events of a certified store. -/
def events (m : Certified) : List Event :=
  m.store.events

end Certified

end Memory
