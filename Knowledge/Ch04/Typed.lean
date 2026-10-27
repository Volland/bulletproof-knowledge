import Knowledge.Memory

/-!
# Chapter 4: Ontologies as types

Classes are types, individuals are terms, properties are
functions or relations, axioms are propositions, and
proofs are evidence. Every claim the chapter makes about
what Lean accepts or rejects is checked below.
-/

namespace Ch04

open Memory Memory.World

-- ANCHOR: untyped
/-- A schema-free graph: every node is a string. -/
abbrev Triple := String × String × String

def graph : List Triple :=
  [("anna",   "worksAt", "acme"),
   ("lisbon", "worksAt", "anna")]  -- accepted!

/-- info: 2 -/
#guard_msgs in
#eval graph.length
-- ANCHOR_END: untyped

-- ANCHOR: individuals
/-- info: Person.anna : Person -/
#guard_msgs in
#check (Person.anna)

/-- info: City.lisbon : City -/
#guard_msgs in
#check (City.lisbon)
-- ANCHOR_END: individuals

-- ANCHOR: disjoint
/-- info: true -/
#guard_msgs in
#eval decide (Person.anna ≠ Person.marco)
-- ANCHOR_END: disjoint

-- ANCHOR: disjoint_error
/--
error: Type mismatch
  City.lisbon
has type
  City
but is expected to have type
  Person
-/
#guard_msgs in
#check Person.anna = City.lisbon
-- ANCHOR_END: disjoint_error

-- ANCHOR: functional
/-- info: Memory.Country.portugal -/
#guard_msgs in
#eval City.lisbon.country
-- ANCHOR_END: functional

-- ANCHOR: fact
/-- Typed triples: one constructor per property,
    each with its domain and range. -/
inductive Fact where
  | worksAt   (p : Person) (o : Org)
  | reportsTo (p : Person) (manager : Person)
  | attended  (p : Person) (eventId : Nat)
  deriving Repr
-- ANCHOR_END: fact

-- ANCHOR: fact_ok
def good : Fact := .worksAt .anna .acme
-- ANCHOR_END: fact_ok

-- ANCHOR: fact_error
/--
error: Application type mismatch: The argument
  City.lisbon
has type
  City
but is expected to have type
  Person
in the application
  Fact.worksAt City.lisbon
-/
#guard_msgs in
def bad : Fact := .worksAt City.lisbon Person.anna
-- ANCHOR_END: fact_error

-- ANCHOR: worksAt
/-- The property `worksAt` as a relation over the
    store: domain `Person`, range `Org`. -/
def WorksAt (s : Store) (p : Person) (o : Org) : Prop :=
  (p, o) ∈ s.worksAt
-- ANCHOR_END: worksAt

instance (s : Store) (p : Person) (o : Org) :
    Decidable (WorksAt s p o) :=
  inferInstanceAs (Decidable ((p, o) ∈ s.worksAt))

-- ANCHOR: signature
/-- info: WorksAt : Store → Person → Org → Prop -/
#guard_msgs in
#check (WorksAt)
-- ANCHOR_END: signature

-- ANCHOR: evidence
/-- Evidence that Anna works at Acme. -/
theorem anna_at_acme : WorksAt store .anna .acme := by
  decide

/-- info: anna_at_acme : WorksAt store Person.anna Org.acme -/
#guard_msgs in
#check (anna_at_acme)
-- ANCHOR_END: evidence

-- ANCHOR: no_evidence
/--
error: Tactic `decide` proved that the proposition
  WorksAt store Person.anna Org.lumen
is false
-/
#guard_msgs in
example : WorksAt store .anna .lumen := by
  decide
-- ANCHOR_END: no_evidence

-- ANCHOR: pat
/-- A proposition (a type) and its proof (a term). -/
theorem lisbon_in_portugal :
    City.lisbon.country = .portugal := rfl
-- ANCHOR_END: pat

-- ANCHOR: pat_error
/--
error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  City.berlin.country = Country.portugal
-/
#guard_msgs in
example : City.berlin.country = .portugal := rfl
-- ANCHOR_END: pat_error

-- ANCHOR: axiom
/-- A schema axiom, proven once for every kind:
    only calls can happen without physical presence. -/
theorem only_calls_virtual (k : EventKind) :
    k.physical = false → k = .call := by
  cases k <;> simp [EventKind.physical]
-- ANCHOR_END: axiom

-- ANCHOR: store_axioms
/-- info: store_consistent : Consistent store -/
#guard_msgs in
#check (store_consistent)
-- ANCHOR_END: store_axioms

-- ANCHOR: subtype
/-- The class of meetings: events of kind `meeting`. -/
def Meeting := { e : Event // e.kind = .meeting }

/-- Membership needs evidence: here, `rfl`. -/
def kickoffMeeting : Meeting := ⟨kickoff, rfl⟩

/-- Every meeting is still an event. -/
def Meeting.toEvent (m : Meeting) : Event := m.val
-- ANCHOR_END: subtype

-- ANCHOR: subtype_error
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.4 = ?m.4
but is expected to have type
  review.kind = EventKind.meeting
in the application
  ⟨review, ⋯⟩
-/
#guard_msgs in
def reviewMeeting : Meeting := ⟨review, rfl⟩
-- ANCHOR_END: subtype_error

-- ANCHOR: subclass_axiom
/-- Inherited knowledge: every meeting is physical. -/
theorem Meeting.physical (m : Meeting) :
    m.toEvent.kind.physical = true := by
  obtain ⟨e, h⟩ := m
  simp [Meeting.toEvent, h, EventKind.physical]
-- ANCHOR_END: subclass_axiom

-- ANCHOR: located
/-- Anything with a place: a preview of Chapter 8. -/
class Located (α : Type) where
  city : α → City

instance : Located Event := ⟨Event.place⟩
instance : Located Meeting := ⟨fun m => m.toEvent.place⟩

/-- One definition serves every located class. -/
def country {α : Type} [Located α] (x : α) : Country :=
  (Located.city x).country

/-- info: Memory.Country.portugal -/
#guard_msgs in
#eval country kickoffMeeting
-- ANCHOR_END: located

end Ch04
