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
def graph : List (String × String × String) :=
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
abbrev WorksAt (s : Store) (p : Person) (o : Org) :
    Prop :=
  (p, o) ∈ s.worksAt
-- ANCHOR_END: worksAt

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
error: Tactic `decide` proved that the proposition
  City.berlin.country = Country.portugal
is false
-/
#guard_msgs in
example : City.berlin.country = .portugal := by
  decide
-- ANCHOR_END: pat_error

-- ANCHOR: axiom
/-- A schema axiom: only calls can happen
    without physical presence. -/
def OnlyCallsVirtual : Prop :=
  ∀ k : EventKind, k.physical = false → k = .call
-- ANCHOR_END: axiom

/-- The proof: try each of the four kinds
    (the tactics are taught in Chapter 6). -/
theorem only_calls_virtual : OnlyCallsVirtual := by
  intro k
  cases k <;> simp [EventKind.physical]

-- ANCHOR: axiom

/-- info: only_calls_virtual : OnlyCallsVirtual -/
#guard_msgs in
#check (only_calls_virtual)
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
error: Tactic `decide` proved that the proposition
  review.kind = EventKind.meeting
is false
-/
#guard_msgs in
def reviewMeeting : Meeting := ⟨review, by decide⟩
-- ANCHOR_END: subtype_error

-- ANCHOR: subclass_axiom
/-- Inherited knowledge: every meeting is physical. -/
def MeetingsArePhysical : Prop :=
  ∀ m : Meeting, m.toEvent.kind.physical = true
-- ANCHOR_END: subclass_axiom

/-- The proof opens the meeting into its event and
    its evidence (tactics: Chapter 6). -/
theorem Meeting.physical : MeetingsArePhysical := by
  intro m
  obtain ⟨e, h⟩ := m
  simp [Meeting.toEvent, h, EventKind.physical]

-- ANCHOR: subclass_axiom

/-- info: Meeting.physical : MeetingsArePhysical -/
#guard_msgs in
#check (Meeting.physical)
-- ANCHOR_END: subclass_axiom

-- ANCHOR: owl_tbox
/-- The TBox. The classes `:Person`, `:City` and
    `:Org` are the shared types, disjoint for free. -/
structure OrgMemory where
  /-- `:worksAt`: domain `:Person`, range `:Org`. -/
  worksAt : List (Person × Org)
  /-- `:headquarters`, functional: at most one. -/
  hq      : Org → Option City
-- ANCHOR_END: owl_tbox

-- ANCHOR: owl_abox
/-- `:acme :headquarters :lisbon`. The rest are
    not recorded. -/
def knownHq : Org → Option City
  | .acme     => some .lisbon
  | .lumen    => none
  | .kyivTech => none

/-- The ABox: `:anna :worksAt :acme`, plus `knownHq`. -/
def orgMemory : OrgMemory :=
  { worksAt := [(.anna, .acme)]
    hq      := knownHq }

/-- info: some (Memory.City.lisbon) -/
#guard_msgs in
#eval orgMemory.hq .acme
-- ANCHOR_END: owl_abox

-- ANCHOR: owl_reject
/--
error: Application type mismatch: The argument
  City.lisbon
has type
  City
but is expected to have type
  Person
in the application
  Prod.mk City.lisbon
-/
#guard_msgs in
def hookAbox : OrgMemory :=
  { worksAt := [(City.lisbon, Person.anna)]
    hq      := knownHq }
-- ANCHOR_END: owl_reject

-- ANCHOR: counterexample
/-- A draft axiom: "every physical event
    is a meeting". -/
def DraftAxiom : Prop :=
  ∀ k : EventKind, k.physical = true → k = .meeting
-- ANCHOR_END: counterexample

/-- Trips are physical but are not meetings. -/
theorem draft_refuted : ¬ DraftAxiom := by
  intro h
  cases h .trip rfl

-- ANCHOR: counterexample

/-- info: draft_refuted : ¬DraftAxiom -/
#guard_msgs in
#check (draft_refuted)

/-- info: true -/
#guard_msgs in
#eval EventKind.trip.physical
-- ANCHOR_END: counterexample

end Ch04
