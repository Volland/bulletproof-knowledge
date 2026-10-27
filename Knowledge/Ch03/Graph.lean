import Knowledge.Memory

/-!
# Chapter 3: triples and labelled property graphs

Two flat views of the same memory. Both are honest
encodings of the running example, and both show where
flat graphs stop: an event must be turned into a node,
and a statement cannot be the subject of another
statement.
-/

namespace Ch03

open Memory

-- ANCHOR: node
/-- Everything a triple may mention. -/
inductive Node where
  | person (p : Person)
  | city   (c : City)
  | org    (o : Org)
  | kind   (k : EventKind)
  | time   (t : Time)
  | event  (id : Nat)   -- an invented node for an event
  deriving DecidableEq, Repr

/-- Predicates: a closed vocabulary of edge labels. -/
inductive Pred where
  | worksAt | reportsTo | isA | heldIn
  | starts | stops | attended
  deriving DecidableEq, Repr

/-- Subject, predicate, object. -/
structure Triple where
  s : Node
  p : Pred
  o : Node
  deriving DecidableEq, Repr
-- ANCHOR_END: node

-- ANCHOR: event_triples
/-- One event becomes one invented node and
    a handful of binary edges around it. -/
def Event.triples (e : Event) : List Triple :=
  let ev := Node.event e.id
  [ ⟨ev, .isA,    .kind e.kind⟩,
    ⟨ev, .heldIn, .city e.place⟩,
    ⟨ev, .starts, .time e.span.start⟩,
    ⟨ev, .stops,  .time e.span.stop⟩ ] ++
  e.who.map fun p => ⟨.person p, .attended, ev⟩
-- ANCHOR_END: event_triples

-- ANCHOR: store_triples
/-- The whole store as a set of triples. -/
def Store.triples (s : Store) : List Triple :=
  s.worksAt.map (fun (p, o) =>
      ⟨.person p, .worksAt, .org o⟩) ++
  s.reportsTo.map (fun (p, m) =>
      ⟨.person p, .reportsTo, .person m⟩) ++
  s.events.flatMap Event.triples
-- ANCHOR_END: store_triples

-- ANCHOR: count
/-- info: 6 -/
#guard_msgs in
#eval (Event.triples World.kickoff).length

/-- info: 18 -/
#guard_msgs in
#eval (Store.triples World.store).length
-- ANCHOR_END: count

-- ANCHOR: query
/-- Who attended event `id`? A join over triples. -/
def attendees (ts : List Triple) (id : Nat) :
    List Person :=
  ts.filterMap fun t =>
    match t with
    | ⟨.person p, .attended, .event i⟩ =>
        if i = id then some p else none
    | _ => none

/-- info: [Memory.Person.anna, Memory.Person.marco] -/
#guard_msgs in
#eval attendees (Store.triples World.store) 1
-- ANCHOR_END: query

-- ANCHOR: no_meta
/-- A statement we would like to talk about. -/
def annaAtAcme : Triple :=
  ⟨.person .anna, .worksAt, .org .acme⟩

/--
error: Application type mismatch: The argument
  annaAtAcme
has type
  Triple
but is expected to have type
  Node
in the application
  Triple.mk annaAtAcme
-/
#guard_msgs in
example : Triple :=
  ⟨annaAtAcme, .attended, .event 1⟩
-- ANCHOR_END: no_meta

/-! ## A labelled property graph -/

-- ANCHOR: lpg
/-- Property values: strings or numbers. -/
inductive Val where
  | str (s : String)
  | nat (n : Nat)
  deriving DecidableEq, Repr

abbrev Props := List (String × Val)

/-- A node has an id, a label and properties. -/
structure LNode where
  id    : Nat
  label : String
  props : Props
  deriving Repr

/-- An edge joins two node ids and has
    its own label and properties. -/
structure LEdge where
  src   : Nat
  dst   : Nat
  label : String
  props : Props
  deriving Repr

structure Lpg where
  nodes : List LNode
  edges : List LEdge
  deriving Repr
-- ANCHOR_END: lpg

-- ANCHOR: lpg_kickoff
/-- The kickoff as a property graph: the event
    is still a node, but time lives in properties
    and each attendance edge can carry a role. -/
def kickoffLpg : Lpg :=
  { nodes := [
      ⟨1, "Meeting", [("start", .nat 2880600),
                      ("stop",  .nat 2880660)]⟩,
      ⟨10, "Person", [("name", .str "Anna")]⟩,
      ⟨11, "Person", [("name", .str "Marco")]⟩,
      ⟨20, "City",   [("name", .str "Lisbon")]⟩ ]
    edges := [
      ⟨10, 1, "ATTENDED", [("role", .str "chair")]⟩,
      ⟨11, 1, "ATTENDED", [("role", .str "guest")]⟩,
      ⟨1, 20, "HELD_IN", []⟩ ] }
-- ANCHOR_END: lpg_kickoff

-- ANCHOR: lpg_check
/-- The numbers above are the kickoff's real span. -/
example : World.kickoff.span.start = 2880600 := rfl
example : World.kickoff.span.stop  = 2880660 := rfl
-- ANCHOR_END: lpg_check

-- ANCHOR: lpg_typo
/-- Nothing stops a misspelled label or an edge
    to a node that does not exist. -/
def broken : Lpg :=
  { kickoffLpg with
    edges := ⟨10, 99, "ATENDED", []⟩ ::
             kickoffLpg.edges }

/-- info: 4 -/
#guard_msgs in
#eval broken.edges.length
-- ANCHOR_END: lpg_typo

end Ch03
