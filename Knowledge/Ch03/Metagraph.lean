import Knowledge.Memory

/-!
# Chapter 3: a metagraph in Lean

Following *Metagraph for AI Agents*: a metavertex may
contain a subgraph, and a metaedge joins a source set to
a target set of elements, where an element may itself be
an edge. Edges are terms, so relations can be the
subjects of other relations.
-/

namespace Ch03

open Memory

-- ANCHOR: atom
/-- Atomic things the agent can mention. -/
inductive Atom where
  | person (p : Person)
  | city   (c : City)
  | org    (o : Org)
  | event  (id : Nat)
  | span   (i : Interval)
  | topic  (name : String)
  deriving DecidableEq, Repr

/-- Edge labels: a closed vocabulary. -/
inductive Rel where
  | presentAt | approved | during | said
  deriving DecidableEq, Repr
-- ANCHOR_END: atom

-- ANCHOR: elem
/-- One type for everything in the metagraph. -/
inductive MElem where
  /-- an atomic vertex -/
  | atom   (a : Atom)
  /-- a metavertex: a named element that
      contains a whole subgraph -/
  | vertex (name : Atom) (inner : List MElem)
  /-- a metaedge from a source set to a
      target set; both may contain edges -/
  | edge   (r : Rel) (src dst : List MElem)
  deriving BEq, Repr
-- ANCHOR_END: elem

/-- A memory is a list of asserted elements. -/
abbrev Metagraph := List MElem

namespace MElem

-- ANCHOR: helpers
def person (p : Person) : MElem := .atom (.person p)
def city (c : City) : MElem := .atom (.city c)
def topic (s : String) : MElem := .atom (.topic s)
-- ANCHOR_END: helpers

end MElem

open MElem

-- ANCHOR: of_event
/-- A recorded event becomes a metavertex whose
    inner subgraph holds who, where and when. -/
def ofEvent (e : Event) : MElem :=
  let people := e.who.map person
  .vertex (.event e.id)
    (people ++
      [ city e.place, .atom (.span e.span),
        .edge .presentAt people [city e.place] ])
-- ANCHOR_END: of_event

-- ANCHOR: claim
/-- Level 1: an edge between atoms. -/
def approval : MElem :=
  .edge .approved [person .anna] [topic "budget"]

/-- Level 2: an edge from an edge
    to a metavertex. -/
def approvalDuring : MElem :=
  .edge .during [approval] [ofEvent World.kickoff]

/-- Level 3: an edge from a person
    to an edge. -/
def marcoSaid : MElem :=
  .edge .said [person .marco] [approvalDuring]
-- ANCHOR_END: claim

-- ANCHOR: memory
/-- What the agent asserts: the events it recorded
    and the claim Marco made. Not the approval. -/
def memory : Metagraph :=
  World.store.events.map ofEvent ++ [marcoSaid]
-- ANCHOR_END: memory

/-! ## Structure: order, folding, unfolding -/

-- ANCHOR: order
/-- How many levels of edges are stacked
    inside an element. Atoms have order 0. -/
def MElem.order : MElem → Nat
  | .atom _ => 0
  | .vertex _ xs => maxOf (xs.map order)
  | .edge _ s d =>
      1 + max (maxOf (s.map order)) (maxOf (d.map order))
where
  maxOf (ns : List Nat) : Nat := ns.foldl max 0

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval [approval, approvalDuring, marcoSaid].map
        MElem.order
-- ANCHOR_END: order

-- ANCHOR: fold
/-- Folding: see a metavertex as a single atom. -/
def MElem.fold : MElem → MElem
  | .vertex n _ => .atom n
  | x           => x

/-- Unfolding: open a metavertex and see
    its inner subgraph. -/
def MElem.unfold : MElem → List MElem
  | .vertex _ xs => xs
  | _            => []

/-- info: 5 -/
#guard_msgs in
#eval (ofEvent World.kickoff).unfold.length
-- ANCHOR_END: fold

/-! ## Queries: what holds, and who says so -/

-- ANCHOR: occurs
/-- Does `x` occur anywhere inside `y`
    (including `y` itself)? -/
def MElem.occursIn (x : MElem) : MElem → Bool
  | .atom a => x == .atom a
  | .vertex n xs =>
      x == .vertex n xs ||
        (xs.map x.occursIn).any id
  | .edge r s d =>
      x == .edge r s d ||
        (s.map x.occursIn).any id ||
        (d.map x.occursIn).any id
-- ANCHOR_END: occurs

-- ANCHOR: holds
/-- An element holds if it is asserted, or sits
    inside the subgraph of an asserted metavertex.
    Being *mentioned* by an edge is not enough. -/
def holds (m : Metagraph) (x : MElem) : Bool :=
  m.any fun y => y == x || y.unfold.contains x

/-- Who said something that mentions `x`? -/
def sources (m : Metagraph) (x : MElem) :
    List Person :=
  m.flatMap fun
    | .edge .said [.atom (.person p)] claim =>
        if claim.any x.occursIn then [p] else []
    | _ => []
-- ANCHOR_END: holds

-- ANCHOR: ask
/-- info: false -/
#guard_msgs in
#eval holds memory approval

/-- info: [Memory.Person.marco] -/
#guard_msgs in
#eval sources memory approval

/-- info: true -/
#guard_msgs in
#eval holds memory
  (.edge .presentAt [person .anna, person .marco]
     [city .lisbon])
-- ANCHOR_END: ask

-- ANCHOR: context
/-- In which recorded events does `x` occur? -/
def contexts (m : Metagraph) (x : MElem) : List Atom :=
  m.flatMap fun
    | y@(.vertex n _) => if x.occursIn y then [n] else []
    | _ => []

/-- info: [Ch03.Atom.event 2, Ch03.Atom.event 1] -/
#guard_msgs in
#eval contexts memory (person .anna)
-- ANCHOR_END: context

-- ANCHOR: flatten
/-- The naive agent: drop the metaedges and keep
    the innermost statement as a plain fact. -/
def flatten : MElem → Metagraph
  | .edge .said _ [c] => flatten c
  | .edge .during [c] _ => flatten c
  | x => [x]

/-- info: true -/
#guard_msgs in
#eval holds (flatten marcoSaid) approval
-- ANCHOR_END: flatten

-- ANCHOR: nonsense
/-- No schema: a city "said" a topic, and Lean
    accepts it as a perfectly good element. -/
def nonsense : MElem :=
  .edge .said [city .lisbon] [topic "budget"]

/-- info: 1 -/
#guard_msgs in
#eval nonsense.order
-- ANCHOR_END: nonsense

end Ch03
