import Knowledge.Memory.Entities
import Knowledge.Memory.Time

/-!
# Facts

A fact is a typed record. A store holds the static
knowledge the agent was configured with (birth times,
employment, reporting lines) plus recorded events.
-/

namespace Memory

-- ANCHOR: event
/-- An event the agent remembers:
    who was there, where, and when. -/
structure Event where
  id    : Nat
  kind  : EventKind
  who   : List Person
  place : City
  span  : Interval
  deriving DecidableEq, Repr
-- ANCHOR_END: event

-- ANCHOR: store
/-- The agent's memory: background knowledge
    plus recorded events. -/
structure Store where
  /-- Birth time of each person. -/
  born      : Person → Time
  /-- Who works where. Closed: absent means false. -/
  worksAt   : List (Person × Org)
  /-- Who reports to whom. -/
  reportsTo : List (Person × Person)
  /-- Everything the agent has recorded. -/
  events    : List Event
-- ANCHOR_END: store

namespace Store

/-- Did `p` take part in `e`, according to the store? -/
def attended (e : Event) (p : Person) : Prop :=
  p ∈ e.who

instance (e : Event) (p : Person) :
    Decidable (attended e p) :=
  inferInstanceAs (Decidable (p ∈ e.who))

-- ANCHOR: record
/-- Add an event without any checks.
    This is what a naive agent does. -/
def record (s : Store) (e : Event) : Store :=
  { s with events := e :: s.events }
-- ANCHOR_END: record

end Store

end Memory
