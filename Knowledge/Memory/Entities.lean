/-!
# The running example: an assistant agent's memory

The vocabulary of the agent's world: people, places,
organizations and event kinds. Every chapter builds on
these declarations.

Each entity kind is a *closed* inductive type: the agent
knows exactly these individuals, and so does the type
checker (Chapter 5).
-/

namespace Memory

-- ANCHOR: entities
/-- People the agent has met. -/
inductive Person where
  | anna | marco | lena | taras | sofia
  deriving DecidableEq, Repr, Inhabited

/-- Cities the agent knows about. -/
inductive City where
  | kyiv | lviv | lisbon | porto | berlin
  deriving DecidableEq, Repr, Inhabited

/-- Countries: the next level of the place hierarchy. -/
inductive Country where
  | ukraine | portugal | germany
  deriving DecidableEq, Repr, Inhabited

/-- Organizations people belong to. -/
inductive Org where
  | acme | lumen | kyivTech
  deriving DecidableEq, Repr, Inhabited

/-- Kinds of events the agent records. -/
inductive EventKind where
  | meeting | call | talk | trip
  deriving DecidableEq, Repr, Inhabited
-- ANCHOR_END: entities

-- ANCHOR: country
/-- Every city lies in exactly one country:
    a total function, not a relation. -/
def City.country : City → Country
  | .kyiv   => .ukraine
  | .lviv   => .ukraine
  | .lisbon => .portugal
  | .porto  => .portugal
  | .berlin => .germany
-- ANCHOR_END: country

-- ANCHOR: physical
/-- Calls are the only events that do not
    require physical presence. -/
def EventKind.physical : EventKind → Bool
  | .call => false
  | _     => true
-- ANCHOR_END: physical

end Memory
