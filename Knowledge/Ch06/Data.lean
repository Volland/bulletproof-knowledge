import Knowledge.Memory

/-!
# Chapter 6 — Data: inductive types, structures, matching

New data types for the agent: where a claim came from, what
the LLM proposed, and simple queries over lists and options.
-/

namespace Ch06

open Memory Memory.World

-- ANCHOR: source
/-- Where a proposed fact came from. -/
inductive Source where
  | user       -- the person told the agent
  | llm        -- the language model produced it
  | document   -- it was read from a file
  deriving Repr, DecidableEq
-- ANCHOR_END: source

-- ANCHOR: source-match
/-- Only the user is taken at their word. -/
def Source.trusted : Source → Bool
  | .user     => true
  | .llm      => false
  | .document => false

/-- info: false -/
#guard_msgs in
#eval Source.llm.trusted

/-- info: false -/
#guard_msgs in
#eval Source.user == Source.llm
-- ANCHOR_END: source-match

-- ANCHOR: err-missing
/--
error: Missing cases:
document
-/
#guard_msgs in
def Source.weight : Source → Nat
  | .user => 3
  | .llm  => 1
-- ANCHOR_END: err-missing

-- ANCHOR: whereabouts
/-- Where someone was: in a city, online,
    or the agent does not know. -/
inductive Whereabouts where
  | inCity (c : City)
  | online
  | unknown
  deriving Repr, DecidableEq

def Whereabouts.country? : Whereabouts → Option Country
  | .inCity c => some c.country
  | _         => none

/-- info: some (Memory.Country.portugal) -/
#guard_msgs in
#eval (Whereabouts.inCity .porto).country?
-- ANCHOR_END: whereabouts

-- ANCHOR: claim
/-- A fact proposed to the agent, before any check. -/
structure Claim where
  who    : Person
  place  : City
  time   : Time
  source : Source := .llm
  deriving Repr

/-- The LLM says Anna was in Berlin at the kickoff. -/
def berlinClaim : Claim :=
  { who := .anna, place := .berlin
    time := kickoff.span.start }

/-- info: Ch06.Source.llm -/
#guard_msgs in
#eval berlinClaim.source
-- ANCHOR_END: claim

-- ANCHOR: claim-use
/-- The same claim, now attributed to the user. -/
def fromUser : Claim :=
  { berlinClaim with source := .user }

/-- info: true -/
#guard_msgs in
#eval fromUser.source.trusted
-- ANCHOR_END: claim-use

-- ANCHOR: lists
/-- info: [2, 1] -/
#guard_msgs in
#eval store.events.map (·.id)

/-- info: [1] -/
#guard_msgs in
#eval (store.events.filter
        (·.kind.physical)).map (·.id)
-- ANCHOR_END: lists

-- ANCHOR: recursion
/-- In how many events did `p` take part? -/
def attendance (p : Person) : List Event → Nat
  | []      => 0
  | e :: es =>
    (if e.who.contains p then 1 else 0)
      + attendance p es

/-- info: 2 -/
#guard_msgs in
#eval attendance .anna store.events

/-- info: 0 -/
#guard_msgs in
#eval attendance .sofia store.events
-- ANCHOR_END: recursion

-- ANCHOR: option
/-- The manager of `p`, if the store records one. -/
def managerOf (s : Store) (p : Person) :
    Option Person :=
  match s.reportsTo.find? (·.1 == p) with
  | some (_, boss) => some boss
  | none           => none

/-- info: some (Memory.Person.anna) -/
#guard_msgs in
#eval managerOf store .marco

/-- info: none -/
#guard_msgs in
#eval managerOf store .anna
-- ANCHOR_END: option

-- ANCHOR: option-use
/-- Report the manager, or say that none is recorded. -/
def describeManager (p : Person) : String :=
  match managerOf store p with
  | some boss => s!"reports to {repr boss}"
  | none      => "no manager recorded"

/-- info: "no manager recorded" -/
#guard_msgs in
#eval describeManager .lena
-- ANCHOR_END: option-use

end Ch06
