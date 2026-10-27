-- ANCHOR: header
import Knowledge.Memory
open Memory Memory.World
namespace Ch06
-- ANCHOR_END: header

/-!
# Chapter 6 — Values, types and functions

The first contact with Lean: evaluating expressions, asking
for types, and defining functions over the agent's memory.
-/

-- ANCHOR: hook
/-- The kickoff ends after it starts.
    The machine checks it; nobody has to trust us. -/
theorem kickoff_ends_after_start :
    kickoff.span.start < kickoff.span.stop := by
  decide
-- ANCHOR_END: hook

-- ANCHOR: eval
/-- info: 5 -/
#guard_msgs in
#eval 2 + 3

/-- info: "Anna is in Lisbon" -/
#guard_msgs in
#eval "Anna" ++ " is in " ++ "Lisbon"
-- ANCHOR_END: eval

-- ANCHOR: check
/-- info: 2 + 3 : Nat -/
#guard_msgs in
#check 2 + 3

/-- info: Memory.Person.anna : Person -/
#guard_msgs in
#check Person.anna

/-- info: Memory.World.kickoff : Event -/
#guard_msgs in
#check kickoff
-- ANCHOR_END: check

-- ANCHOR: eval-kickoff
/--
info: { id := 1,
  kind := Memory.EventKind.meeting,
  who := [Memory.Person.anna, Memory.Person.marco],
  place := Memory.City.lisbon,
  span := { start := 2880600, stop := 2880660, valid := _ } }
-/
#guard_msgs in
#eval kickoff
-- ANCHOR_END: eval-kickoff

-- ANCHOR: def
/-- Minutes in one day. -/
def minutesPerDay : Nat := 24 * 60

/-- How long something lasts, in minutes. -/
def duration (start stop : Nat) : Nat :=
  stop - start

/-- info: 60 -/
#guard_msgs in
#eval duration 600 660
-- ANCHOR_END: def

-- ANCHOR: check-fn
/-- info: Ch06.duration (start stop : Nat) : Nat -/
#guard_msgs in
#check duration

/-- info: duration : Nat → Nat → Nat -/
#guard_msgs in
#check @duration
-- ANCHOR_END: check-fn

-- ANCHOR: truncated
/-- info: 0 -/
#guard_msgs in
#eval duration 660 600
-- ANCHOR_END: truncated

-- ANCHOR: lambda
/-- info: fun h => 60 * h : Nat → Nat -/
#guard_msgs in
#check fun h => 60 * h

/-- info: [60, 120, 180] -/
#guard_msgs in
#eval [1, 2, 3].map (fun h => 60 * h)

/-- info: [0, 60, 120] -/
#guard_msgs in
#eval [600, 660, 720].map (duration 600)
-- ANCHOR_END: lambda

-- ANCHOR: let-if
/-- Classify a span by its length. -/
def describe (i : Interval) : String :=
  let len := i.stop - i.start
  if len < 30 then "short"
  else if len ≤ 90 then "normal"
  else "long"

/-- info: "normal" -/
#guard_msgs in
#eval describe kickoff.span
-- ANCHOR_END: let-if

-- ANCHOR: match
/-- How the agent refers to a person. -/
def name : Person → String
  | .anna  => "Anna"
  | .marco => "Marco"
  | .lena  => "Lena"
  | .taras => "Taras"
  | .sofia => "Sofia"

/-- info: "Marco" -/
#guard_msgs in
#eval name .marco

/-- One line of the agent's summary. -/
def summary (e : Event) : String :=
  let names := e.who.map name
  s!"event {e.id}: {names} for " ++
    s!"{duration e.span.start e.span.stop} min"

/-- info: "event 1: [Anna, Marco] for 60 min" -/
#guard_msgs in
#eval summary kickoff
-- ANCHOR_END: match

-- ANCHOR: err-type
/--
error: Type mismatch
  City.lisbon
has type
  City
but is expected to have type
  Person
-/
#guard_msgs in
def whoIsThere : Person := City.lisbon
-- ANCHOR_END: err-type

-- ANCHOR: err-unknown
/-- error: Unknown constant `Memory.Person.ana` -/
#guard_msgs in
#eval Person.ana

/-- error: Unknown identifier `kickof` -/
#guard_msgs in
#eval kickof
-- ANCHOR_END: err-unknown

end Ch06
