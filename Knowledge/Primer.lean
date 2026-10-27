import Knowledge.Memory

/-!
# Reading Lean in ten minutes

The snippets of the primer in *How to Read This Book*.
Nothing here is new; it only names the pieces of Lean
that every chapter uses.
-/

namespace Primer
open Memory Memory.World

-- ANCHOR: def
/-- A named value. -/
def lunch : Time := day 2000 + hour 13

/-- A function: a city in, a `Bool` out. -/
def inPortugal (c : City) : Bool :=
  c.country == .portugal

/-- info: true -/
#guard_msgs in
#eval inPortugal .lisbon
-- ANCHOR_END: def

-- ANCHOR: types
/-- A closed list of values: these two, no others. -/
inductive Mode where
  | inPerson | remote
  deriving Repr

/-- A record with named fields. -/
structure Visit where
  who  : Person
  city : City
  mode : Mode
  deriving Repr

def annaInLisbon : Visit :=
  { who := .anna, city := .lisbon, mode := .inPerson }
-- ANCHOR_END: types

-- ANCHOR: match
/-- One line per case. -/
def Mode.needsTravel : Mode → Bool
  | .inPerson => true
  | .remote   => false
-- ANCHOR_END: match

-- ANCHOR: prop
/-- A proposition, proven by computation. -/
theorem lisbon_in_pt :
    City.lisbon.country = .portugal := by
  decide
-- ANCHOR_END: prop

-- ANCHOR: prop_bad
/--
error: Tactic `decide` proved that the proposition
  City.berlin.country = Country.portugal
is false
-/
#guard_msgs in
example : City.berlin.country = .portugal := by
  decide
-- ANCHOR_END: prop_bad

-- ANCHOR: rfl
/-- `rfl`: both sides compute to the same value. -/
example : City.lisbon.country = .portugal := rfl
-- ANCHOR_END: rfl

-- ANCHOR: anon
/-- `⟨…⟩` fills the fields in order. -/
def marcoInLisbon : Visit :=
  ⟨.marco, .lisbon, .inPerson⟩

/-- Two claims joined by `∧`: one proof for each. -/
example : City.lisbon.country = .portugal ∧
    City.berlin.country = .germany :=
  ⟨rfl, rfl⟩
-- ANCHOR_END: anon

-- ANCHOR: abbrev
/-- A `def` that Lean looks through when it needs to. -/
abbrev InPortugal (c : City) : Prop :=
  c.country = .portugal

/-- `decide` sees the equation behind the name. -/
example : InPortugal .porto := by decide
-- ANCHOR_END: abbrev

-- ANCHOR: option
/-- Read a city name; `none` if we do not know it. -/
def cityOf? : String → Option City
  | "Lisbon" => some .lisbon
  | "Berlin" => some .berlin
  | _        => none

/-- info: some (Memory.City.lisbon) -/
#guard_msgs in
#eval cityOf? "Lisbon"

/-- info: none -/
#guard_msgs in
#eval cityOf? "Atlantis"
-- ANCHOR_END: option

-- ANCHOR: lambda
/-- `fun m => m.events.length`, written short. -/
def countEvents : Certified → Nat :=
  (·.events.length)

/-- info: 2 -/
#guard_msgs in
#eval countEvents memory
-- ANCHOR_END: lambda

end Primer
