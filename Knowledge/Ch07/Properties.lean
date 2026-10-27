import Knowledge.Memory

/-!
# Chapter 7: properties

A property attaches values to an individual. How many
values it may have is part of its type:

* exactly one: a total function (`City.country`);
* at most one: a function into `Option`;
* any number: a function into `List`;
* a constraint the type cannot express: a `Prop`.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: exactlyOne
/-- Exactly one value: composing two functional
    properties gives another one. -/
def countryOf (e : Event) : Country :=
  e.place.country

/-- info: Memory.Country.portugal -/
#guard_msgs in
#eval countryOf kickoff
-- ANCHOR_END: exactlyOne

-- ANCHOR: atMostOne
/-- At most one value: the first employer listed. -/
def employer (s : Store) (p : Person) : Option Org :=
  s.worksAt.lookup p

/-- info: some (Memory.Org.acme) -/
#guard_msgs in
#eval employer store .anna

/-- info: none -/
#guard_msgs in
#eval employer store .sofia
-- ANCHOR_END: atMostOne

-- ANCHOR: many
/-- Any number of values: the events a person
    attended, by identifier. -/
def eventsOf (s : Store) (p : Person) : List Nat :=
  (s.events.filter (·.who.contains p)).map (·.id)

/-- info: [2, 1] -/
#guard_msgs in
#eval eventsOf store .anna

/-- info: [] -/
#guard_msgs in
#eval eventsOf store .lena
-- ANCHOR_END: many

-- ANCHOR: functional
/-- A list-backed relation is *functional* when each
    key has at most one value. -/
def Functional {α β : Type} (r : List (α × β)) : Prop :=
  ∀ x ∈ r, ∀ y ∈ r, x.1 = y.1 → x.2 = y.2

instance {α β : Type} [DecidableEq α] [DecidableEq β]
    (r : List (α × β)) : Decidable (Functional r) := by
  unfold Functional; infer_instance

/-- `SingleManager` is this constraint, by definition. -/
theorem singleManager_iff (s : Store) :
    SingleManager s ↔ Functional s.reportsTo :=
  Iff.rfl
-- ANCHOR_END: functional

-- ANCHOR: messy
/-- A store where Anna has two employers. -/
def messy : Store :=
  { store with
    worksAt := (.anna, .lumen) :: store.worksAt }

/-- info: some (Memory.Org.lumen) -/
#guard_msgs in
#eval employer messy .anna

example : Functional store.worksAt := by decide
example : ¬ Functional messy.worksAt := by decide
-- ANCHOR_END: messy

-- ANCHOR: minCard
/-- At least `n` values: a constraint, not a type. -/
def AtLeast (n : Nat) (e : Event) : Prop :=
  n ≤ e.who.length

instance (n : Nat) (e : Event) :
    Decidable (AtLeast n e) :=
  inferInstanceAs (Decidable (n ≤ _))

example : AtLeast 2 kickoff := by decide
example : ¬ AtLeast 3 kickoff := by decide
-- ANCHOR_END: minCard

-- ANCHOR: pair
/-- Exactly two values, in the type: a list that
    carries a proof of its length. -/
abbrev Pair := { l : List Person // l.length = 2 }

def oneOnOne : Pair := ⟨[.anna, .taras], by decide⟩
-- ANCHOR_END: pair

-- ANCHOR: pair_bad
/--
error: Tactic `decide` proved that the proposition
  [Person.anna].length = 2
is false
-/
#guard_msgs in
def lonely : Pair := ⟨[.anna], by decide⟩
-- ANCHOR_END: pair_bad

end Ch07
