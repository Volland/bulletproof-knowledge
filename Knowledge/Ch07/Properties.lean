import Knowledge.Memory

/-!
# Chapter 7: properties

A property attaches values to an individual. How many
values it may have is part of its type:

* exactly one: a total function (`City.country`);
* at most one: a function into `Option`;
* any number: a function into `List`;
* a promise the data must keep: an axiom (`Functional`).
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

-- ANCHOR: messy
/-- A store where Anna has two employers. -/
def messy : Store :=
  { store with
    worksAt := (.anna, .lumen) :: store.worksAt }

/-- info: some (Memory.Org.lumen) -/
#guard_msgs in
#eval employer messy .anna
-- ANCHOR_END: messy

-- ANCHOR: functional
/-- A list-backed relation is *functional* when each
    key has at most one value. -/
def Functional {α β : Type} (r : List (α × β)) : Prop :=
  ∀ x ∈ r, ∀ y ∈ r, x.1 = y.1 → x.2 = y.2

instance {α β : Type} [DecidableEq α] [DecidableEq β]
    (r : List (α × β)) : Decidable (Functional r) := by
  unfold Functional; infer_instance

example : Functional store.worksAt := by decide
example : ¬ Functional messy.worksAt := by decide

/-- `SingleManager` is this constraint, by definition. -/
theorem singleManager_iff (s : Store) :
    SingleManager s ↔ Functional s.reportsTo :=
  Iff.rfl
-- ANCHOR_END: functional

end Ch07
