import Knowledge.Memory

/-!
# Chapter 7: entities and relations

Entities are closed inductive types (in `Memory.Entities`).
Here we show what that buys us (identity, the unique name
assumption, exhaustive matching) and then build relations
on top of the store: closed, list-backed relations that
`decide` can settle, and an inductive relation that it
cannot.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: una
/-- Different constructors are different individuals:
    the unique name assumption holds by construction. -/
example : Person.anna ≠ Person.marco := by decide

/-- info: false -/
#guard_msgs in
#eval Person.anna == Person.marco

/-- info: true -/
#guard_msgs in
#eval City.lisbon == .lisbon
-- ANCHOR_END: una

-- ANCHOR: noConfusion
/-- The same fact, proven without `decide`: Lean derives
    `noConfusion` for every inductive type. -/
example : Person.anna ≠ Person.marco :=
  fun h => Person.noConfusion h
-- ANCHOR_END: noConfusion

-- ANCHOR: exhaustive
/-- error: Missing cases:
Person.lena
Person.taras
Person.sofia -/
#guard_msgs in
def greeting : Person → String
  | .anna  => "Hi Anna"
  | .marco => "Ciao Marco"
-- ANCHOR_END: exhaustive

-- ANCHOR: worksAt
/-- `p` works at `o`, according to the store. -/
def WorksAt (s : Store) (p : Person) (o : Org) : Prop :=
  (p, o) ∈ s.worksAt

instance (s : Store) (p : Person) (o : Org) :
    Decidable (WorksAt s p o) :=
  inferInstanceAs (Decidable ((p, o) ∈ s.worksAt))
-- ANCHOR_END: worksAt

-- ANCHOR: worksAt_facts
/-- A recorded fact is a proof. -/
example : WorksAt store .anna .acme := by decide

/-- An absent fact is a proof of its negation:
    the closed world (Chapter 5). -/
example : ¬ WorksAt store .anna .lumen := by decide

/-- info: false -/
#guard_msgs in
#eval decide (WorksAt store .lena .acme)
-- ANCHOR_END: worksAt_facts

/--
error: Unknown constant `Memory.Person.lisbon`

Note: Inferred this name from the expected resulting type of `.lisbon`:
  Person
---
error: Unknown constant `Memory.Org.anna`

Note: Inferred this name from the expected resulting type of `.anna`:
  Org
-/
#guard_msgs in
-- ANCHOR: wrongDomain
example : Prop := WorksAt store .lisbon .anna
-- ANCHOR_END: wrongDomain

-- ANCHOR: colleagues
/-- Two different people who share an employer. -/
def Colleagues (s : Store) (p q : Person) : Prop :=
  p ≠ q ∧ ∃ r ∈ s.worksAt, r.1 = p ∧ WorksAt s q r.2

instance (s : Store) (p q : Person) :
    Decidable (Colleagues s p q) := by
  unfold Colleagues; infer_instance
-- ANCHOR_END: colleagues

-- ANCHOR: colleagues_facts
example : Colleagues store .anna .marco := by decide
example : ¬ Colleagues store .anna .taras := by decide
example : ¬ Colleagues store .anna .anna := by decide
-- ANCHOR_END: colleagues_facts

-- ANCHOR: under
/-- `Under s p q`: `p` is somewhere under `q` in the
    reporting chain. Defined by rules, not by a list. -/
inductive Under (s : Store) : Person → Person → Prop
  | direct {p q : Person} :
      (p, q) ∈ s.reportsTo → Under s p q
  | step {p q r : Person} :
      (p, q) ∈ s.reportsTo → Under s q r → Under s p r
-- ANCHOR_END: under

-- ANCHOR: under_proof
/-- A proof built from the rules by hand. -/
example : Under store .marco .anna :=
  .direct (by decide)
-- ANCHOR_END: under_proof

/--
error: failed to synthesize
  Decidable (Under store Person.marco Person.anna)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
-- ANCHOR: under_decide
example : Under store .marco .anna := by decide
-- ANCHOR_END: under_decide

end Ch07
