import Knowledge.Memory

/-!
# Chapter 5: the closed world in Lean

The agent's memory is a closed world. Its entity types are
closed inductives, its relations are finite lists, and its
questions are decidable. Absence from a closed relation is
not silence: it is a proof of `¬`.

For contrast, `OpenKickoff` models what an open-world
reasoner knows: some facts, and no claim that they are all.
-/

namespace Ch05

open Memory Memory.World

-- ANCHOR: ask_lena
/-- info: false -/
#guard_msgs in
#eval decide (Store.attended kickoff .lena)
-- ANCHOR_END: ask_lena

-- ANCHOR: lena_absent
/-- Lena did not attend the kickoff: a theorem. -/
theorem lena_absent :
    ¬ Store.attended kickoff .lena := by
  decide
-- ANCHOR_END: lena_absent

-- ANCHOR: works_at
/-- Employment as a closed relation: a pair holds
    exactly when it is on the store's list. -/
def WorksAt (s : Store) (p : Person) (o : Org) : Prop :=
  (p, o) ∈ s.worksAt

instance (s : Store) (p : Person) (o : Org) :
    Decidable (WorksAt s p o) :=
  inferInstanceAs (Decidable ((p, o) ∈ s.worksAt))

theorem lena_not_at_acme :
    ¬ WorksAt store .lena .acme := by
  decide
-- ANCHOR_END: works_at

-- ANCHOR: una
/-- Unique names: different constructors are
    different individuals. -/
theorem anna_is_not_lena :
    Person.anna ≠ Person.lena := by
  decide
-- ANCHOR_END: una

-- ANCHOR: exhaustive
/--
error: Missing cases:
Person.sofia
-/
#guard_msgs in
def Person.homeCity : Person → City
  | .anna  => .lisbon
  | .marco => .porto
  | .lena  => .berlin
  | .taras => .kyiv
-- ANCHOR_END: exhaustive

-- ANCHOR: all
/-- Every person the agent knows, listed once. -/
def Person.all : List Person :=
  [.anna, .marco, .lena, .taras, .sofia]

/-- The list really is complete: checked case by case. -/
theorem Person.mem_all (p : Person) :
    p ∈ Person.all := by
  cases p <;> decide
-- ANCHOR_END: all

-- ANCHOR: who
/-- Who attended an event, and who did not. -/
def attendees (e : Event) : List Person :=
  Person.all.filter (fun p => decide (p ∈ e.who))

def absentees (e : Event) : List Person :=
  Person.all.filter (fun p => decide (p ∉ e.who))

/-- info: [Memory.Person.anna, Memory.Person.marco] -/
#guard_msgs in
#eval attendees kickoff

/--
info: [Memory.Person.lena, Memory.Person.taras,
  Memory.Person.sofia]
-/
#guard_msgs (whitespace := lax) in
#eval absentees kickoff
-- ANCHOR_END: who

-- ANCHOR: forall
/-- To decide a claim about every person, decide it
    for each of the five on `Person.all`. -/
instance (P : Person → Prop) [DecidablePred P] :
    Decidable (∀ p, P p) :=
  if h : ∀ p ∈ Person.all, P p then
    isTrue fun p => h p (Person.mem_all p)
  else
    isFalse fun h' => h fun p _ => h' p

/-- Everyone at the kickoff works at Acme. -/
theorem kickoff_all_acme :
    ∀ p, Store.attended kickoff p →
      WorksAt store p .acme := by
  decide
-- ANCHOR_END: forall

-- ANCHOR: open_kickoff
/-- The open-world view of the kickoff: two facts are
    known, and nothing says they are the only ones. -/
structure OpenKickoff where
  Attended : Person → Prop
  anna     : Attended .anna
  marco    : Attended .marco
-- ANCHOR_END: open_kickoff

-- ANCHOR: open_fails
/--
error: failed to synthesize
  Decidable (∀ (w : OpenKickoff), ¬w.Attended Person.lena)

Hint: Additional diagnostic information may be
available using the `set_option diagnostics true`
command.
-/
#guard_msgs (whitespace := lax) in
example : ∀ w : OpenKickoff, ¬ w.Attended .lena := by
  decide
-- ANCHOR_END: open_fails

-- ANCHOR: two_worlds
/-- A world that fits the facts, with Lena present. -/
def withLena : OpenKickoff where
  Attended p := p = .anna ∨ p = .marco ∨ p = .lena
  anna  := .inl rfl
  marco := .inr (.inl rfl)

/-- A world that fits the facts, with Lena absent. -/
def withoutLena : OpenKickoff where
  Attended p := p = .anna ∨ p = .marco
  anna  := .inl rfl
  marco := .inr rfl

/-- Both worlds agree with every stated fact and
    disagree about Lena: the facts leave her open. -/
theorem lena_unknown :
    withLena.Attended .lena ∧
      ¬ withoutLena.Attended .lena :=
  ⟨.inr (.inr rfl), by
    show ¬ (_ ∨ _)
    decide⟩
-- ANCHOR_END: two_worlds

-- ANCHOR: completion
/-- Closing the world: the listed facts are all
    the facts (Clark's completion). -/
structure ClosedKickoff extends OpenKickoff where
  only : ∀ p, Attended p → p = .anna ∨ p = .marco

/-- In every closed world, Lena was absent. -/
theorem closed_no_lena (w : ClosedKickoff) :
    ¬ w.Attended .lena := by
  intro h
  cases w.only .lena h <;> contradiction
-- ANCHOR_END: completion

end Ch05
