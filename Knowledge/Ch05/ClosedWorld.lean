import Knowledge.Memory

/-!
# Chapter 5: the closed world in Lean

The agent's memory is a closed world. Its entity types are
closed inductives, its relations are finite lists, and its
questions are decidable. Absence from a closed relation is
not silence: it is a proof of `¬`.

For contrast, `OpenKickoff` models what an open-world
reasoner knows: some facts, and no claim that they are all.

Some proofs here use tactics taught in Chapter 6. The book
shows their statements with `#check` and keeps the proofs in
this file.
-/

namespace Ch05

open Memory Memory.World

-- ANCHOR: lena_absent
/-- Lena did not attend the kickoff: a theorem. -/
theorem lena_absent :
    ¬ Store.attended kickoff .lena := by
  decide
-- ANCHOR_END: lena_absent

/-- Employment as a closed relation: the same definition
    as Chapter 4's `WorksAt`, repeated because chapter
    modules do not import each other. -/
def WorksAt (s : Store) (p : Person) (o : Org) : Prop :=
  (p, o) ∈ s.worksAt

instance (s : Store) (p : Person) (o : Org) :
    Decidable (WorksAt s p o) :=
  inferInstanceAs (Decidable ((p, o) ∈ s.worksAt))

-- ANCHOR: works_at
theorem lena_not_at_acme :
    ¬ WorksAt store .lena .acme := by
  decide
-- ANCHOR_END: works_at

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
-- ANCHOR_END: all

/-- The list really is complete: checked case by case. -/
theorem Person.mem_all (p : Person) :
    p ∈ Person.all := by
  cases p <;> decide

-- ANCHOR: all

/-- info: Ch05.Person.mem_all (p : Person) : p ∈ Person.all -/
#guard_msgs in
#check Person.mem_all
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

/-- To decide a claim about every person, decide it
    for each of the five on `Person.all`. -/
instance (P : Person → Prop) [DecidablePred P] :
    Decidable (∀ p, P p) :=
  if h : ∀ p ∈ Person.all, P p then
    isTrue fun p => h p (Person.mem_all p)
  else
    isFalse fun h' => h fun p _ => h' p

-- ANCHOR: forall
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
abbrev withLena : OpenKickoff where
  Attended p := p = .anna ∨ p = .marco ∨ p = .lena
  anna  := by decide
  marco := by decide

/-- A world that fits the facts, with Lena absent. -/
abbrev withoutLena : OpenKickoff where
  Attended p := p = .anna ∨ p = .marco
  anna  := by decide
  marco := by decide

/-- Both worlds agree with every stated fact and
    disagree about Lena: the facts leave her open. -/
theorem lena_unknown :
    withLena.Attended .lena ∧
      ¬ withoutLena.Attended .lena := by
  decide
-- ANCHOR_END: two_worlds

-- ANCHOR: completion
/-- Closing the world: the listed facts are all
    the facts (Clark's completion). -/
structure ClosedKickoff extends OpenKickoff where
  only : ∀ p, Attended p → p = .anna ∨ p = .marco
-- ANCHOR_END: completion

/-- In every closed world, Lena was absent. -/
theorem closed_no_lena (w : ClosedKickoff) :
    ¬ w.Attended .lena := by
  intro h
  cases w.only .lena h <;> contradiction

-- ANCHOR: completion

/-- info: Ch05.closed_no_lena (w : ClosedKickoff) :
  ¬w.Attended Person.lena -/
#guard_msgs (whitespace := lax) in
#check closed_no_lena
-- ANCHOR_END: completion

end Ch05
