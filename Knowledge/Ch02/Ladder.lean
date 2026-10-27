import Knowledge.Memory

/-!
# Chapter 2: the logic ladder

Propositions of increasing order, each stated as a Lean
`Prop` about the shared agent memory.
-/

namespace Ch02

open Memory Memory.World

/- `α` and `β` stand for any type in the definitions below. -/
variable {α β : Type}

-- ANCHOR: rung0
/-- Two sentences, treated as opaque atoms. -/
abbrev AnnaAtKickoff : Prop := Person.anna ∈ kickoff.who
abbrev MarcoAtKickoff : Prop := Person.marco ∈ kickoff.who

/-- True by its shape alone, whatever `a` and `b` say. -/
theorem and_swap (a b : Prop) : a ∧ b → b ∧ a :=
  fun ⟨ha, hb⟩ => ⟨hb, ha⟩

example : MarcoAtKickoff ∧ AnnaAtKickoff :=
  and_swap _ _ ⟨by decide, by decide⟩
-- ANCHOR_END: rung0

-- ANCHOR: rung1
/-- Relations over individuals, read from the store. -/
abbrev ReportsTo (p m : Person) : Prop :=
  (p, m) ∈ store.reportsTo

abbrev Attended (e : Event) (p : Person) : Prop :=
  p ∈ e.who

/-- The hook sentence: a rule over every person. -/
def TeamAtKickoff : Prop :=
  ∀ p : Person, ReportsTo p .anna → Attended kickoff p

/-- Checked person by person against the store. -/
theorem teamAtKickoff : TeamAtKickoff
-- ANCHOR_END: rung1
    := by
  intro p
  cases p <;> decide

-- ANCHOR: witness
/-- "Did Taras attend anything?" The answer is a
    witness (the review) plus two checked facts. -/
theorem tarasAttended :
    ∃ e ∈ store.events, Attended e .taras :=
  ⟨review, by decide, by decide⟩
-- ANCHOR_END: witness

-- ANCHOR: taras_claim
/--
error: Tactic `decide` proved that the proposition
  Attended kickoff Person.taras
is false
-/
#guard_msgs in
example : Attended kickoff .taras := by decide
-- ANCHOR_END: taras_claim

-- ANCHOR: rung2
/-- Properties of relations: predicates whose
    argument is itself a relation. -/
def Symmetric (R : α → α → Prop) : Prop :=
  ∀ a b, R a b → R b a

def Transitive (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R b c → R a c

def Functional (R : α → β → Prop) : Prop :=
  ∀ a b c, R a b → R a c → b = c
-- ANCHOR_END: rung2

-- ANCHOR: rung2_use
theorem overlaps_symmetric :
    Symmetric Interval.Overlaps :=
  fun _ _ h => Interval.overlaps_symm h

/-- Checked over all 125 triples of people. -/
theorem reportsTo_functional : Functional ReportsTo
-- ANCHOR_END: rung2_use
    := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

-- ANCHOR: chain
/-- The chain of a relation: one step, or one step
    followed by a chain. Defined once, for every `R`. -/
inductive Chain (R : α → α → Prop) : α → α → Prop where
  | step : ∀ a b, R a b → Chain R a b
  | link : ∀ a b c, R a b → Chain R b c → Chain R a c

/-- A rule about rules: every chain is transitive. -/
theorem chain_transitive (R : α → α → Prop) :
    Transitive (Chain R)
-- ANCHOR_END: chain
    := by
  intro x y z h₁ h₂
  induction h₁ with
  | step a b h => exact .link a b z h h₂
  | link a b c h _ ih =>
    exact .link a b z h (ih h₂)

end Ch02
