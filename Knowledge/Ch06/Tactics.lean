import Knowledge.Memory

/-!
# Chapter 6 — Tactics and decidability

Proofs built step by step, with the goal view as the guide,
and propositions that Lean can settle by computation.
-/

namespace Ch06

open Memory Memory.World

-- ANCHOR: rfl
/-- The kickoff lasts sixty minutes. -/
theorem kickoff_lasts_an_hour :
    kickoff.span.stop - kickoff.span.start = 60 := by
  rfl
-- ANCHOR_END: rfl

-- ANCHOR: intro-exact
/-- Overlap does not care about argument order. -/
theorem overlaps_swap (i j : Interval) :
    Interval.Overlaps i j → Interval.Overlaps j i := by
  intro h
  exact ⟨h.2, h.1⟩
-- ANCHOR_END: intro-exact

-- ANCHOR: apply
/-- Anything at or before the start of a span is also
    at or before its end. -/
theorem before_stop (i : Interval) (t : Time)
    (h : t ≤ i.start) : t ≤ i.stop := by
  apply Nat.le_trans h
  exact i.valid
-- ANCHOR_END: apply

-- ANCHOR: constructor
theorem kickoff_facts :
    kickoff.place = .lisbon ∧
      kickoff.kind = .meeting := by
  constructor
  · rfl
  · rfl
-- ANCHOR_END: constructor

-- ANCHOR: unsolved
/--
error: unsolved goals
case right
⊢ kickoff.kind = EventKind.meeting
-/
#guard_msgs in
example :
    kickoff.place = .lisbon ∧
      kickoff.kind = .meeting := by
  constructor
  · rfl
-- ANCHOR_END: unsolved

-- ANCHOR: cases-city
/-- The agent knows two Portuguese cities. -/
theorem portuguese_city (c : City)
    (h : c.country = .portugal) :
    c = .lisbon ∨ c = .porto := by
  cases c with
  | lisbon => exact Or.inl rfl
  | porto  => exact Or.inr rfl
  | _      => contradiction
-- ANCHOR_END: cases-city

-- ANCHOR: cases-all
/-- Every known city lies in one of three countries. -/
theorem three_countries (c : City) :
    c.country = .ukraine ∨ c.country = .portugal ∨
      c.country = .germany := by
  cases c <;> decide
-- ANCHOR_END: cases-all

-- ANCHOR: cases-or
/-- A meeting in Lisbon or Porto is in Portugal. -/
theorem in_portugal (c : City)
    (h : c = .lisbon ∨ c = .porto) :
    c.country = .portugal := by
  cases h with
  | inl hl => rw [hl]; rfl
  | inr hp => rw [hp]; rfl
-- ANCHOR_END: cases-or

-- ANCHOR: induction
/-- The identifiers of a list of events. -/
def ids : List Event → List Nat
  | []      => []
  | e :: es => e.id :: ids es

/-- Every event contributes exactly one identifier. -/
theorem ids_length (es : List Event) :
    (ids es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ids, ih]
-- ANCHOR_END: induction

-- ANCHOR: simp
/-- Recording an event adds exactly one event. -/
theorem record_grows (s : Store) (e : Event) :
    (s.record e).events.length
      = s.events.length + 1 := by
  simp [Store.record]
-- ANCHOR_END: simp

-- ANCHOR: omega
/-- Start plus duration lands on the stop time,
    provided the stop is not before the start. -/
theorem add_sub_back (a b : Nat) (h : a ≤ b) :
    a + (b - a) = b := by
  omega

/-- For an `Interval` the proviso is free:
    the `valid` field supplies it. -/
theorem start_plus_length (i : Interval) :
    i.start + (i.stop - i.start) = i.stop :=
  add_sub_back i.start i.stop i.valid
-- ANCHOR_END: omega

-- ANCHOR: omega-bad
/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  d ≥ 0
  c ≥ 0
  c - d ≥ 1
where
 c := ↑a
 d := ↑b
-/
#guard_msgs in
example (a b : Nat) : a + (b - a) = b := by
  omega
-- ANCHOR_END: omega-bad

-- ANCHOR: omega-time
/--
error: omega could not prove the goal:
No usable constraints found. You may need to unfold
definitions so `omega` can see linear arithmetic facts
about `Nat` and `Int`, which may also involve
multiplication, division, and modular remainder by
constants.
-/
#guard_msgs (whitespace := lax) in
example (a b : Time) (h : a ≤ b) :
    a + (b - a) = b := by
  omega

/-- Unfolding the abbreviation first fixes it. -/
example (a b : Time) (h : a ≤ b) :
    a + (b - a) = b := by
  simp only [Time] at *
  omega
-- ANCHOR_END: omega-time

-- ANCHOR: decide
/-- Marco was not on the review call: checked by
    evaluating the membership test. -/
theorem marco_missed_review :
    ¬ Store.attended review .marco := by
  decide
-- ANCHOR_END: decide

-- ANCHOR: decide-false
/--
error: Tactic `decide` proved that the proposition
  Store.attended review Person.marco
is false
-/
#guard_msgs in
example : Store.attended review .marco := by
  decide
-- ANCHOR_END: decide-false

-- ANCHOR: sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem later_problem :
    kickoff.span.start < review.span.stop := by
  sorry
-- ANCHOR_END: sorry

-- ANCHOR: decidable-eval
/-- info: true -/
#guard_msgs in
#eval decide (kickoff.span.start < review.span.stop)

/-- info: false -/
#guard_msgs in
#eval decide (Store.attended review .marco)
-- ANCHOR_END: decidable-eval

-- ANCHOR: held-in
/-- The event took place in city `c`. -/
def HeldIn (e : Event) (c : City) : Prop :=
  e.place = c
-- ANCHOR_END: held-in

-- ANCHOR: held-in-bad
/--
error: failed to synthesize
  Decidable (HeldIn kickoff City.lisbon)

Hint: Additional diagnostic information may be available
using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
example : HeldIn kickoff .lisbon := by
  decide
-- ANCHOR_END: held-in-bad

-- ANCHOR: held-in-inst
instance (e : Event) (c : City) :
    Decidable (HeldIn e c) :=
  inferInstanceAs (Decidable (e.place = c))

theorem kickoff_in_lisbon : HeldIn kickoff .lisbon := by
  decide

/-- info: false -/
#guard_msgs in
#eval decide (HeldIn review .lisbon)
-- ANCHOR_END: held-in-inst

-- ANCHOR: undecidable
/--
error: failed to synthesize
  Decidable (∀ (n : Nat), n + 0 = n)

Hint: Additional diagnostic information may be available
using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in
example : ∀ n : Nat, n + 0 = n := by
  decide
-- ANCHOR_END: undecidable

-- ANCHOR: bounded
/-- Bounded quantifiers over a list are decidable. -/
theorem nobody_unborn_at_kickoff :
    ∀ p ∈ kickoff.who,
      store.born p ≤ kickoff.span.start := by
  decide
-- ANCHOR_END: bounded

-- ANCHOR: dite
/-- Report a scheduling clash, using the decision. -/
def clash (i j : Interval) : String :=
  if Interval.Overlaps i j then "clash" else "free"

/-- info: "clash" -/
#guard_msgs in
#eval clash kickoff.span review.span
-- ANCHOR_END: dite

end Ch06
