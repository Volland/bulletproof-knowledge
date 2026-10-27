import Knowledge.Memory

/-!
# Chapter 6 — Dependent types

Types that mention values: intervals that carry a proof,
bounded numbers, length-indexed vectors and subtypes.
-/

namespace Ch06

open Memory Memory.World

-- ANCHOR: interval-mk
/--
info: Memory.Interval.mk (start stop : Time)
  (valid : start ≤ stop) : Interval
-/
#guard_msgs (whitespace := lax) in
#check Interval.mk
-- ANCHOR_END: interval-mk

-- ANCHOR: interval-build
/-- A 15-minute stand-up, 9:00 to 9:15. -/
def standup : Interval := ⟨540, 555, by decide⟩

/-- Lunch, built with the helper from `Memory`. -/
def lunch : Interval := Interval.mk! 720 780
-- ANCHOR_END: interval-build

-- ANCHOR: interval-bad
/--
error: Tactic `decide` proved that the proposition
  555 ≤ 540
is false
-/
#guard_msgs in
def backwards : Interval := ⟨555, 540, by decide⟩
-- ANCHOR_END: interval-bad

-- ANCHOR: fin
/-- An hour of the day: a number below 24. -/
abbrev Hour := Fin 24

def nineAm : Hour := ⟨9, by decide⟩

/--
info: Fin.mk {n : Nat} (val : Nat) (isLt : val < n) : Fin n
-/
#guard_msgs in
#check Fin.mk
-- ANCHOR_END: fin

-- ANCHOR: fin-bad
/--
error: Tactic `decide` proved that the proposition
  25 < 24
is false
-/
#guard_msgs in
def lateNight : Hour := ⟨25, by decide⟩
-- ANCHOR_END: fin-bad

-- ANCHOR: fin-wrap
/-- info: 1 -/
#guard_msgs in
#eval (25 : Hour)
-- ANCHOR_END: fin-wrap

-- ANCHOR: vec
/-- A list whose length is part of its type. -/
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

/-- The two most recent event ids, newest first. -/
def lastTwo : Vec Nat 2 := .cons 2 (.cons 1 .nil)

/-- info: Ch06.lastTwo : Vec Nat 2 -/
#guard_msgs in
#check lastTwo
-- ANCHOR_END: vec

-- ANCHOR: vec-head
/-- The first element. There is no `nil` case:
    a `Vec α (n + 1)` is never empty. -/
def Vec.head {α : Type} {n : Nat} :
    Vec α (n + 1) → α
  | .cons x _ => x

/-- info: 2 -/
#guard_msgs in
#eval lastTwo.head
-- ANCHOR_END: vec-head

-- ANCHOR: vec-head-bad
/--
error: Application type mismatch: The argument
  Vec.nil
has type
  Vec Nat 0
but is expected to have type
  Vec ?m.5 (?m.6 + 1)
in the application
  Vec.nil.head
-/
#guard_msgs in
#eval (Vec.nil : Vec Nat 0).head
-- ANCHOR_END: vec-head-bad

-- ANCHOR: replicate
/-- `n` copies of `x`. The result type depends on
    the *value* of the argument `n`. -/
def Vec.replicate {α : Type} :
    (n : Nat) → α → Vec α n
  | 0,     _ => .nil
  | k + 1, x => .cons x (replicate k x)

/--
info: Ch06.Vec.replicate {α : Type} (n : Nat) :
  α → Vec α n
-/
#guard_msgs (whitespace := lax) in
#check Vec.replicate
-- ANCHOR_END: replicate

-- ANCHOR: subtype
/-- Events that are meetings: an event plus a proof
    that its kind is `.meeting`. -/
def Meeting : Type := { e : Event // e.kind = .meeting }

def kickoffMeeting : Meeting := ⟨kickoff, rfl⟩

/-- Only meetings have a room to book. -/
def Meeting.room (m : Meeting) : City := m.val.place

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval kickoffMeeting.room
-- ANCHOR_END: subtype

-- ANCHOR: subtype-bad
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.4 = ?m.4
but is expected to have type
  review.kind = EventKind.meeting
in the application
  ⟨review, ⋯⟩
-/
#guard_msgs in
def reviewMeeting : Meeting := ⟨review, rfl⟩
-- ANCHOR_END: subtype-bad

end Ch06
