import Knowledge.Memory

/-!
# Chapter 8 — Subtypes and coercions

A subclass as a subtype: a `Meeting` is an `Event` plus
a proof that its kind is `.meeting`. A coercion lets a
meeting go wherever an event is expected.
-/

namespace Ch08

open Memory Memory.World

-- ANCHOR: meeting
/-- The class of meetings: events whose kind is
    `.meeting`. A value carries the event *and* a
    proof that it is a meeting. -/
def Meeting := { e : Event // e.kind = .meeting }

/-- The kickoff is a meeting; `rfl` is the proof. -/
def kickoffM : Meeting := ⟨kickoff, rfl⟩
-- ANCHOR_END: meeting

-- ANCHOR: not-a-meeting
/--
error: Tactic `decide` proved that the proposition
  review.kind = EventKind.meeting
is false
-/
#guard_msgs in
example : Meeting := ⟨review, by decide⟩
-- ANCHOR_END: not-a-meeting

-- ANCHOR: placeOf
/-- An ordinary function on events. -/
def placeOf (e : Event) : City := e.place
-- ANCHOR_END: placeOf

-- ANCHOR: no-coe
/--
error: Application type mismatch: The argument
  kickoffM
has type
  Meeting
but is expected to have type
  Event
in the application
  placeOf kickoffM
-/
#guard_msgs in
#eval placeOf kickoffM
-- ANCHOR_END: no-coe

-- ANCHOR: coe
/-- Every meeting is an event: forget the proof. -/
instance : Coe Meeting Event := ⟨Subtype.val⟩

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval placeOf kickoffM

/-- info: kickoffM.val : Event -/
#guard_msgs in
#check (kickoffM : Event)
-- ANCHOR_END: coe

-- ANCHOR: embedding
/-- The coercion loses nothing: two meetings with the
    same underlying event are the same meeting. -/
theorem Meeting.ext {a b : Meeting}
    (h : (a : Event) = b) : a = b :=
  Subtype.ext h
-- ANCHOR_END: embedding

-- ANCHOR: inherit
/-- A fact about the subclass, proven once:
    every meeting requires physical presence. -/
theorem Meeting.physical (m : Meeting) :
    (m : Event).kind.physical = true := by
  show m.val.kind.physical = true
  rw [m.property]
  rfl
-- ANCHOR_END: inherit

-- ANCHOR: smart
/-- Classify an untrusted event. The proof `h` from
    the `if` becomes the membership certificate. -/
def Meeting.ofEvent? (e : Event) : Option Meeting :=
  if h : e.kind = .meeting then some ⟨e, h⟩
  else none

/-- info: (some 1, none) -/
#guard_msgs in
#eval ((Meeting.ofEvent? kickoff).map (·.val.id),
       (Meeting.ofEvent? review).map (·.val.id))
-- ANCHOR_END: smart

-- ANCHOR: chain
/-- A subclass of a subclass: meetings in Lisbon. -/
def LisbonMeeting :=
  { m : Meeting // (m : Event).place = .lisbon }

instance : Coe LisbonMeeting Meeting := ⟨Subtype.val⟩

def kickoffL : LisbonMeeting := ⟨kickoffM, rfl⟩

-- Two coercions chain: LisbonMeeting → Meeting → Event.
/-- info: [Memory.Person.anna, Memory.Person.marco] -/
#guard_msgs in
#eval (kickoffL : Event).who
-- ANCHOR_END: chain

end Ch08
