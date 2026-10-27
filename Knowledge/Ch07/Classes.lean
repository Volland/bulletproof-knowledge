import Knowledge.Memory

/-!
# Chapter 7: classes

A class is a type. A subclass is a subtype: values of
the parent type packed with a proof that they belong.
A smart constructor is the one place where that proof
is looked for; every later use gets it for free.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: meeting
/-- The class of meetings: events of kind `meeting`. -/
abbrev Meeting := { e : Event // e.kind = .meeting }

/-- The kickoff is a meeting; `decide` finds the proof. -/
def kickoffM : Meeting := ⟨kickoff, by decide⟩

-- Subtype instances apply: `abbrev` is transparent.
/-- info: true -/
#guard_msgs in
#eval kickoffM == kickoffM
-- ANCHOR_END: meeting

-- ANCHOR: meeting_bad
/--
error: Tactic `decide` proved that the proposition
  review.kind = EventKind.meeting
is false
-/
#guard_msgs in
def reviewM : Meeting := ⟨review, by decide⟩
-- ANCHOR_END: meeting_bad

-- ANCHOR: smart
/-- Smart constructor: check once, at the boundary. -/
def Meeting.ofEvent? (e : Event) : Option Meeting :=
  if h : e.kind = .meeting then some ⟨e, h⟩ else none

/-- info: true -/
#guard_msgs in
#eval (Meeting.ofEvent? kickoff).isSome

/-- info: false -/
#guard_msgs in
#eval (Meeting.ofEvent? review).isSome
-- ANCHOR_END: smart

-- ANCHOR: inPerson
/-- The class of events that need physical presence. -/
abbrev InPerson := { e : Event // e.kind.physical = true }

/-- Every meeting is in person: a subclass axiom,
    proven once, as a function between classes. -/
def Meeting.toInPerson (m : Meeting) : InPerson :=
  ⟨m.val, by rw [m.property]; rfl⟩
-- ANCHOR_END: inPerson

-- ANCHOR: employee
/-- Employees of a given store: a class whose
    membership depends on the store's data. -/
abbrev Employee (s : Store) :=
  { p : Person // (s.worksAt.lookup p).isSome }

/-- On employees, the optional employer is total. -/
def Employee.org {s : Store} (p : Employee s) : Org :=
  (s.worksAt.lookup p.val).get p.property

def annaE : Employee store := ⟨.anna, by decide⟩

/-- info: Memory.Org.acme -/
#guard_msgs in
#eval annaE.org
-- ANCHOR_END: employee

-- ANCHOR: employee_bad
/--
error: Tactic `decide` proved that the proposition
  (List.lookup Person.sofia store.worksAt).isSome = true
is false
-/
#guard_msgs in
def sofiaE : Employee store := ⟨.sofia, by decide⟩
-- ANCHOR_END: employee_bad

end Ch07
