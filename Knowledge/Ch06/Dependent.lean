import Knowledge.Memory

/-!
# Chapter 6 — Dependent types

Types that mention values: intervals that carry a proof,
bounded numbers, and subtypes.
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
/-- A 15-minute check-in, 9:00 to 9:15. -/
def checkIn : Interval := ⟨540, 555, by decide⟩
-- ANCHOR_END: interval-build

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

-- ANCHOR: subtype
/-- An event the memory really holds: the event,
    plus a proof that it is in the store. -/
def StoredEvent : Type := { e : Event // e ∈ store.events }

def storedKickoff : StoredEvent := ⟨kickoff, by decide⟩

/-- Where a stored event took place. -/
def StoredEvent.place (s : StoredEvent) : City :=
  s.val.place

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval storedKickoff.place
-- ANCHOR_END: subtype

-- ANCHOR: subtype-bad
/--
error: Tactic `decide` proved that the proposition
  phantom ∈ store.events
is false
-/
#guard_msgs in
def storedPhantom : StoredEvent := ⟨phantom, by decide⟩
-- ANCHOR_END: subtype-bad

end Ch06
