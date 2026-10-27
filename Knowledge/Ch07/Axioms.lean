import Knowledge.Memory

/-!
# Chapter 7: axioms

Two places an axiom can live: inside a structure, as a
proof field (`Interval.valid`), or over the whole store,
as a decidable proposition (`BornBefore`, `NoBilocation`,
...). This file exercises both on the concrete world.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: interval_ok
/-- A one-hour span: `decide` proves `600 ≤ 660`. -/
def tenToEleven : Interval := .mk! 600 660
-- ANCHOR_END: interval_ok

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  660 ≤ 600
is false
-/
#guard_msgs in
-- ANCHOR: interval_bad
def backwards : Interval := .mk! 660 600
-- ANCHOR_END: interval_bad

-- ANCHOR: each_axiom
example : BornBefore store    := by decide
example : NoBilocation store  := by decide
example : SingleManager store := by decide
example : UniqueIds store     := by decide
-- ANCHOR_END: each_axiom

-- ANCHOR: phantom_prop
/-- Chapter 1's naive store, with the phantom in it. -/
def haunted : Store := store.record phantom

/-- A certificate of rejection: a proof that the
    phantom breaks the axioms. -/
theorem haunted_bad : ¬ NoBilocation haunted := by
  decide

/-- info: some (Memory.Violation.noBilocation) -/
#guard_msgs in
#eval diagnose haunted
-- ANCHOR_END: phantom_prop

-- The naive store took the phantom without a word.
/-- info: 3 -/
#guard_msgs in
#eval haunted.events.length

/--
error: Tactic `decide` proved that the proposition
  Consistent haunted
is false
-/
#guard_msgs in
-- ANCHOR: phantom_consistent
example : Consistent haunted := by decide
-- ANCHOR_END: phantom_consistent

-- ANCHOR: others_hold
/-- The phantom breaks exactly one axiom. -/
example : BornBefore haunted    := by decide
example : SingleManager haunted := by decide
example : UniqueIds haunted     := by decide
-- ANCHOR_END: others_hold

end Ch07
