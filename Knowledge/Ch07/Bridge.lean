import Knowledge.Memory

/-!
# Chapter 7: from Pydantic to dependent types

Lean counterparts of three Pydantic features: a field
constraint (`Field(gt=0)`) as a subtype, a validator that
can never be skipped, and a run-time smart constructor in
place of `ValidationError`.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: posId
/-- Pydantic's `Field(gt=0)` as a subtype: the number
    travels with the evidence that it is positive. -/
abbrev EventId := { n : Nat // 0 < n }

def kickoffId : EventId := ⟨1, by decide⟩
-- ANCHOR_END: posId

/--
error: Type mismatch
  __src✝.valid
has type
  __src✝.start ≤ __src✝.stop
but is expected to have type
  __src✝.start ≤ 0
-/
#guard_msgs in
-- ANCHOR: mutate
def stretched : Interval :=
  { kickoff.span with stop := 0 }
-- ANCHOR_END: mutate

-- ANCHOR: smartInterval
/-- A run-time smart constructor: `none` plays the
    part of Pydantic's `ValidationError`. -/
def interval? (a b : Time) : Option Interval :=
  if h : a ≤ b then some ⟨a, b, h⟩ else none

/-- info: true -/
#guard_msgs in
#eval (interval? 600 660).isSome

/-- info: false -/
#guard_msgs in
#eval (interval? 660 600).isSome
-- ANCHOR_END: smartInterval

end Ch07
