import Knowledge.Memory

/-!
# Chapter 1: a first look

Small, friendly examples on top of the shared `Memory`
library. Nothing here is new machinery; the point is to
see the propose-check-commit loop run once.
-/

namespace Ch01

open Memory Memory.World

-- ANCHOR: naive
/-- info: 3 -/
#guard_msgs in
#eval (store.record phantom).events.length
-- ANCHOR_END: naive

-- ANCHOR: overlap
/-- info: true -/
#guard_msgs in
#eval decide (Interval.Overlaps kickoff.span phantom.span)
-- ANCHOR_END: overlap

-- ANCHOR: diagnose
/-- info: some (Memory.Violation.noBilocation) -/
#guard_msgs in
#eval diagnose (store.record phantom)
-- ANCHOR_END: diagnose

-- ANCHOR: good_interval
/-- Ten to eleven in the morning of day 0. -/
def morning : Interval :=
  { start := 600, stop := 660, valid := by decide }
-- ANCHOR_END: good_interval

-- ANCHOR: bad_interval
/--
error: Tactic `decide` proved that the proposition
  600 ≤ 540
is false
-/
#guard_msgs in
def backwards : Interval :=
  { start := 600, stop := 540, valid := by decide }
-- ANCHOR_END: bad_interval

-- ANCHOR: verdict
/-- What the checker tells the LLM about one proposal. -/
def verdict (m : Certified) (e : Event) : String :=
  match m.insert e with
  | .ok _    => s!"event {e.id}: accepted"
  | .error v => s!"event {e.id}: rejected, {repr v}"
-- ANCHOR_END: verdict

-- ANCHOR: proposals
/-- Lena gives a talk in Berlin the next day. -/
def talk : Event :=
  { id := 3, kind := .talk
    who := [.lena], place := .berlin
    span := .mk! (day 2001 + hour 9)
                 (day 2001 + hour 10) }

/-- Sofia at a meeting 500 days before she exists. -/
def lateIntro : Event :=
  { id := 4, kind := .meeting
    who := [.sofia, .marco], place := .porto
    span := .mk! (day 500) (day 500 + hour 1) }

/-- What an LLM might propose after reading a chat log. -/
def proposals : List Event :=
  [talk, phantom, lateIntro, kickoff]
-- ANCHOR_END: proposals

-- ANCHOR: run
/--
info: event 3: accepted
event 3: rejected, Memory.Violation.noBilocation
event 4: rejected, Memory.Violation.bornBefore
event 1: rejected, Memory.Violation.uniqueIds
-/
#guard_msgs in
#eval IO.println
  ("\n".intercalate (proposals.map (verdict memory)))
-- ANCHOR_END: run

-- ANCHOR: answer
/-- A claimed answer, with its proof. -/
theorem anna_in_lisbon :
    ∃ e ∈ store.events,
      .anna ∈ e.who ∧ e.place = .lisbon :=
  ⟨kickoff, by decide, by decide⟩
-- ANCHOR_END: answer

-- ANCHOR: no_answer
/--
error: Tactic `decide` proved that the proposition
  Person.lena ∈ kickoff.who
is false
-/
#guard_msgs in
example : .lena ∈ kickoff.who := by decide
-- ANCHOR_END: no_answer

/--
info: 'Memory.World.store_consistent' depends on axioms: [propext]
-/
#guard_msgs in
-- ANCHOR: axioms
#print axioms store_consistent
-- ANCHOR_END: axioms

end Ch01
