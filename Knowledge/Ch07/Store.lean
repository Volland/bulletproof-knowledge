import Knowledge.Memory

/-!
# Chapter 7: using the certified store

`Memory.Certified.insert` is the gate. Here we push a
legitimate event, the phantom, Sofia's early meeting and
a duplicate identifier through it, and show that a
certified store cannot be built around a bad store by
hand either.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: standup
/-- A real meeting: Lena and Taras in Kyiv, the
    morning after the kickoff. -/
def standup : Event :=
  { id := 4, kind := .meeting
    who := [.lena, .taras], place := .kyiv
    span := .mk! (day 2001 + hour 9)
                 (day 2001 + hour 10) }

/-- info: Except.ok 3 -/
#guard_msgs in
#eval (memory.insert standup).map (·.events.length)
-- ANCHOR_END: standup

-- ANCHOR: phantom
/-- info: Except.error (Memory.Violation.noBilocation) -/
#guard_msgs in
#eval (memory.insert phantom).map (·.events.length)
-- ANCHOR_END: phantom

-- ANCHOR: sofia
/-- An LLM places Sofia at a Porto meeting on day 900.
    The store says she joins the world on day 1000. -/
def sofiaEarly : Event :=
  { id := 5, kind := .meeting
    who := [.sofia, .marco], place := .porto
    span := .mk! (day 900 + hour 14)
                 (day 900 + hour 15) }

/-- info: Except.error (Memory.Violation.bornBefore) -/
#guard_msgs in
#eval (memory.insert sofiaEarly).map (·.events.length)
-- ANCHOR_END: sofia

-- ANCHOR: sofia_late
/-- The same meeting, a thousand days later, is fine. -/
def sofiaLate : Event :=
  { sofiaEarly with
    span := .mk! (day 1900 + hour 14)
                 (day 1900 + hour 15) }

/-- info: Except.ok 3 -/
#guard_msgs in
#eval (memory.insert sofiaLate).map (·.events.length)
-- ANCHOR_END: sofia_late

-- ANCHOR: duplicate
-- Recording the kickoff twice reuses id 1.
/-- info: Except.error (Memory.Violation.uniqueIds) -/
#guard_msgs in
#eval (memory.insert kickoff).map (·.events.length)
-- ANCHOR_END: duplicate

-- ANCHOR: chain
/-- A session: each step needs the previous one's
    certificate. The first failure stops the chain. -/
def session : Except Violation Certified := do
  let m₁ ← memory.insert standup
  let m₂ ← m₁.insert sofiaLate
  m₂.insert sofiaEarly

/-- info: Except.error (Memory.Violation.bornBefore) -/
#guard_msgs in
#eval session.map (·.events.length)
-- ANCHOR_END: chain

-- ANCHOR: unchanged
-- A rejection leaves the old memory as it was.
/-- info: 2 -/
#guard_msgs in
#eval memory.events.length
-- ANCHOR_END: unchanged

/--
error: Tactic `decide` proved that the proposition
  Consistent (store.record phantom)
is false
-/
#guard_msgs in
-- ANCHOR: by_hand
def forged : Certified :=
  ⟨store.record phantom, by decide⟩
-- ANCHOR_END: by_hand

end Ch07
