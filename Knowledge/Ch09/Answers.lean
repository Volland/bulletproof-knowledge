import Knowledge.Memory

/-!
# Chapter 9: fighting hallucinations

No proof, no entry; no proof, no answer. A hallucinated
fact fails to typecheck, and `#guard_msgs` keeps the
failure on record. An answer carries a certificate: the
event that makes it true.
-/

namespace Ch09

open Memory Memory.World Interval

-- ANCHOR: no_proof
/--
error: Tactic `decide` proved that the proposition
  Consistent (store.record phantom)
is false
-/
#guard_msgs in
example : Consistent (store.record phantom) := by
  decide
-- ANCHOR_END: no_proof

-- ANCHOR: verdict
/-- The violated axiom, or `none` if accepted. -/
def verdict : Except Violation Certified →
    Option Violation
  | .ok _    => none
  | .error v => some v
-- ANCHOR_END: verdict

-- ANCHOR: traps
/-- Sofia at a meeting long before she was born. -/
def early : Event :=
  { id := 4, kind := .meeting
    who := [.sofia], place := .porto
    span := .mk! (day 10) (day 10 + 60) }

/-- A second event with the kickoff's id. -/
def dupe : Event :=
  { kickoff with id := 1, place := .porto
                 span := .mk! (day 3000) (day 3000 + 30) }

/-- A legitimate follow-up call. -/
def followUp : Event :=
  { id := 5, kind := .call
    who := [.anna, .lena], place := .lisbon
    span := .mk! (day 2001) (day 2001 + 30) }
-- ANCHOR_END: traps

-- ANCHOR: regression
theorem rejects_phantom :
    verdict (memory.insert phantom) =
      some .noBilocation := by decide

theorem rejects_early :
    verdict (memory.insert early) =
      some .bornBefore := by decide

theorem rejects_dupe :
    verdict (memory.insert dupe) =
      some .uniqueIds := by decide

theorem accepts_followUp :
    verdict (memory.insert followUp) = none := by
  decide
-- ANCHOR_END: regression

-- ANCHOR: regression_break
/--
error: Tactic `decide` proved that the proposition
  verdict (memory.insert phantom) = none
is false
-/
#guard_msgs in
example : verdict (memory.insert phantom) = none := by
  decide
-- ANCHOR_END: regression_break

-- ANCHOR: question
/-- "Was `p` physically in city `c`?" -/
def WasInCity (s : Store) (p : Person) (c : City) :
    Prop :=
  ∃ e ∈ s.events,
    p ∈ e.who ∧ e.place = c ∧ e.kind.physical = true

instance (s : Store) (p : Person) (c : City) :
    Decidable (WasInCity s p c) := by
  unfold WasInCity; infer_instance
-- ANCHOR_END: question

-- ANCHOR: answer_term
/-- Yes, and here is the event. -/
theorem anna_in_lisbon : WasInCity store .anna .lisbon :=
  ⟨kickoff, by decide, by decide, rfl, rfl⟩
-- ANCHOR_END: answer_term

-- ANCHOR: answer_wrong
/--
error: Tactic `decide` proved that the proposition
  WasInCity store Person.anna City.kyiv
is false
-/
#guard_msgs in
example : WasInCity store .anna .kyiv := by decide

/-- No: a closed-world "no", with a proof. -/
theorem anna_not_in_kyiv :
    ¬ WasInCity store .anna .kyiv := by decide
-- ANCHOR_END: answer_wrong

-- ANCHOR: certified_answer
/-- An answer is an event plus the proofs that it is
    in the store and that it answers the question. -/
structure Answer (s : Store) (q : Event → Prop) where
  event : Event
  mem   : event ∈ s.events
  holds : q event

/-- Search the list, keeping the membership proof. -/
def search (q : Event → Prop) [DecidablePred q] :
    (es : List Event) →
    Option {e // e ∈ es ∧ q e}
  | [] => none
  | e :: es =>
    if h : q e then some ⟨e, by simp, h⟩
    else (search q es).map fun ⟨x, hx, hq⟩ =>
      ⟨x, by simp [hx], hq⟩

def ask (s : Store) (q : Event → Prop)
    [DecidablePred q] : Option (Answer s q) :=
  (search q s.events).map fun ⟨e, hm, hq⟩ =>
    ⟨e, hm, hq⟩
-- ANCHOR_END: certified_answer

-- ANCHOR: ask_eval
/-- The question as a predicate on one event. -/
def inCity (p : Person) (c : City) (e : Event) :
    Prop :=
  p ∈ e.who ∧ e.place = c ∧ e.kind.physical = true

instance (p : Person) (c : City) :
    DecidablePred (inCity p c) := fun _ => by
  unfold inCity; infer_instance

/-- info: some 1 -/
#guard_msgs in
#eval (ask store (inCity .anna .lisbon)).map
  (·.event.id)

/-- info: none -/
#guard_msgs in
#eval (ask store (inCity .anna .kyiv)).map
  (·.event.id)
-- ANCHOR_END: ask_eval

-- ANCHOR: answer_sound
/-- A certified answer is a proof of the question. -/
theorem Answer.sound {s : Store} {p : Person}
    {c : City} (a : Answer s (inCity p c)) :
    WasInCity s p c :=
  ⟨a.event, a.mem, a.holds⟩
-- ANCHOR_END: answer_sound

-- ANCHOR: lasting
/-- In *every* consistent store that contains the
    kickoff, nobody from the kickoff is at a physical
    event in another city at the same time. -/
theorem not_elsewhere {s : Store} (c : Consistent s)
    (hk : kickoff ∈ s.events)
    {e : Event} (he : e ∈ s.events)
    (hp : e.kind.physical = true)
    (hc : e.place ≠ .lisbon)
    (ho : Overlaps kickoff.span e.span)
    {p : Person} (hw : p ∈ kickoff.who) :
    p ∉ e.who :=
  c.noBilocation kickoff hk e he rfl hp
    (Ne.symm hc) ho p hw
-- ANCHOR_END: lasting

end Ch09
