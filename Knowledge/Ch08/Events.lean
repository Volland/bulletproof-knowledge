import Knowledge.Memory

/-!
# Chapter 8 — An event taxonomy

Meetings, calls, talks and trips are four classes of
event. Shared axioms live in a parent type class;
each class adds its own axiom, and each instance must
prove that its own axiom implies the shared ones.
-/

namespace Ch08.Taxonomy

open Memory Memory.World

-- ANCHOR: event-class
/-- The shared axioms of every event class. -/
class EventClass (α : Type) where
  toEvent  : α → Event
  kind     : EventKind
  kind_eq  : ∀ a, (toEvent a).kind = kind
  nonempty : ∀ a, (toEvent a).who ≠ []

/-- In-person classes add one more law. -/
class Physical (α : Type) extends EventClass α where
  physical : kind.physical = true
-- ANCHOR_END: event-class

-- ANCHOR: meeting
/-- A meeting: at least two people, in person. The
    `R` marks a record with laws, to keep it apart from
    the `MeetingEv` subtype in `Subtypes.lean`. -/
structure MeetingR where
  ev     : Event
  isKind : ev.kind = .meeting
  quorum : 2 ≤ ev.who.length

instance : Physical MeetingR where
  toEvent m  := m.ev
  kind       := .meeting
  kind_eq m  := m.isKind
  nonempty m := List.ne_nil_of_length_pos
                  (Nat.lt_of_lt_of_le (by decide) m.quorum)
  physical   := rfl
-- ANCHOR_END: meeting

-- ANCHOR: others
/-- A call: at least two people, anywhere. -/
structure CallR where
  ev     : Event
  isKind : ev.kind = .call
  quorum : 2 ≤ ev.who.length

/-- A talk: a speaker, who is present (Chapter 7). -/
structure TalkR where
  ev      : Event
  isKind  : ev.kind = .talk
  speaker : Person
  speaks  : speaker ∈ ev.who

/-- A trip: one traveller per record. -/
structure TripR where
  ev     : Event
  isKind : ev.kind = .trip
  solo   : ev.who.length = 1

instance : EventClass CallR where
  toEvent c  := c.ev
  kind       := .call
  kind_eq c  := c.isKind
  nonempty c := List.ne_nil_of_length_pos
                  (Nat.lt_of_lt_of_le (by decide) c.quorum)

instance : Physical TalkR where
  toEvent t  := t.ev
  kind       := .talk
  kind_eq t  := t.isKind
  nonempty t := List.ne_nil_of_mem t.speaks
  physical   := rfl

instance : Physical TripR where
  toEvent t  := t.ev
  kind       := .trip
  kind_eq t  := t.isKind
  nonempty t := List.ne_nil_of_length_pos (by
                  rw [t.solo]; decide)
  physical   := rfl
-- ANCHOR_END: others

-- ANCHOR: call-physical
/--
error: Tactic `decide` proved that the proposition
  (EventClass.kind CallR).physical = true
is false
-/
#guard_msgs in
example : Physical CallR :=
  { physical := by decide }
-- ANCHOR_END: call-physical

-- ANCHOR: shared-theorem
open EventClass in
/-- Proven once, for every class: somebody was there. -/
theorem EventClass.someone {α : Type} [EventClass α]
    (a : α) : ∃ p, p ∈ (toEvent a).who := by
  cases h : (toEvent a).who with
  | nil => exact absurd h (nonempty a)
  | cons p _ => exact ⟨p, List.mem_cons_self⟩
-- ANCHOR_END: shared-theorem

-- ANCHOR: present
open EventClass in
/-- Members of an in-person class need presence. -/
theorem Physical.present {α : Type} [Physical α]
    (a : α) : (toEvent a).kind.physical = true := by
  rw [kind_eq a]
  exact Physical.physical
-- ANCHOR_END: present

-- ANCHOR: one-city
open EventClass in
/-- For *any* two in-person classes (a talk and a
    trip, say): in a store without bilocation, one
    person at two overlapping events was in one city. -/
theorem Physical.oneCity {α β : Type}
    [Physical α] [Physical β]
    (s : Store) (hs : NoBilocation s)
    (a : α) (b : β)
    (ha : toEvent a ∈ s.events)
    (hb : toEvent b ∈ s.events)
    (ho : Interval.Overlaps (toEvent a).span
                            (toEvent b).span)
    (p : Person)
    (pa : p ∈ (toEvent a).who)
    (pb : p ∈ (toEvent b).who) :
    (toEvent a).place = (toEvent b).place := by
  by_cases hne : (toEvent a).place = (toEvent b).place
  · exact hne
  · exact absurd pb
      (hs _ ha _ hb (Physical.present a)
        (Physical.present b) hne ho p pa)
-- ANCHOR_END: one-city

-- ANCHOR: smart
/-- Classify an untrusted event as a meeting. -/
def MeetingR.ofEvent? (e : Event) :
    Option MeetingR :=
  if h₁ : e.kind = .meeting then
    if h₂ : 2 ≤ e.who.length then some ⟨e, h₁, h₂⟩
    else none
  else none

def kickoffMeeting : Option MeetingR :=
  MeetingR.ofEvent? kickoff
-- ANCHOR_END: smart

-- ANCHOR: solo
/-- An LLM "remembers" Anna holding a meeting in
    Porto, alone. -/
def solo : Event :=
  { id := 4, kind := .meeting
    who := [.anna], place := .porto
    span := .mk! (day 2001 + hour 9)
                 (day 2001 + hour 10) }

-- The base axioms see nothing wrong ...
/-- info: Except.ok 3 -/
#guard_msgs in
#eval (memory.insert solo).map (·.events.length)

-- ... but `solo` is not a meeting.
/-- info: (true, false) -/
#guard_msgs in
#eval (kickoffMeeting.isSome,
       (MeetingR.ofEvent? solo).isSome)
-- ANCHOR_END: solo

-- ANCHOR: kind-law
/-- The class-specific axiom, chosen by kind. -/
def KindLaw (e : Event) : Prop :=
  match e.kind with
  | .meeting => 2 ≤ e.who.length
  | .call    => 2 ≤ e.who.length
  | .talk    => e.who ≠ []
  | .trip    => e.who.length = 1

instance (e : Event) : Decidable (KindLaw e) := by
  unfold KindLaw; split <;> infer_instance

/-- The store-level axiom: every event obeys its
    class. -/
def TaxonomyOK (s : Store) : Prop :=
  ∀ e ∈ s.events, KindLaw e

instance (s : Store) : Decidable (TaxonomyOK s) := by
  unfold TaxonomyOK; infer_instance

theorem store_taxonomy : TaxonomyOK store := by
  decide
-- ANCHOR_END: kind-law

-- ANCHOR: solo-rejected
/--
error: Tactic `decide` proved that the proposition
  TaxonomyOK (store.record solo)
is false
-/
#guard_msgs in
example : TaxonomyOK (store.record solo) := by decide
-- ANCHOR_END: solo-rejected

end Ch08.Taxonomy
