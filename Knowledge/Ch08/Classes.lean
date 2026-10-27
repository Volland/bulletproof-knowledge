import Knowledge.Memory

/-!
# Chapter 8 — Type classes as class hierarchies

A type class names a capability ("has a place", "has a
time span"). `extends` builds subclasses, an instance
declares membership, and Prop fields are laws that each
member must prove.
-/

namespace Ch08

open Memory Memory.World

-- ANCHOR: located
/-- Things that happen somewhere. -/
class Located (α : Type) where
  place : α → City

/-- Things that occupy a span of time. The last two
    methods have defaults computed from `span`. -/
class Timed (α : Type) where
  span     : α → Interval
  start    : α → Time := fun a => (span a).start
  duration : α → Nat :=
    fun a => (span a).stop - (span a).start

/-- Things people take part in. -/
class Participant (α : Type) where
  who     : α → List Person
  attends : α → Person → Bool :=
    fun a p => (who a).contains p
-- ANCHOR_END: located

-- ANCHOR: extends
/-- Located in space and in time. -/
class Happening (α : Type)
    extends Located α, Timed α

/-- Located, with people present. -/
class Gathering (α : Type)
    extends Located α, Participant α

/-- Both: the diamond. `Located` is reached twice. -/
class Occurrence (α : Type)
    extends Happening α, Gathering α
-- ANCHOR_END: extends

-- ANCHOR: event-instance
/-- Membership: `Event` is an `Occurrence`. We give
    the three required methods; the defaults fill in
    `start`, `duration`, and `attends`. -/
instance : Occurrence Event where
  place e := e.place
  span  e := e.span
  who   e := e.who

/-- info: (60, true, false) -/
#guard_msgs in
#eval (Timed.duration kickoff,
       Participant.attends kickoff .anna,
       Participant.attends kickoff .lena)
-- ANCHOR_END: event-instance

-- ANCHOR: generic
/-- Any two located things, of any two types. -/
def sameCity {α β : Type} [Located α] [Located β]
    (a : α) (b : β) : Bool :=
  Located.place a == Located.place b

/-- People present at both occurrences. -/
def shared {α : Type} [Occurrence α] (a b : α) :
    List Person :=
  (Participant.who a).filter (Participant.attends b)

/-- info: (false, [Memory.Person.anna]) -/
#guard_msgs in
#eval (sameCity kickoff review, shared kickoff review)
-- ANCHOR_END: generic

-- ANCHOR: not-member
/--
error: failed to synthesize instance of type class
  Located Person

Hint: Type class instance resolution failures can
be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
#eval Located.place Person.anna
-- ANCHOR_END: not-member

-- ANCHOR: visit
/-- A second member type: one person in one city. -/
structure Visit where
  person : Person
  city   : City
  span   : Interval

/-- `attends` is overridden with a direct test;
    the default would build a list first. -/
instance : Occurrence Visit where
  place v   := v.city
  span  v   := v.span
  who   v   := [v.person]
  attends v p := v.person == p

def lenaInPorto : Visit :=
  ⟨.lena, .porto, .mk! (day 1990) (day 1995)⟩

/-- info: (false, 7200) -/
#guard_msgs in
#eval (sameCity lenaInPorto kickoff,
       Timed.duration lenaInPorto)
-- ANCHOR_END: visit

-- ANCHOR: diamond
/-- Only `Happening` is stored whole. The `Gathering`
    parent is rebuilt from pieces, and its `Located`
    part is the very one inside `Happening`. -/
example {α : Type} [inst : Occurrence α] :
    inst.toGathering =
      { toLocated     := inst.toHappening.toLocated
        toParticipant := inst.toParticipant } :=
  rfl
-- ANCHOR_END: diamond

-- Shown in the chapter as text (lines too wide).
/--
info: class Ch08.Occurrence (α : Type) : Type
number of parameters: 1
parents:
  Ch08.Occurrence.toHappening : Happening α
  Ch08.Occurrence.toGathering : Gathering α
fields:
  Ch08.Located.place : α → City
  Ch08.Timed.span : α → Interval
  Ch08.Timed.start : α → Time :=
    fun a => (Timed.span a).start
  Ch08.Timed.duration : α → Nat :=
    fun a => (Timed.span a).stop - (Timed.span a).start
  Ch08.Participant.who : α → List Person
  Ch08.Participant.attends : α → Person → Bool :=
    fun a p => (Participant.who a).contains p
constructor:
  Ch08.Occurrence.mk {α : Type}
    [toHappening : Happening α]
    [toParticipant : Participant α] : Occurrence α
field notation resolution order:
  Ch08.Occurrence, Ch08.Happening, Ch08.Gathering,
  Ch08.Located, Ch08.Timed, Ch08.Participant
-/
#guard_msgs (whitespace := lax) in
#print Occurrence

-- ANCHOR: coherent
/-- Both roads to `Located` lead to the same place,
    by definition: `rfl` closes the goal. -/
example {α : Type} [Occurrence α] (a : α) :
    (Occurrence.toHappening.toLocated
      : Located α).place a =
    (Occurrence.toGathering.toLocated
      : Located α).place a :=
  rfl
-- ANCHOR_END: coherent

-- ANCHOR: subtype-instance
/-- Membership is inherited by subtypes: whatever
    satisfies `p` is still an occurrence. -/
instance {α : Type} {p : α → Prop} [Occurrence α] :
    Occurrence { a // p a } where
  place a := Located.place a.val
  span  a := Timed.span a.val
  who   a := Participant.who a.val
-- ANCHOR_END: subtype-instance

-- ANCHOR: physical-opaque
/-- In-person events, as a `def` (compare `MeetingEv`
    in `Subtypes.lean`). -/
def InPerson := { e : Event // e.kind.physical = true }

def kickoffP : InPerson := ⟨kickoff, rfl⟩

/--
error: failed to synthesize instance of type class
  Located InPerson

Hint: Type class instance resolution failures can
be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
#eval Located.place kickoffP
-- ANCHOR_END: physical-opaque

-- ANCHOR: physical-instance
/-- Tell instance search to see through the `def`. -/
instance : Occurrence InPerson :=
  inferInstanceAs
    (Occurrence { e : Event // e.kind.physical = true })

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval Located.place kickoffP
-- ANCHOR_END: physical-instance

-- ANCHOR: synth
/-- info: instOccurrenceInPerson.toGathering.toLocated -/
#guard_msgs in
#synth Located InPerson
-- ANCHOR_END: synth

-- The trace is shown, trimmed, as text in the chapter.
/--
error: failed to synthesize
  Located Person

Hint: Additional diagnostic information may be
available using the `set_option diagnostics true`
command.
---
trace: [Meta.synthInstance] ❌️ Located Person
  [Meta.synthInstance] ✅️ new goal Located Person
    [Meta.synthInstance.instances]
      #[@Happening.toLocated, @Gathering.toLocated]
  [Meta.synthInstance.apply] ✅️ apply
    @Gathering.toLocated to Located Person
    [Meta.synthInstance.tryResolve] ✅️
      Located Person ≟ Located Person
    [Meta.synthInstance] ✅️ new goal Gathering Person
      [Meta.synthInstance.instances]
        #[@Occurrence.toGathering]
  [Meta.synthInstance.apply] ✅️ apply
    @Occurrence.toGathering to Gathering Person
    [Meta.synthInstance.tryResolve] ✅️
      Gathering Person ≟ Gathering Person
    [Meta.synthInstance] ✅️ no instances for
      Occurrence Person
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance.apply] ✅️ apply
    @Happening.toLocated to Located Person
    [Meta.synthInstance.tryResolve] ✅️
      Located Person ≟ Located Person
    [Meta.synthInstance] ✅️ new goal Happening Person
      [Meta.synthInstance.instances]
        #[@Occurrence.toHappening]
  [Meta.synthInstance.apply] ✅️ apply
    @Occurrence.toHappening to Happening Person
    [Meta.synthInstance.tryResolve] ✅️
      Happening Person ≟ Happening Person
    [Meta.synthInstance] ✅️ no instances for
      Occurrence Person
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs (whitespace := lax) in
-- ANCHOR: trace
set_option trace.Meta.synthInstance true in
#synth Located Person
-- ANCHOR_END: trace

-- ANCHOR: law
/-- A subclass with a law: at least one person is
    present. Every instance must *prove* `nonempty`. -/
class Staffed (α : Type) extends Participant α where
  nonempty : ∀ a, who a ≠ []

/-- A theorem proven once, for every member. -/
theorem Staffed.someone {α : Type} [Staffed α]
    (a : α) : ∃ p, p ∈ Participant.who a := by
  cases h : Participant.who a with
  | nil => exact absurd h (Staffed.nonempty a)
  | cons p _ => exact ⟨p, List.mem_cons_self⟩
-- ANCHOR_END: law

-- ANCHOR: law-visit
/-- A visit always has its visitor. -/
instance : Staffed Visit where
  who v := [v.person]
  nonempty v := List.cons_ne_nil v.person []
-- ANCHOR_END: law-visit

-- ANCHOR: law-event
/-- No `Staffed Event` instance can exist: an event
    with nobody in it is a well-typed `Event`. -/
theorem event_not_staffed :
    ¬ ∀ e : Event, e.who ≠ [] :=
  fun h => h ⟨0, .call, [], .kyiv, .mk! 0 0⟩ rfl
-- ANCHOR_END: law-event

-- ANCHOR: law-subtype
/-- Events that do have someone present. -/
abbrev StaffedEvent := { e : Event // e.who ≠ [] }

instance : Staffed StaffedEvent where
  who e := e.val.who
  nonempty e := e.property

def kickoffS : StaffedEvent := ⟨kickoff, by decide⟩

/-- info: [Memory.Person.anna, Memory.Person.marco] -/
#guard_msgs in
#eval Participant.who kickoffS
-- ANCHOR_END: law-subtype

-- ANCHOR: overlap
section Overlap
/-- A second, conflicting `Located Event`: say, a
    plugin that files every event under head office. -/
local instance : Located Event := ⟨fun _ => .berlin⟩

/-- info: Memory.City.berlin -/
#guard_msgs in
#eval Located.place kickoff

/-- info: instLocatedEvent -/
#guard_msgs in
#synth Located Event
end Overlap

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval Located.place kickoff
-- ANCHOR_END: overlap

section Loop
-- ANCHOR: loop
/-- "A thing is located if a list of such things is."
    Each step asks for a bigger goal than the last. -/
local instance {α : Type} [Located (List α)] :
    Located α :=
  ⟨fun a => Located.place [a]⟩
-- ANCHOR_END: loop

/--
error: failed to synthesize
  Located Person
(deterministic) timeout at `typeclass`, maximum
number of heartbeats (2000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats
<num>` to set the limit.

Hint: Additional diagnostic information may be
available using the `set_option diagnostics true`
command.

Hint: Additional diagnostic information may be
available using the `set_option diagnostics true`
command.
-/
#guard_msgs (whitespace := lax) in
-- ANCHOR: loop

set_option synthInstance.maxHeartbeats 2000 in
#eval Located.place Person.anna
-- ANCHOR_END: loop
end Loop

-- ANCHOR: cycle
section Cycle
/-- A plain cycle: located if timed, timed if located. -/
local instance {α : Type} [Timed α] : Located α :=
  ⟨fun _ => .kyiv⟩
local instance {α : Type} [Located α] : Timed α :=
  ⟨fun _ => .mk! 0 0, fun _ => 0, fun _ => 0⟩

/--
error: failed to synthesize instance of type class
  Located Person

Hint: Type class instance resolution failures can
be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
#eval Located.place Person.anna
end Cycle
-- ANCHOR_END: cycle

end Ch08
