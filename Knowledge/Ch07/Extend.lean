import Knowledge.Memory

/-!
# Chapter 7: extending the ontology

The `Memory` library is fixed. We extend it from outside:
two new axioms, a consistency structure that includes the
old one, a certified store built on it, and a new class
(`Talk`) whose invariant implies one of the new axioms.
-/

namespace Ch07

open Memory Memory.World

-- ANCHOR: new_axioms
/-- Every event has at least one attendee. -/
def HasAttendees (s : Store) : Prop :=
  ∀ e ∈ s.events, e.who ≠ []

/-- Each person works for at most one organization. -/
def SingleEmployer (s : Store) : Prop :=
  ∀ r₁ ∈ s.worksAt, ∀ r₂ ∈ s.worksAt,
    r₁.1 = r₂.1 → r₁.2 = r₂.2

instance (s : Store) : Decidable (HasAttendees s) := by
  unfold HasAttendees; infer_instance
instance (s : Store) : Decidable (SingleEmployer s) := by
  unfold SingleEmployer; infer_instance
-- ANCHOR_END: new_axioms

-- ANCHOR: consistent7
/-- The extended ontology: all old axioms, plus two. -/
structure Consistent7 (s : Store) : Prop where
  core           : Consistent s
  hasAttendees   : HasAttendees s
  singleEmployer : SingleEmployer s

instance (s : Store) : Decidable (Consistent7 s) :=
  if h₁ : Consistent s then
    if h₂ : HasAttendees s then
      if h₃ : SingleEmployer s then
        isTrue ⟨h₁, h₂, h₃⟩
      else isFalse fun c => h₃ c.singleEmployer
    else isFalse fun c => h₂ c.hasAttendees
  else isFalse fun c => h₁ c.core
-- ANCHOR_END: consistent7

-- ANCHOR: violation7
/-- Old violations, wrapped, plus the new ones. -/
inductive Violation7 where
  | core (v : Violation)
  | noAttendees
  | twoEmployers
  deriving DecidableEq, Repr

def diagnose7 (s : Store) : Option Violation7 :=
  match diagnose s with
  | some v => some (.core v)
  | none =>
    if ¬ HasAttendees s then some .noAttendees
    else if ¬ SingleEmployer s then some .twoEmployers
    else none
-- ANCHOR_END: violation7

-- ANCHOR: certified7
structure Certified7 where
  store : Store
  ok    : Consistent7 store

namespace Certified7

def insert (m : Certified7) (e : Event) :
    Except Violation7 Certified7 :=
  let s' := m.store.record e
  if h : Consistent7 s' then .ok ⟨s', h⟩
  else .error ((diagnose7 s').getD .noAttendees)

/-- Forget the new axioms: the extension refines
    the old ontology, it does not replace it. -/
def toCertified (m : Certified7) : Certified :=
  ⟨m.store, m.ok.core⟩

end Certified7
-- ANCHOR_END: certified7

-- ANCHOR: memory7
/-- The world store satisfies the extended ontology
    too. The kernel checks all six axioms. -/
theorem store_ok7 : Consistent7 store := by decide

def memory7 : Certified7 := ⟨store, store_ok7⟩
-- ANCHOR_END: memory7

-- ANCHOR: ghost
/-- A talk that nobody attends: an LLM extracted the
    title and the room but no people. -/
def ghost : Event :=
  { id := 6, kind := .talk, who := []
    place := .porto
    span := .mk! (day 2002 + hour 15)
                 (day 2002 + hour 16) }

-- The old ontology has no objection:
/-- info: Except.ok 3 -/
#guard_msgs in
#eval (memory.insert ghost).map (·.events.length)

/-- info: Except.error (Ch07.Violation7.noAttendees) -/
#guard_msgs in
#eval (memory7.insert ghost).map (·.store.events.length)
-- ANCHOR_END: ghost

-- ANCHOR: old_traps
/--
info: Except.error
  (Ch07.Violation7.core (Memory.Violation.noBilocation))
-/
#guard_msgs (whitespace := lax) in
#eval (memory7.insert phantom).map (·.store.events.length)
-- ANCHOR_END: old_traps

-- ANCHOR: talk
/-- A new class: a talk with a speaker who is there. -/
structure Talk where
  event   : Event
  isTalk  : event.kind = .talk
  speaker : Person
  present : speaker ∈ event.who

/-- The class invariant implies the new axiom for
    this one event: a talk is never empty. -/
theorem Talk.nonempty (t : Talk) : t.event.who ≠ [] :=
  List.ne_nil_of_mem t.present
-- ANCHOR_END: talk

-- ANCHOR: talk_smart
def Talk.ofEvent? (e : Event) (p : Person) :
    Option Talk :=
  if h₁ : e.kind = .talk then
    if h₂ : p ∈ e.who then some ⟨e, h₁, p, h₂⟩
    else none
  else none

/-- info: false -/
#guard_msgs in
#eval (Talk.ofEvent? ghost .lena).isSome
-- ANCHOR_END: talk_smart

-- ANCHOR: lenaTalk
def lenaTalk : Talk :=
  { event :=
      { ghost with who := [.lena, .sofia, .marco] }
    isTalk := rfl
    speaker := .lena
    present := by decide }

/-- info: Except.ok 3 -/
#guard_msgs in
#eval (memory7.insert lenaTalk.event).map
  (·.store.events.length)
-- ANCHOR_END: lenaTalk

/-! ## Growing the population at run time

`Person` is closed: a sixth person is a new constructor and a
rebuild. Production agents type identifiers instead, and pair
each with a proof that it is registered. Chapter 12's
`Agent/Registry.lean` puts the same idea into a store axiom. -/

-- ANCHOR: dynamic_ids
/-- An open identifier: any string, but its own type. -/
structure PersonId where
  val : String
  deriving DecidableEq, Repr

/-- The people the agent knows, each listed once. -/
structure Registry where
  people : List PersonId
  nodup  : people.Nodup

/-- A person known to `r`: an identifier and a proof
    that `r` lists it. The type depends on the data. -/
abbrev KnownPerson (r : Registry) :=
  { p : PersonId // p ∈ r.people }

/-- Smart constructor: adds a new identifier and
    refuses one that is already registered. -/
def Registry.register (r : Registry) (p : PersonId) :
    Option Registry :=
  if h : p ∈ r.people then none
  else some ⟨p :: r.people, List.nodup_cons.mpr ⟨h, r.nodup⟩⟩

/-- Look a name up: a `KnownPerson` brings its proof. -/
def Registry.find? (r : Registry) (p : PersonId) :
    Option (KnownPerson r) :=
  if h : p ∈ r.people then some ⟨p, h⟩ else none
-- ANCHOR_END: dynamic_ids

-- ANCHOR: dynamic_ids_demo
def registry : Registry :=
  ⟨[⟨"anna"⟩, ⟨"lena"⟩], by decide⟩

def oksana : PersonId := ⟨"oksana"⟩

/-- Registering Oksana: a function call on data. -/
def grown : Registry :=
  (registry.register oksana).getD registry

/-- info: (false, true, true) -/
#guard_msgs in
#eval ((registry.find? oksana).isSome,
       (grown.find? oksana).isSome,
       (grown.register ⟨"anna"⟩).isNone)
-- ANCHOR_END: dynamic_ids_demo

end Ch07
