import Knowledge.Memory
import Knowledge.Ch08.Subtypes
import Knowledge.Ch08.Classes
import Knowledge.Ch08.Places
import Knowledge.Ch08.Events

/-!
# Solutions to the Chapter 8 exercises
-/

namespace Solutions.Ch08

open Memory Memory.World
open _root_.Ch08

/-! ## Exercise 8.1 — two subclasses, one link -/

/-- Every meeting is in person: a link between two
    subclasses, proven once with `MeetingEv.physical`. -/
def MeetingEv.toInPerson (m : MeetingEv) : InPerson :=
  ⟨m, MeetingEv.physical m⟩

instance : Coe MeetingEv InPerson := ⟨MeetingEv.toInPerson⟩

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval Located.place (kickoffM : InPerson)

/-- The same class as an `abbrev`: instance search sees
    the subtype, so the generic subtype instance applies
    and no `inferInstanceAs` is needed. -/
abbrev InPersonA := { e : Event // e.kind.physical = true }

def kickoffA : InPersonA := ⟨kickoff, rfl⟩

/-- info: Memory.City.lisbon -/
#guard_msgs in
#eval Located.place kickoffA

/-! ## Exercise 8.2 — a class with a host -/

class Hosted (α : Type) extends Participant α where
  host         : α → Person
  host_present : ∀ a, host a ∈ who a

instance : Hosted Visit where
  who v          := [v.person]
  host v         := v.person
  host_present _ := List.mem_cons_self

/-- Every hosted thing has somebody present. -/
theorem Hosted.nonempty {α : Type} [Hosted α] (a : α) :
    Participant.who a ≠ [] :=
  List.ne_nil_of_mem (Hosted.host_present a)

/-- So every `Hosted` type is `Staffed`. -/
instance {α : Type} [Hosted α] : Staffed α where
  nonempty := Hosted.nonempty

/-! ## Exercise 8.3 — paths and `Inside` -/

theorem kyiv_in_east :
    PartOf (.city .kyiv) (.region .easternEurope) :=
  .step (.city .kyiv) (.direct (.country .ukraine))

theorem iberia_not_in_portugal :
    ¬ PartOf (.region .iberia) (.country .portugal) :=
  fun h => absurd h.level_lt (by decide)

theorem Inside.trans {a b c : Place} :
    Inside a b → Inside b c → Inside a c := by
  intro h₁ h₂
  cases h₁ with
  | inl e => subst e; exact h₂
  | inr p =>
    cases h₂ with
    | inl e => subst e; exact .inr p
    | inr q => exact .inr (p.trans q)

/-! ## Exercise 8.4 — where Marco and Taras were -/

theorem marco_in_portugal :
    WasIn store .marco (.country .portugal) :=
  ⟨kickoff, by decide, rfl, by decide,
   .inr (.direct (.city .lisbon))⟩

/-- Taras only took part in the review, a call. -/
theorem taras_not_in_ukraine :
    ¬ WasIn store .taras (.country .ukraine) := by
  decide

/-! ## Exercise 8.5 — classifying calls -/

open Taxonomy in
def callOfEvent? (e : Event) : Option CallR :=
  if h₁ : e.kind = .call then
    if h₂ : 2 ≤ e.who.length then some ⟨e, h₁, h₂⟩
    else none
  else none

/-- info: (true, false) -/
#guard_msgs in
#eval ((callOfEvent? review).isSome,
       (callOfEvent? kickoff).isSome)

/-- The review as a certified call ... -/
def reviewCall : Taxonomy.CallR := ⟨review, rfl, by decide⟩

/-- ... inherits the shared theorem: someone was there. -/
example : ∃ p, p ∈ review.who :=
  Taxonomy.EventClass.someone reviewCall

end Solutions.Ch08
