import Knowledge.Memory

/-!
# Solutions to the Chapter 7 exercises
-/

namespace Solutions.Ch07

open Memory Memory.World

/-! ## Exercise 7.1: the `Met` relation -/

/-- Two different people attended the same event. -/
def Met (s : Store) (p q : Person) : Prop :=
  p ≠ q ∧ ∃ e ∈ s.events, p ∈ e.who ∧ q ∈ e.who

instance (s : Store) (p q : Person) :
    Decidable (Met s p q) := by
  unfold Met; infer_instance

example : Met store .anna .marco := by decide
-- A call counts: `Met` says nothing about place.
example : Met store .anna .taras := by decide
example : ¬ Met store .marco .taras := by decide
example : ¬ Met store .anna .anna := by decide

/-! ## Exercise 7.2: the class of calls -/

abbrev Call := { e : Event // e.kind = .call }

def reviewC : Call := ⟨review, by decide⟩

/-- No call needs physical presence. -/
theorem Call.notPhysical (c : Call) :
    c.val.kind.physical = false := by
  rw [c.property]; rfl

/--
error: Tactic `decide` proved that the proposition
  kickoff.kind = EventKind.call
is false
-/
#guard_msgs in
def kickoffC : Call := ⟨kickoff, by decide⟩

/-! ## Exercise 7.3: nobody reports to themselves -/

def NoSelfReport (s : Store) : Prop :=
  ∀ r ∈ s.reportsTo, r.1 ≠ r.2

instance (s : Store) : Decidable (NoSelfReport s) := by
  unfold NoSelfReport; infer_instance

example : NoSelfReport store := by decide

def loop : Store :=
  { store with
    reportsTo := (.lena, .lena) :: store.reportsTo }

example : ¬ NoSelfReport loop := by decide

-- `SingleManager` alone does not catch it:
-- Lena still has exactly one manager.
example : SingleManager loop := by decide

/-! ## Exercise 7.4: the edge of Sofia's trap -/

def meetAt (t : Time) : Event :=
  { id := 7, kind := .meeting
    who := [.sofia, .marco], place := .porto
    span := ⟨t, t + 60, Nat.le_add_right t 60⟩ }

/-- info: Except.ok 3 -/
#guard_msgs in
#eval (memory.insert (meetAt (day 1000))).map
  (·.events.length)

/-- info: Except.error (Memory.Violation.bornBefore) -/
#guard_msgs in
#eval (memory.insert (meetAt (day 1000 - 1))).map
  (·.events.length)

end Solutions.Ch07
