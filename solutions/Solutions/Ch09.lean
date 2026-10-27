import Knowledge.Memory
import Knowledge.Ch09.Invariants
import Knowledge.Ch09.Updates
import Knowledge.Ch09.Evolution

/-!
# Solutions to the Chapter 9 exercises
-/

namespace Solutions.Ch09

open Memory Memory.World Interval
open _root_.Ch09

-- Exercise 9.1: `insert` never touches reporting lines.
theorem insert_reportsTo {m m' : Certified} {e : Event}
    (h : m.insert e = .ok m') :
    m'.store.reportsTo = m.store.reportsTo := by
  rw [insert_ok h]
  rfl

-- Exercise 9.2: forgetting every event of one kind is
-- a safe update.
def forgetKind (k : EventKind) : SafeUpdate where
  run s := { s with events := s.events.filter (·.kind != k) }
  safe _ c := consistent_of_sublist c List.filter_sublist

/-- info: [1] -/
#guard_msgs in
#eval ((forgetKind .call).apply memory).events.map (·.id)

-- Exercise 9.3: safe updates compose.
def andThen (u v : SafeUpdate) : SafeUpdate where
  run s := v.run (u.run s)
  safe s c := v.safe _ (u.safe s c)

def forgetBoth : SafeUpdate :=
  andThen (forget 1) (forget 2)

/-- info: 0 -/
#guard_msgs in
#eval (forgetBoth.apply memory).events.length

-- Exercise 9.4: a new axiom, "every talk has a
-- speaker", with a counterexample to the identity
-- migration.
def TalksHaveOne (s : Store) : Prop :=
  ∀ e ∈ s.events, e.kind = .talk → e.who ≠ []

instance (s : Store) : Decidable (TalksHaveOne s) := by
  unfold TalksHaveOne; infer_instance

def emptyTalk : Event :=
  { id := 7, kind := .talk, who := [], place := .porto
    span := .mk! (day 2002) (day 2002 + 45) }

theorem talks_unsafe :
    ¬ Safe Consistent
        (fun s => Consistent s ∧ TalksHaveOne s) id := by
  intro h
  have := h (store.record emptyTalk) (by decide)
  revert this
  decide

theorem store_has_speakers : TalksHaveOne store := by
  decide

-- Exercise 9.5: a certified answer to
-- "did Anna and Taras share an event?"
def Shared (s : Store) (p q : Person) : Prop :=
  ∃ e ∈ s.events, p ∈ e.who ∧ q ∈ e.who

instance (s : Store) (p q : Person) :
    Decidable (Shared s p q) := by
  unfold Shared; infer_instance

theorem anna_taras : Shared store .anna .taras :=
  ⟨review, by decide, by decide, by decide⟩

theorem not_lena_marco : ¬ Shared store .lena .marco := by
  decide

end Solutions.Ch09
