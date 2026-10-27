import Knowledge.Memory.Facts

/-!
# Axioms of the agent's world

Each axiom is a proposition about a `Store`, and each is
*decidable*: the agent can compute whether it holds.
A store is consistent when all axioms hold. In the formal
sense of this book, a hallucination is a proposed fact
that would make a consistent store inconsistent.
-/

namespace Memory

open Interval

-- ANCHOR: axioms
/-- Nobody attends an event before they are born. -/
def BornBefore (s : Store) : Prop :=
  ∀ e ∈ s.events, ∀ p ∈ e.who,
    s.born p ≤ e.span.start

/-- Nobody is physically in two different cities
    at overlapping times. -/
def NoBilocation (s : Store) : Prop :=
  ∀ e₁ ∈ s.events, ∀ e₂ ∈ s.events,
    e₁.kind.physical = true →
    e₂.kind.physical = true →
    e₁.place ≠ e₂.place →
    Overlaps e₁.span e₂.span →
    ∀ p ∈ e₁.who, p ∉ e₂.who

/-- Each person reports to at most one manager. -/
def SingleManager (s : Store) : Prop :=
  ∀ r₁ ∈ s.reportsTo, ∀ r₂ ∈ s.reportsTo,
    r₁.1 = r₂.1 → r₁.2 = r₂.2

/-- Event identifiers are unique. -/
def UniqueIds (s : Store) : Prop :=
  (s.events.map (·.id)).Nodup
-- ANCHOR_END: axioms

instance (s : Store) : Decidable (BornBefore s) := by
  unfold BornBefore; infer_instance
instance (s : Store) : Decidable (NoBilocation s) := by
  unfold NoBilocation; infer_instance
instance (s : Store) : Decidable (SingleManager s) := by
  unfold SingleManager; infer_instance
instance (s : Store) : Decidable (UniqueIds s) := by
  unfold UniqueIds; infer_instance

-- ANCHOR: consistent
/-- A store is consistent when every axiom holds. -/
structure Consistent (s : Store) : Prop where
  bornBefore    : BornBefore s
  noBilocation  : NoBilocation s
  singleManager : SingleManager s
  uniqueIds     : UniqueIds s
-- ANCHOR_END: consistent

instance (s : Store) : Decidable (Consistent s) :=
  if h₁ : BornBefore s then
    if h₂ : NoBilocation s then
      if h₃ : SingleManager s then
        if h₄ : UniqueIds s then
          isTrue ⟨h₁, h₂, h₃, h₄⟩
        else isFalse fun c => h₄ c.uniqueIds
      else isFalse fun c => h₃ c.singleManager
    else isFalse fun c => h₂ c.noBilocation
  else isFalse fun c => h₁ c.bornBefore

-- ANCHOR: violation
/-- Which axiom a proposed fact would break.
    Chapter 12 sends this back to the LLM. -/
inductive Violation where
  | bornBefore | noBilocation
  | singleManager | uniqueIds
  deriving DecidableEq, Repr

/-- Name the first axiom that fails, if any. -/
def diagnose (s : Store) : Option Violation :=
  if ¬ BornBefore s then some .bornBefore
  else if ¬ NoBilocation s then some .noBilocation
  else if ¬ SingleManager s then some .singleManager
  else if ¬ UniqueIds s then some .uniqueIds
  else none
-- ANCHOR_END: violation

end Memory
