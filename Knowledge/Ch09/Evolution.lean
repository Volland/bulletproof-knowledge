import Knowledge.Ch09.Invariants

/-!
# Chapter 9: schema evolution

The ontology changes: calls now require at least two
participants. Old memories were certified against the
old axioms. Do they satisfy the new ones? A migration is
a function between stores, and "safe" is a theorem.
-/

namespace Ch09

open Memory Memory.World Interval

-- ANCHOR: new_axiom
/-- The new rule: a call has at least two people. -/
def CallsHaveTwo (s : Store) : Prop :=
  ∀ e ∈ s.events, e.kind = .call → 2 ≤ e.who.length

instance (s : Store) : Decidable (CallsHaveTwo s) := by
  unfold CallsHaveTwo; infer_instance

/-- Version 2 of the ontology: the old axioms plus
    the new one. -/
structure ConsistentV2 (s : Store) : Prop where
  old   : Consistent s
  calls : CallsHaveTwo s

instance (s : Store) : Decidable (ConsistentV2 s) :=
  if h₁ : Consistent s then
    if h₂ : CallsHaveTwo s then isTrue ⟨h₁, h₂⟩
    else isFalse fun c => h₂ c.calls
  else isFalse fun c => h₁ c.old
-- ANCHOR_END: new_axiom

-- ANCHOR: migration
/-- An ontology, for this chapter: which stores
    it accepts. -/
abbrev Ontology := Store → Prop

/-- A migration is safe when it sends every store
    the old ontology accepts to one the new ontology
    accepts. -/
def Safe (old new : Ontology)
    (f : Store → Store) : Prop :=
  ∀ s, old s → new (f s)
-- ANCHOR_END: migration

-- ANCHOR: our_store
/-- Our own memory passes the new rule. -/
theorem store_v2 : ConsistentV2 store := by decide
-- ANCHOR_END: our_store

-- ANCHOR: counterexample
/-- Marco calls in and nobody else joins. -/
def voicemail : Event :=
  { id := 3, kind := .call
    who := [.marco], place := .lisbon
    span := .mk! (day 2001) (day 2001 + 5) }

def oldStore : Store :=
  store.record voicemail

/-- The old ontology accepts it ... -/
theorem old_ok : Consistent oldStore := by decide

/-- ... and the identity migration is not safe. -/
theorem id_unsafe :
    ¬ Safe Consistent ConsistentV2 id := by
  intro h
  have := h oldStore old_ok
  revert this
  decide
-- ANCHOR_END: counterexample

-- ANCHOR: backward
/-- Going back is always safe: V2 only adds a rule. -/
theorem v2_to_v1 : Safe ConsistentV2 Consistent id :=
  fun _ h => h.old
-- ANCHOR_END: backward

-- ANCHOR: drop_solo
/-- One repair: forget calls with fewer than two
    people. -/
def soloCall (e : Event) : Bool :=
  e.kind == .call && e.who.length < 2

def dropSolo (s : Store) : Store :=
  { s with events := s.events.filter (!soloCall ·) }

theorem dropSolo_safe :
    Safe Consistent ConsistentV2 dropSolo := by
  intro s c
  refine ⟨consistent_of_sublist c List.filter_sublist, ?_⟩
  intro e he hk
  simp only [dropSolo, List.mem_filter] at he
  simp [soloCall, hk] at he
  omega
-- ANCHOR_END: drop_solo

-- ANCHOR: drop_eval
/-- info: [2, 1] -/
#guard_msgs in
#eval (dropSolo oldStore).events.map (·.id)
-- ANCHOR_END: drop_eval

-- ANCHOR: retag
/-- Another repair: call a solo call a `talk`. -/
def retag (s : Store) : Store :=
  { s with events := s.events.map fun e =>
      if soloCall e then { e with kind := .talk }
      else e }

/-- Marco's voicemail, from Lisbon, during a Kyiv
    meeting he attended. -/
def kyivSync : Event :=
  { id := 4, kind := .meeting
    who := [.marco, .lena], place := .kyiv
    span := .mk! (day 2001) (day 2001 + 60) }

theorem retag_unsafe :
    ¬ Safe Consistent ConsistentV2 retag := by
  intro h
  have := h (oldStore.record kyivSync) (by decide)
  revert this
  decide
-- ANCHOR_END: retag

end Ch09
