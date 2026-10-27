import Knowledge.Memory

/-!
# Chapter 9: invariants

Two kinds of proof. A proof by computation evaluates an
axiom on one concrete store. A proof by reasoning holds
for every store, including the ones the agent has not
seen yet.
-/

namespace Ch09

open Memory Memory.World Interval

-- ANCHOR: by_computation
/-- Proof by computation: the kernel evaluates
    `NoBilocation` on this one store. -/
theorem store_noBilocation : NoBilocation store := by
  decide
-- ANCHOR_END: by_computation

-- ANCHOR: by_reasoning
/-- Proof by reasoning: for every interval with
    positive length, it overlaps itself. -/
theorem overlaps_self (i : Interval)
    (h : i.start < i.stop) : Overlaps i i :=
  ⟨h, h⟩
-- ANCHOR_END: by_reasoning

-- ANCHOR: no_decide_forall
/--
error: failed to synthesize
  Decidable
    (∀ (i : Interval), i.start < i.stop → i.Overlaps i)

Hint: Additional diagnostic information may be
available using the `set_option diagnostics true`
command.
-/
#guard_msgs (whitespace := lax) in
example : ∀ i : Interval,
    i.start < i.stop → Overlaps i i := by
  decide
-- ANCHOR_END: no_decide_forall

-- ANCHOR: free_theorem
/-- Every certified store satisfies `BornBefore`:
    the proof is already inside it. -/
theorem attended_after_birth (m : Certified)
    {e : Event} (he : e ∈ m.events)
    {p : Person} (hp : p ∈ e.who) :
    m.store.born p ≤ e.span.start :=
  m.ok.bornBefore e he p hp
-- ANCHOR_END: free_theorem

-- ANCHOR: insert_ok
/-- If `insert` succeeds, the new store is the old
    store with the event added. -/
theorem insert_ok {m m' : Certified} {e : Event}
    (h : m.insert e = .ok m') :
    m'.store = m.store.record e := by
  simp only [Certified.insert] at h
  split at h
  · cases h; rfl
  · cases h
-- ANCHOR_END: insert_ok

-- ANCHOR: insert_facts
/-- The event is in the new store. -/
theorem insert_mem {m m' : Certified} {e : Event}
    (h : m.insert e = .ok m') : e ∈ m'.events := by
  simp [Certified.events, insert_ok h, Store.record]

/-- Nothing that was there is lost. -/
theorem insert_keeps {m m' : Certified} {e x : Event}
    (h : m.insert e = .ok m') (hx : x ∈ m.events) :
    x ∈ m'.events := by
  simp [Certified.events, insert_ok h, Store.record]
  exact .inr hx

/-- The new store is consistent. -/
theorem insert_consistent {m m' : Certified}
    {e : Event} (_ : m.insert e = .ok m') :
    Consistent m'.store :=
  m'.ok
-- ANCHOR_END: insert_facts

-- ANCHOR: insert_complete
/-- `insert` accepts exactly the events that keep
    the store consistent: nothing true is refused. -/
theorem insert_ok_iff (m : Certified) (e : Event) :
    (∃ m', m.insert e = .ok m') ↔
      Consistent (m.store.record e) := by
  constructor
  · intro ⟨m', h⟩
    rw [← insert_ok h]
    exact m'.ok
  · intro h
    exact ⟨⟨_, h⟩, by simp [Certified.insert, h]⟩
-- ANCHOR_END: insert_complete

-- ANCHOR: sublist
/-- Keeping only some of the events, in order, never
    breaks an axiom. -/
theorem consistent_of_sublist {s : Store}
    {es : List Event} (c : Consistent s)
    (h : es.Sublist s.events) :
    Consistent { s with events := es } where
  bornBefore e he p hp :=
    c.bornBefore e (h.subset he) p hp
  noBilocation e₁ h₁ e₂ h₂ :=
    c.noBilocation e₁ (h.subset h₁) e₂ (h.subset h₂)
  singleManager := c.singleManager
  uniqueIds := c.uniqueIds.sublist (h.map _)
-- ANCHOR_END: sublist

-- ANCHOR: remove
/-- Forget every event with this identifier. -/
def removeId (s : Store) (i : Nat) : Store :=
  { s with events := s.events.filter (·.id != i) }

/-- Removing events preserves consistency. -/
theorem removeId_consistent {s : Store}
    (c : Consistent s) (i : Nat) :
    Consistent (removeId s i) :=
  consistent_of_sublist c List.filter_sublist
-- ANCHOR_END: remove

-- ANCHOR: call_safe
/-- A call never breaks `NoBilocation`: it is not a
    physical event, so it cannot put anyone in a
    second city. -/
theorem call_noBilocation {s : Store} {e : Event}
    (hk : e.kind = .call) (h : NoBilocation s) :
    NoBilocation (s.record e) := by
  intro e₁ h₁ e₂ h₂ ph₁ ph₂
  simp only [Store.record, List.mem_cons] at h₁ h₂
  rcases h₁ with rfl | h₁
  · simp [hk, EventKind.physical] at ph₁
  rcases h₂ with rfl | h₂
  · simp [hk, EventKind.physical] at ph₂
  exact h e₁ h₁ e₂ h₂ ph₁ ph₂
-- ANCHOR_END: call_safe

-- ANCHOR: call_never_rejected
/-- If a store has no bilocation, `diagnose` does not
    blame bilocation. -/
theorem diagnose_ne {s : Store} (h : NoBilocation s) :
    (diagnose s).getD .uniqueIds ≠ .noBilocation := by
  unfold diagnose
  repeat' split
  all_goals simp_all

/-- So `insert` never rejects a call for bilocation.
    It may still reject it for another reason. -/
theorem call_not_bilocation (m : Certified)
    {e : Event} (hk : e.kind = .call) :
    m.insert e ≠ .error .noBilocation := by
  have hb := call_noBilocation hk m.ok.noBilocation
  simp only [Certified.insert]
  split
  · simp
  · simpa using diagnose_ne hb
-- ANCHOR_END: call_never_rejected

-- ANCHOR: broken
/-- What each violation name claims about a store. -/
def Broken : Violation → Store → Prop
  | .bornBefore,    s => ¬ BornBefore s
  | .noBilocation,  s => ¬ NoBilocation s
  | .singleManager, s => ¬ SingleManager s
  | .uniqueIds,     s => ¬ UniqueIds s
-- ANCHOR_END: broken

-- ANCHOR: diagnose_correct
/-- `diagnose` never blames an axiom that holds. -/
theorem diagnose_sound {s : Store} {v : Violation}
    (h : diagnose s = some v) : Broken v s := by
  unfold diagnose at h
  repeat' split at h
  all_goals (cases h <;> simp_all [Broken])

/-- `diagnose` is silent exactly on consistent stores. -/
theorem diagnose_none_iff (s : Store) :
    diagnose s = none ↔ Consistent s := by
  constructor
  · intro h
    unfold diagnose at h
    repeat' split at h
    all_goals simp_all
    exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
  · intro c
    simp [diagnose, c.bornBefore, c.noBilocation,
      c.singleManager, c.uniqueIds]
-- ANCHOR_END: diagnose_correct

-- ANCHOR: insert_error
/-- The reason `insert` reports is true: the named
    axiom fails in the store with `e` added. The
    `.getD .uniqueIds` fallback is never used. -/
theorem insert_error_sound {m : Certified}
    {e : Event} {v : Violation}
    (h : m.insert e = .error v) :
    Broken v (m.store.record e) := by
  simp only [Certified.insert] at h
  split at h
  · cases h
  · rename_i hc
    cases hd : diagnose (m.store.record e) with
    | none =>
      exact absurd ((diagnose_none_iff _).mp hd) hc
    | some w =>
      rw [hd] at h
      cases h
      exact diagnose_sound hd
-- ANCHOR_END: insert_error

end Ch09
