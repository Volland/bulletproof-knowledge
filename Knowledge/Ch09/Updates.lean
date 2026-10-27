import Knowledge.Ch09.Invariants

/-!
# Chapter 9: proving updates

An update is a function `Store → Store`. A *safe* update
comes with a theorem: it maps consistent stores to
consistent stores. A safe update needs no run-time check.
An update without such a theorem must go through one.
-/

namespace Ch09

open Memory Memory.World Interval

-- ANCHOR: safe_update
/-- An update together with its preservation proof. -/
structure SafeUpdate where
  run  : Store → Store
  safe : ∀ s, Consistent s → Consistent (run s)

/-- Applying a safe update cannot fail. -/
def SafeUpdate.apply (u : SafeUpdate)
    (m : Certified) : Certified :=
  ⟨u.run m.store, u.safe m.store m.ok⟩
-- ANCHOR_END: safe_update

-- ANCHOR: forget
/-- Forgetting an event is always safe. -/
def forget (i : Nat) : SafeUpdate where
  run s  := removeId s i
  safe _ c := removeId_consistent c i

/-- info: [1] -/
#guard_msgs in
#eval ((forget 2).apply memory).events.map (·.id)
-- ANCHOR_END: forget

-- ANCHOR: later
/-- Move an interval `d` minutes later. -/
def later (d : Nat) (i : Interval) : Interval :=
  ⟨i.start + d, i.stop + d,
   Nat.add_le_add_right i.valid d⟩

/-- Shifting both spans keeps overlap as it was. -/
theorem overlaps_later {d : Nat} {i j : Interval} :
    Overlaps (later d i) (later d j) ↔
      Overlaps i j := by
  simp [Overlaps, later]
-- ANCHOR_END: later

-- ANCHOR: shift
/-- Correct a clock error: every event `d` minutes
    later. -/
def shiftEvent (d : Nat) (e : Event) : Event :=
  { e with span := later d e.span }

def shiftAll (d : Nat) (s : Store) : Store :=
  { s with events := s.events.map (shiftEvent d) }
-- ANCHOR_END: shift

-- ANCHOR: shift_safe
/-- Moving every event `d` minutes later keeps a
    consistent store consistent. -/
theorem shiftAll_consistent (d : Nat) (s : Store)
    (c : Consistent s) :
    Consistent (shiftAll d s) where
  -- proof: one answer per axiom
-- ANCHOR_END: shift_safe
  bornBefore := by
    intro e' he' p hp
    simp only [shiftAll, List.mem_map] at he'
    obtain ⟨e, he, rfl⟩ := he'
    have := c.bornBefore e he p hp
    exact Nat.le_trans this (Nat.le_add_right _ d)
  noBilocation := by
    intro e₁' h₁ e₂' h₂ ph₁ ph₂ hne hov
    simp only [shiftAll, List.mem_map] at h₁ h₂
    obtain ⟨e₁, h₁, rfl⟩ := h₁
    obtain ⟨e₂, h₂, rfl⟩ := h₂
    exact c.noBilocation e₁ h₁ e₂ h₂ ph₁ ph₂ hne
      (overlaps_later.mp hov)
  singleManager := c.singleManager
  uniqueIds := by
    have hid : (·.id) ∘ shiftEvent d = (·.id) := rfl
    simp only [UniqueIds, shiftAll, List.map_map, hid]
    exact c.uniqueIds

-- ANCHOR: shift_safe

def shift (d : Nat) : SafeUpdate :=
  ⟨shiftAll d, shiftAll_consistent d⟩
-- ANCHOR_END: shift_safe

-- ANCHOR: merge
/-- Two names turned out to be one person:
    replace `b` by `a` everywhere. -/
def into (a b : Person) (p : Person) : Person :=
  if p = b then a else p

def merge (a b : Person) (s : Store) : Store :=
  { s with
    worksAt   := s.worksAt.map fun (p, o) =>
                   (into a b p, o)
    reportsTo := s.reportsTo.map fun (p, q) =>
                   (into a b p, into a b q)
    events    := s.events.map fun e =>
                   { e with who := e.who.map (into a b) } }
-- ANCHOR_END: merge

-- ANCHOR: merge_counter
/-- Taras and Marco are one person? Then that person
    reports to Anna *and* to Lena. -/
theorem merge_unsafe :
    ¬ ∀ s, Consistent s →
        Consistent (merge .marco .taras s) := by
  intro h
  have := h store store_consistent
  revert this
  decide
-- ANCHOR_END: merge_counter

-- ANCHOR: merge_partial
/-- Merging never touches event identifiers. -/
theorem merge_uniqueIds (a b : Person) {s : Store}
    (h : UniqueIds s) : UniqueIds (merge a b s) := by
  simp only [UniqueIds, merge, List.map_map]
  exact h

/-- Merging keeps `BornBefore` if the surviving name
    was born no later than the merged one. -/
theorem merge_bornBefore {a b : Person} {s : Store}
    (hab : s.born a ≤ s.born b)
    (h : BornBefore s) :
    BornBefore (merge a b s) := by
  -- proof: each attendee is `into a b q`, old `q`
-- ANCHOR_END: merge_partial
  intro e' he' p hp
  simp only [merge, List.mem_map] at he'
  obtain ⟨e, he, rfl⟩ := he'
  simp only [List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have := h e he q hq
  simp only [merge, into]
  split
  · subst q; exact Nat.le_trans hab this
  · exact this

-- ANCHOR: checked
/-- An update without a proof goes through the same
    check as `insert`. -/
def update (m : Certified)
    (f : Store → Store) :
    Except Violation Certified :=
  let s := f m.store
  if h : Consistent s then .ok ⟨s, h⟩
  else .error ((diagnose s).getD .uniqueIds)

/-- info: Except.error (Memory.Violation.singleManager) -/
#guard_msgs in
#eval (update memory (merge .marco .taras)).map
  (·.events.length)
-- ANCHOR_END: checked

end Ch09
