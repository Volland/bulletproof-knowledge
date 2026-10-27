import Knowledge.Ch09.Invariants
import Knowledge.Ch09.Updates
import Knowledge.Ch09.Evolution
import Knowledge.Ch09.Answers

/-!
# Chapter 9: trust hygiene

What the kernel checks, what it cannot check, and the
holes through which an unproven claim can slip in:
`sorry`, extra axioms, `native_decide`, `partial`, and
a wrong specification.
-/

namespace Ch09

open Memory Memory.World Interval

-- ANCHOR: sorry
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem trust_me : Consistent (store.record phantom) :=
  by sorry
-- ANCHOR_END: sorry

-- ANCHOR: print_axioms
/--
info: 'Ch09.trust_me' depends on axioms:
  [propext, sorryAx]
-/
#guard_msgs (whitespace := lax) in
#print axioms trust_me

/--
info: 'Memory.World.store_consistent' depends on
  axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms store_consistent
-- ANCHOR_END: print_axioms

-- ANCHOR: audit
/--
info: 'Ch09.call_not_bilocation' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms call_not_bilocation

/--
info: 'Ch09.shiftAll_consistent' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms shiftAll_consistent

/--
info: 'Ch09.dropSolo_safe' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dropSolo_safe

/--
info: 'Ch09.insert_error_sound' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms insert_error_sound
-- ANCHOR_END: audit

-- ANCHOR: axiom
/-- An axiom is a claim Lean accepts without proof. -/
axiom phantom_fine : Consistent (store.record phantom)

def badMemory : Certified :=
  ⟨store.record phantom, phantom_fine⟩

/--
info: 'Ch09.badMemory' depends on axioms:
  [propext, phantom_fine]
-/
#guard_msgs (whitespace := lax) in
#print axioms badMemory
-- ANCHOR_END: axiom

-- ANCHOR: native
theorem fast : Consistent store := by native_decide

/--
info: 'Ch09.fast' depends on axioms:
  [propext, fast._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms fast
-- ANCHOR_END: native

-- ANCHOR: partial
/-- `partial` lets a function loop forever. -/
partial def chase (n : Nat) : Nat := chase (n + 1)

/--
error: Tactic `unfold` failed to unfold `chase` in
  chase 0 = chase 1
-/
#guard_msgs in
example : chase 0 = chase 1 := by unfold chase
-- ANCHOR_END: partial

-- ANCHOR: wrong_spec
/-- A weaker rule, written in a hurry: a clash only
    when two events have exactly the same span. -/
def NoBilocationSameSlot (s : Store) : Prop :=
  ∀ e₁ ∈ s.events, ∀ e₂ ∈ s.events,
    e₁.kind.physical = true →
    e₂.kind.physical = true →
    e₁.place ≠ e₂.place →
    e₁.span = e₂.span →
    ∀ p ∈ e₁.who, p ∉ e₂.who

instance (s : Store) :
    Decidable (NoBilocationSameSlot s) := by
  unfold NoBilocationSameSlot; infer_instance

/-- The kernel proves the phantom "consistent". -/
theorem phantom_passes :
    NoBilocationSameSlot (store.record phantom) := by
  decide
-- ANCHOR_END: wrong_spec

-- ANCHOR: typo_spec
/-- A typo: `=` where `≠` was meant. -/
def NoBilocationTypo (s : Store) : Prop :=
  ∀ e₁ ∈ s.events, ∀ e₂ ∈ s.events,
    e₁.kind.physical = true →
    e₂.kind.physical = true →
    e₁.place = e₂.place →
    Overlaps e₁.span e₂.span →
    ∀ p ∈ e₁.who, p ∉ e₂.who

instance (s : Store) :
    Decidable (NoBilocationTypo s) := by
  unfold NoBilocationTypo; infer_instance

/-- The true store is now "inconsistent": the kickoff
    clashes with itself. -/
theorem typo_rejects_truth :
    ¬ NoBilocationTypo store := by decide
-- ANCHOR_END: typo_spec

-- ANCHOR: self_report
/-- Merging Marco into Anna: Anna now reports to
    herself, and every axiom is happy. -/
theorem self_report_ok :
    Consistent (merge .anna .marco store) := by
  decide

/--
info: [(Memory.Person.anna, Memory.Person.anna),
  (Memory.Person.taras, Memory.Person.lena)]
-/
#guard_msgs (whitespace := lax) in
#eval (merge .anna .marco store).reportsTo
-- ANCHOR_END: self_report

-- ANCHOR: busy
/-- A daily stand-up call, the `n`-th one. -/
def standup (n : Nat) : Event :=
  { id := 100 + n, kind := .call
    who := [.anna, .lena], place := .kyiv
    span := ⟨day 3000 + 30 * n,
             day 3000 + 30 * n + 15,
             Nat.le_add_right _ _⟩ }

/-- Our store plus `n` stand-ups. -/
def busy (n : Nat) : Store :=
  { store with
    events := (List.range n).map standup
                ++ store.events }
-- ANCHOR_END: busy

-- ANCHOR: too_slow
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic
information
-/
#guard_msgs (whitespace := lax) in
example : NoBilocation (busy 60) := by decide

example : NoBilocation (busy 60) := by decide +kernel
-- ANCHOR_END: too_slow

-- ANCHOR: calls_lemma
/-- Adding any list of calls keeps `NoBilocation`. -/
theorem calls_noBilocation {s : Store}
    (cs : List Event)
    (hc : ∀ e ∈ cs, e.kind = .call)
    (h : NoBilocation s) :
    NoBilocation { s with events := cs ++ s.events } := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    have hc' : ∀ e ∈ cs, e.kind = .call :=
      fun e he => hc e (List.mem_cons_of_mem c he)
    exact call_noBilocation
      (hc c List.mem_cons_self) (ih hc')
-- ANCHOR_END: calls_lemma

-- ANCHOR: busy_all
/-- Every size at once: a theorem, not a computation. -/
theorem busy_noBilocation (n : Nat) :
    NoBilocation (busy n) := by
  apply calls_noBilocation _ _ store_noBilocation
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨k, _, rfl⟩ := he
  rfl
-- ANCHOR_END: busy_all

-- ANCHOR: standups_apart
/-- Consecutive stand-ups never overlap, for every
    `n`. `simp` unfolds, `omega` counts. -/
theorem standups_apart (n : Nat) :
    ¬ Overlaps (standup n).span
               (standup (n + 1)).span := by
  simp only [Overlaps, standup, day]
  unfold Time
  omega
-- ANCHOR_END: standups_apart

end Ch09
