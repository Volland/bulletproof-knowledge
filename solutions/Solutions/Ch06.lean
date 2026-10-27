import Knowledge.Memory

/-!
# Solutions to the Chapter 6 exercises

Each solution is self-contained: it imports only the shared
`Knowledge.Memory` library.
-/

namespace Solutions.Ch06

open Memory Memory.World

/-! ## Exercise 6.1 — Who was where -/

/-- Identifiers of the events `p` took part in. -/
def attendedIds (s : Store) (p : Person) : List Nat :=
  (s.events.filter (·.who.contains p)).map (·.id)

/-- info: [2, 1] -/
#guard_msgs in
#eval attendedIds store .anna

/-- info: [] -/
#guard_msgs in
#eval attendedIds store .lena

/-! ## Exercise 6.2 — An interval that cannot fail -/

/-- An interval of `len` minutes starting at `start`.
    No `decide` needed: the proof works for all numbers. -/
def ofLength (start len : Time) : Interval :=
  ⟨start, start + len, Nat.le_add_right start len⟩

/-- info: 645 -/
#guard_msgs in
#eval (ofLength 600 45).stop

/-! ## Exercise 6.3 — A decidable class of events -/

/-- An event that needs no physical presence. -/
def Remote (e : Event) : Prop :=
  e.kind.physical = false

instance (e : Event) : Decidable (Remote e) :=
  inferInstanceAs (Decidable (e.kind.physical = false))

theorem review_remote : Remote review := by
  decide

theorem kickoff_not_remote : ¬ Remote kickoff := by
  decide

/-! ## Exercise 6.4 — Back-to-back meetings do not clash -/

/-- If `i` ends no later than `j` starts, the two spans
    do not overlap (spans are half-open, `[start, stop)`). -/
theorem back_to_back (i j : Interval)
    (h : i.stop ≤ j.start) : ¬ Interval.Overlaps i j := by
  intro ho
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ho.2 h)

/-- The same with `omega`, after unfolding `Overlaps`
    and the abbreviation `Time`. -/
theorem back_to_back' (i j : Interval)
    (h : i.stop ≤ j.start) : ¬ Interval.Overlaps i j := by
  simp only [Interval.Overlaps, Time] at *
  omega

/-! ## Exercise 6.5 — Induction over memories -/

def ids : List Event → List Nat
  | []      => []
  | e :: es => e.id :: ids es

theorem ids_append (xs ys : List Event) :
    ids (xs ++ ys) = ids xs ++ ids ys := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp [ids, ih]

end Solutions.Ch06
