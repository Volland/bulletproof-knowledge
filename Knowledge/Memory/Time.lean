/-!
# Time

Time is a natural number: minutes since the agent's epoch.
An interval carries a *proof* that it does not end before
it starts, so an ill-formed interval cannot be written.
-/

namespace Memory

/-- Minutes since the agent's epoch. -/
abbrev Time := Nat

-- ANCHOR: interval
/-- A time span `[start, stop)`. The field `valid` is a
    proof: no `Interval` ends before it starts. -/
structure Interval where
  start : Time
  stop  : Time
  valid : start ≤ stop
  deriving DecidableEq, Repr
-- ANCHOR_END: interval

namespace Interval

-- ANCHOR: overlaps
/-- Two spans overlap when each starts before
    the other ends. -/
def Overlaps (i j : Interval) : Prop :=
  i.start < j.stop ∧ j.start < i.stop

instance (i j : Interval) : Decidable (Overlaps i j) :=
  inferInstanceAs (Decidable (_ ∧ _))
-- ANCHOR_END: overlaps

-- ANCHOR: mk
/-- Build an interval from concrete numbers;
    `decide` supplies the proof of `start ≤ stop`. -/
def mk! (start stop : Time)
    (h : start ≤ stop := by decide) : Interval :=
  ⟨start, stop, h⟩
-- ANCHOR_END: mk

-- ANCHOR: overlaps_symm
theorem overlaps_symm {i j : Interval} :
    Overlaps i j → Overlaps j i :=
  fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩
-- ANCHOR_END: overlaps_symm

end Interval

end Memory
