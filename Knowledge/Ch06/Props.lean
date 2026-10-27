import Knowledge.Memory

/-!
# Chapter 6 — Propositions and proofs

Statements about the agent's memory as types, and proofs as
ordinary terms of those types.
-/

namespace Ch06

open Memory Memory.World

-- ANCHOR: universe
/-- info: Nat : Type -/
#guard_msgs in
#check Nat

/-- info: Type : Type 1 -/
#guard_msgs in
#check Type

/-- info: kickoff.span.start ≤ kickoff.span.stop : Prop -/
#guard_msgs in
#check kickoff.span.start ≤ kickoff.span.stop

/-- info: Prop : Type -/
#guard_msgs in
#check Prop
-- ANCHOR_END: universe

-- ANCHOR: valid
/--
info: kickoff.span.valid :
  kickoff.span.start ≤ kickoff.span.stop
-/
#guard_msgs (whitespace := lax) in
#check kickoff.span.valid
-- ANCHOR_END: valid

-- ANCHOR: first-theorem
/-- The kickoff does not end before it starts.
    The proof is the interval's own `valid` field. -/
theorem kickoff_ordered :
    kickoff.span.start ≤ kickoff.span.stop :=
  kickoff.span.valid
-- ANCHOR_END: first-theorem

-- ANCHOR: attended
/-- `p` took part in `e`: a proposition, not a Boolean. -/
def Attended (e : Event) (p : Person) : Prop :=
  p ∈ e.who

/-- info: Attended kickoff Person.marco : Prop -/
#guard_msgs in
#check Attended kickoff .marco

/-- info: kickoff.who.contains Person.marco : Bool -/
#guard_msgs in
#check kickoff.who.contains .marco
-- ANCHOR_END: attended

-- ANCHOR: mem
/-- Anna is the head of the attendee list. -/
theorem anna_at_kickoff : Attended kickoff .anna :=
  List.Mem.head _

/-- Marco is in the tail of the list. -/
theorem marco_at_kickoff : Attended kickoff .marco :=
  List.Mem.tail _ (List.Mem.head _)
-- ANCHOR_END: mem

-- ANCHOR: and
theorem both_at_kickoff :
    Attended kickoff .anna ∧ Attended kickoff .marco :=
  ⟨anna_at_kickoff, marco_at_kickoff⟩

/-- Taking a conjunction apart: `.1` and `.2`. -/
theorem marco_again : Attended kickoff .marco :=
  both_at_kickoff.2
-- ANCHOR_END: and

-- ANCHOR: or
/-- True, because the left side is true. The right
    side (the hallucinated Berlin meeting) is not
    examined at all. -/
theorem anna_somewhere :
    Attended kickoff .anna ∨ Attended phantom .anna :=
  Or.inl anna_at_kickoff
-- ANCHOR_END: or

-- ANCHOR: forall
/-- For every interval, it is not the case that it
    ends before it starts. -/
theorem never_backwards :
    ∀ i : Interval, ¬ i.stop < i.start :=
  fun i => Nat.not_lt.mpr i.valid
-- ANCHOR_END: forall

-- ANCHOR: not
/-- `¬ P` is, by definition, `P → False`. -/
theorem not_is_imp (P : Prop) : (¬ P) = (P → False) :=
  rfl
-- ANCHOR_END: not

-- ANCHOR: exists
/-- Someone attended a call: here is the call,
    here is the evidence. -/
theorem taras_on_a_call :
    ∃ e ∈ store.events,
      Attended e .taras ∧ e.kind = .call :=
  ⟨review, List.Mem.head _,
    List.Mem.tail _ (List.Mem.head _), rfl⟩
-- ANCHOR_END: exists

-- ANCHOR: bad-proof
/--
error: Type mismatch
  List.Mem.head ?m.3
has type
  List.Mem ?m.2 (?m.2 :: ?m.3)
but is expected to have type
  Attended kickoff Person.lena
-/
#guard_msgs in
theorem lena_at_kickoff : Attended kickoff .lena :=
  List.Mem.head _
-- ANCHOR_END: bad-proof

end Ch06
