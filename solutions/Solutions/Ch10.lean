import Elpi
import Knowledge.Memory
import Reasoning.Ch10.Query

/-!
# Solutions to the Chapter 10 exercises

They reuse the chapter's bridge (`memdb`) and rule program
(`rules`) from `Reasoning/Ch10`.
-/

open Lean Meta
open Elpi.Cmd
open Memory
open Ch10 (store EventRow pairs)

namespace Solutions.Ch10

/-! ## Exercise 10.1: skip-level managers -/

elpi_program sol
elpi_accumulate sol db memdb
elpi_accumulate sol lp%{
  pred skip-level o:person, o:person.
  skip-level G P :- reports-to P M, reports-to M G.
}%

set_option elpi.solutions 10 in
/-- info: G = anna, P = sofia -/
#guard_msgs in
#elpi sol lp%{ skip-level G P }%

/-! ## Exercise 10.2: where was someone at a given time? -/

elpi_accumulate sol lp%{
  pred located o:person, o:city, i:int.
  located P C T :-
    event E K C S F, mem.physical K tt,
    S =< T, T < F,
    attended E P.
}%

-- day 2001, 14:30 is 2001 * 1440 + 870 minutes.
set_option elpi.solutions 10 in
/-- info: T = 2882310, C = porto -/
#guard_msgs in
#elpi sol lp%{ T is 2001 * 1440 + 870, located marco C T }%

/-- error: query has no solution -/
#guard_msgs in
#elpi sol lp%{ T is 2002 * 1440 + 60, located marco C T }%

end Solutions.Ch10

/-! ## Exercise 10.3: a Lean function as a predicate -/

namespace Solutions.Ch10
/-- Length of an event in minutes. -/
def durationOf (r : EventRow) : Nat :=
  r.stop - r.start
end Solutions.Ch10

elpi_extern Solutions.Ch10.durationOf as "duration"

namespace Solutions.Ch10

elpi_accumulate sol lp%{
  pred long-event o:int.
  long-event Id :-
    mem.event R, R = eventRow.mk Id _ _ _ _ _,
    duration R D, D > 120.
}%

set_option elpi.solutions 10 in
/-- info: Id = 4 -/
#guard_msgs in
#elpi sol lp%{ long-event Id }%

/-! ## Exercise 10.4: found by ELPI, checked by Lean -/

def Colleague (s : Store) (a b : Person) : Prop :=
  a ≠ b ∧
  ∃ x ∈ s.worksAt, x.1 = a ∧ (b, x.2) ∈ s.worksAt

instance (s : Store) (a b : Person) :
    Decidable (Colleague s a b) := by
  unfold Colleague; infer_instance

def colleaguesChecked (p : Person) : MetaM (List Person) := do
  let found ← pairs (α := Person) (β := Person)
    "colleague A B" "A" "B"
  let mine := found.filterMap fun (a, b) =>
    if a = p then some b else none
  for q in mine do
    unless decide (Colleague store p q) do
      throwError "unjustified answer: {repr q}"
  return mine

/-- info: [Memory.Person.marco, Memory.Person.sofia] -/
#guard_msgs in
#eval colleaguesChecked .anna

example : Colleague store .anna .sofia := by decide
example : ¬ Colleague store .anna .lena := by decide

/-! ## Exercise 10.5: irreflexive `before` -/

elpi_accumulate sol lp%{
  constraint earlier {
    rule (earlier X X) <=> fail.
    rule (earlier X Y) (earlier Y X) <=> fail.
    rule (earlier X Y) (earlier Y Z) <=> (earlier X Z).
  }
  pred earlier o:int, o:int.
  earlier A B :- var A, !,
    declare_constraint (earlier A B) [A].
  earlier A B :- var B, !,
    declare_constraint (earlier A B) [B].
  earlier A B :- A < B.
}%

/-- error: query has no solution -/
#guard_msgs in
#elpi sol lp%{ earlier K K }%

/-- error: query has no solution -/
#guard_msgs in
#elpi sol lp%{ earlier K R, earlier R K }%

end Solutions.Ch10
