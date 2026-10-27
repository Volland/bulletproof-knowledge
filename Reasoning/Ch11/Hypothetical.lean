import Elpi
import Knowledge.Memory

/-!
# Chapter 11: hypothetical and generic queries

`H => G` runs the goal `G` with the extra clause `H`, and
removes `H` afterwards. `pi x\ G` runs `G` with a fresh
constant `x`. Together they answer "what if" questions
without writing anything into memory.
-/

open Elpi.Cmd

namespace Ch11
open Memory

deriving instance Elpi for Person
deriving instance Elpi for City
deriving instance Elpi for EventKind

-- ANCHOR: facts
elpi_program ch11_hyp
elpi_accumulate ch11_hyp lp%{
  pred reports o:person, o:person.
  reports marco anna.
  reports taras lena.

  % ev Id Kind City Start Stop  (minutes)
  pred ev o:int, o:eventKind, o:city, o:int, o:int.
  ev 1 meeting lisbon 2880600 2880660.
  ev 2 call    kyiv   2880600 2880660.

  pred attended o:int, o:person.
  attended 1 anna. attended 1 marco.
  attended 2 anna. attended 2 taras.

  pred born o:person, o:int.
  born sofia 1440000.
  born P 0 :- not (P = sofia).
}%
-- ANCHOR_END: facts

-- ANCHOR: rules
elpi_accumulate ch11_hyp lp%{
  pred met o:person, o:person.
  met X Y :- attended E X, ev E meeting _ _ _,
             attended E Y, not (X = Y).

  pred above o:person, o:person.
  above X Y :- reports X Y.
  above X Z :- reports X Y, above Y Z.
}%
-- ANCHOR_END: rules

/-! ## Assume, ask, forget -/

-- ANCHOR: assume
/-- info: X = anna -/
#guard_msgs in
#elpi ch11_hyp lp%{ attended 1 lena => met lena X }%
-- ANCHOR_END: assume

-- ANCHOR: forget
/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_hyp lp%{ met lena X }%
-- ANCHOR_END: forget

-- ANCHOR: counterfactual
/-- info: true -/
#guard_msgs in
#elpi ch11_hyp lp%{ reports anna lena => above marco lena }%

/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_hyp lp%{ above marco lena }%
-- ANCHOR_END: counterfactual

-- ANCHOR: collect
elpi_accumulate ch11_hyp lp%{
  % everyone above P, as a list
  pred bosses i:person, o:list person.
  bosses P L :- std.findall (above P _) Sols,
                std.map Sols (s\ y\ s = above _ y) L.
}%

/-- info: L = [anna, lena] -/
#guard_msgs in
#elpi ch11_hyp lp%{ reports anna lena => bosses marco L }%

/-- info: L = [anna] -/
#guard_msgs in
#elpi ch11_hyp lp%{ bosses marco L }%
-- ANCHOR_END: collect

/-! ## Checking a proposal before it is committed -/

-- ANCHOR: violations
elpi_accumulate ch11_hyp lp%{
  pred physical i:eventKind.
  physical meeting. physical talk. physical trip.

  % someone in two cities at overlapping times
  pred bilocated o:person, o:int, o:int.
  bilocated P E1 E2 :-
    attended E1 P, attended E2 P, E1 < E2,
    ev E1 K1 C1 S1 T1, ev E2 K2 C2 S2 T2,
    physical K1, physical K2, not (C1 = C2),
    S1 < T2, S2 < T1.

  % someone at an event before they were born
  pred unborn o:person, o:int.
  unborn P E :- attended E P, ev E _ _ S _,
                born P B, S < B.
}%
-- ANCHOR_END: violations

-- ANCHOR: phantom
/-- info: P = anna, A = 1, B = 3 -/
#guard_msgs in
#elpi ch11_hyp lp%{
  [ ev 3 meeting berlin 2880600 2880720,
    attended 3 anna, attended 3 lena ]
  => bilocated P A B }%
-- ANCHOR_END: phantom

-- ANCHOR: unborn
/-- info: P = sofia, E = 4 -/
#guard_msgs in
#elpi ch11_hyp lp%{
  [ ev 4 talk porto 720000 720060,
    attended 4 sofia ]
  => unborn P E }%
-- ANCHOR_END: unborn

-- ANCHOR: clean
/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_hyp lp%{ bilocated P A B ; unborn P A }%
-- ANCHOR_END: clean

/-! ## Generic reasoning with `pi` -/

-- ANCHOR: generic
/-- info: true -/
#guard_msgs in
#elpi ch11_hyp lp%{
  pi x\ reports x marco => above x anna }%

/-- info: true -/
#guard_msgs in
#elpi ch11_hyp lp%{
  pi x\ attended 1 x => met x anna }%
-- ANCHOR_END: generic

-- ANCHOR: generic_fail
/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_hyp lp%{ pi x\ above x anna }%
-- ANCHOR_END: generic_fail

end Ch11
