import Reasoning.Ch10.Bridge

/-!
# Chapter 10: rules over the agent's memory

The facts come from the Lean store through `memdb`
(`Bridge.lean`). This module adds rules: colleagues,
management chains, co-attendance, presence in a country,
and a bilocation check with typed verdicts.
-/

open Elpi.Cmd
open Memory

namespace Ch10

-- ANCHOR: lean-version
/-- "Who manages Anna's colleagues?" as a Lean function:
    one direction, one question, written by hand. -/
def colleaguesManagers (s : Store) (p : Person) :
    List Person :=
  let orgs := s.worksAt.filterMap fun (q, o) =>
    if q = p then some o else none
  let cols := s.worksAt.filterMap fun (q, o) =>
    if o ∈ orgs ∧ q ≠ p then some q else none
  s.reportsTo.filterMap fun (q, m) =>
    if q ∈ cols then some m else none

/-- info: [Memory.Person.anna, Memory.Person.marco] -/
#guard_msgs in
#eval colleaguesManagers store .anna
-- ANCHOR_END: lean-version

-- ANCHOR: program
elpi_program rules
elpi_accumulate rules db memdb
-- ANCHOR_END: program

-- ANCHOR: colleague
elpi_accumulate rules lp%{
  pred colleague o:person, o:person.
  colleague A B :-
    works-at A O, works-at B O, not (A = B).
}%

set_option elpi.solutions 10 in
/-- info: C = marco, M = anna
---
info: C = sofia, M = marco -/
#guard_msgs in
#elpi rules lp%{ colleague anna C, reports-to C M }%
-- ANCHOR_END: colleague

-- ANCHOR: manages
elpi_accumulate rules lp%{
  pred manages o:person, o:person.
  manages M P :- reports-to P M.
  manages M P :- reports-to P X, manages M X.
}%

set_option elpi.solutions 10 in
/-- info: M = marco
---
info: M = anna -/
#guard_msgs in
#elpi rules lp%{ manages M sofia }%

set_option elpi.solutions 10 in
/-- info: P = marco
---
info: P = sofia -/
#guard_msgs in
#elpi rules lp%{ manages anna P }%
-- ANCHOR_END: manages

-- ANCHOR: hook
set_option elpi.solutions 10 in
/-- info: C = marco, M = anna
---
info: C = sofia, M = marco
---
info: C = sofia, M = anna -/
#guard_msgs in
#elpi rules lp%{ colleague anna C, manages M C }%
-- ANCHOR_END: hook

-- ANCHOR: met
elpi_accumulate rules lp%{
  pred met o:person, o:person.
  met A B :-
    attended E A, attended E B, not (A = B).
}%

set_option elpi.solutions 10 in
/-- info: P = lena
---
info: P = sofia
---
info: P = anna -/
#guard_msgs in
#elpi rules lp%{ met marco P }%
-- ANCHOR_END: met

-- ANCHOR: was-in
elpi_accumulate rules lp%{
  pred was-in o:person, o:country.
  was-in P Country :-
    event E Kind City _ _,
    mem.physical Kind tt,
    mem.country City Country,
    attended E P.
}%

set_option elpi.solutions 10 in
/-- info: P = lena
---
info: P = marco
---
info: P = sofia
---
info: P = anna
---
info: P = marco -/
#guard_msgs in
#elpi rules lp%{ was-in P portugal }%
-- ANCHOR_END: was-in

-- ANCHOR: visited
elpi_accumulate rules lp%{
  pred was-in! i:person, i:country.
  was-in! P C :- was-in P C, !.

  pred visited o:person, o:country.
  visited P C :- person P, country C, was-in! P C.
}%

set_option elpi.solutions 10 in
/-- info: P = anna
---
info: P = marco
---
info: P = lena
---
info: P = sofia -/
#guard_msgs in
#elpi rules lp%{ visited P portugal }%
-- ANCHOR_END: visited

-- ANCHOR: naf
set_option elpi.solutions 10 in
/-- info: P = taras -/
#guard_msgs in
#elpi rules lp%{ person P, not (was-in P portugal) }%
-- ANCHOR_END: naf

-- ANCHOR: naf-trap
/-- error: query has no solution -/
#guard_msgs in
#elpi rules lp%{ not (was-in P portugal), person P }%
-- ANCHOR_END: naf-trap

-- ANCHOR: reach
elpi_accumulate rules lp%{
  % met is symmetric: walking it naively can go
  % back and forth forever. Seen is the visited list.
  pred reach i:list person, i:person, o:person.
  reach Seen A B :- met A B, not (std.mem Seen B).
  reach Seen A C :-
    met A B, not (std.mem Seen B),
    reach [B|Seen] B C.

  pred linked i:person, i:person.
  linked A B :- reach [A] A B, !.
}%

set_option elpi.solutions 10 in
/-- info: P = anna
---
info: P = marco
---
info: P = lena
---
info: P = sofia -/
#guard_msgs in
#elpi rules lp%{
  person P, not (P = taras), linked taras P
}%
-- ANCHOR_END: reach

-- ANCHOR: conflict
elpi_accumulate rules lp%{
  % A proposed event clashes with a remembered one when
  % someone would be in two cities at overlapping times.
  pred clash i:eventRow, o:person, o:int.
  clash (eventRow.mk _ K Who C S E) P Id :-
    mem.physical K tt,
    std.mem Who P,
    attended Id P,
    event Id K2 C2 S2 E2,
    mem.physical K2 tt,
    not (C = C2),
    S < E2, S2 < E.
}%
-- ANCHOR_END: conflict

end Ch10

-- ANCHOR: candidates
namespace Ch10
/-- Events an LLM proposed: Chapter 1's phantom meeting. -/
def proposed : List EventRow :=
  [EventRow.of World.phantom]
end Ch10

elpi_extern many Ch10.proposed as "mem.proposed"
-- ANCHOR_END: candidates

namespace Ch10

-- ANCHOR: clash-query
elpi_accumulate rules lp%{
  pred suspicious o:person, o:int.
  suspicious P Id :- mem.proposed Ev, clash Ev P Id.
}%

set_option elpi.solutions 10 in
/-- info: P = anna, Id = 1 -/
#guard_msgs in
#elpi rules lp%{ suspicious P Id }%
-- ANCHOR_END: clash-query

-- Sanity check: no remembered event, proposed again,
-- clashes with the certified store.
/-- error: query has no solution -/
#guard_msgs in
#elpi rules lp%{ attended Id P, event Id K C S E,
                 clash (eventRow.mk 0 K [P] C S E) Q I }%

-- ANCHOR: verdict-data
elpi_data lp%{
  kind verdict type.
  type accept verdict.
  type reject int -> verdict.
}%
-- ANCHOR_END: verdict-data

-- ANCHOR: verdict
elpi_accumulate rules lp%{
  pred verdict-of i:eventRow, o:verdict.
  verdict-of Ev (reject Id) :- clash Ev _ Id, !.
  verdict-of _ accept.
}%
-- ANCHOR_END: verdict

elpi_accumulate rules lp%{
  % Re-judge every remembered event as if it were new.
  pred rejudge o:int, o:verdict.
  rejudge Id V :-
    mem.event E, E = eventRow.mk Id _ _ _ _ _,
    verdict-of E V.
}%

set_option elpi.solutions 10 in
/-- info: Id = 4, V = accept
---
info: Id = 3, V = accept
---
info: Id = 2, V = accept
---
info: Id = 1, V = accept -/
#guard_msgs in
#elpi rules lp%{ rejudge Id V }%

end Ch10
