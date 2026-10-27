import Elpi

/-!
# Chapter 10: λProlog in twenty minutes

A pure ELPI program, written by hand. It mirrors a corner of
the agent's memory, but it does not touch `Knowledge.Memory`:
the people and organizations are declared a second time, in
ELPI. `Bridge.lean` removes that duplication.
-/

open Elpi.Cmd

namespace Ch10.Basics

-- ANCHOR: office
elpi_program office
elpi_accumulate office lp%{
  kind person type.
  type anna, marco, lena, taras, sofia person.

  kind org type.
  type acme, lumen, kyivTech org.

  pred works-at o:person, o:org.
  works-at anna acme.
  works-at marco acme.
  works-at taras kyivTech.
  works-at lena lumen.

  pred reports-to o:person, o:person.
  reports-to marco anna.
  reports-to taras lena.
  reports-to sofia marco.
}%
-- ANCHOR_END: office

-- ANCHOR: first-query
/-- info: O = acme -/
#guard_msgs in
#elpi office lp%{ works-at marco O }%
-- ANCHOR_END: first-query

-- ANCHOR: two-answers
set_option elpi.solutions 5 in
/-- info: P = anna
---
info: P = marco -/
#guard_msgs in
#elpi office lp%{ works-at P acme }%
-- ANCHOR_END: two-answers

-- ANCHOR: yes-no
/-- info: true -/
#guard_msgs in
#elpi office lp%{ works-at anna acme }%

/-- error: query has no solution -/
#guard_msgs in
#elpi office lp%{ works-at lena acme }%
-- ANCHOR_END: yes-no

-- ANCHOR: typed
/-- error: acme has type org but is used with type person
---
error: anna has type person but is used with type org -/
#guard_msgs in
elpi_accumulate office lp%{
  works-at acme anna.
}%
-- ANCHOR_END: typed

-- ANCHOR: undeclared
/-- error: undeclared constant 'lisbon' -/
#guard_msgs in
#elpi office lp%{ works-at anna lisbon }%
-- ANCHOR_END: undeclared

-- ANCHOR: unify
/-- info: X = anna, Y = lena -/
#guard_msgs in
#elpi office lp%{ pr X lena = pr anna Y }%

/-- error: query has no solution -/
#guard_msgs in
#elpi office lp%{ pr X lena = pr anna marco }%
-- ANCHOR_END: unify

-- ANCHOR: rules
elpi_accumulate office lp%{
  pred colleague o:person, o:person.
  colleague A B :-
    works-at A O, works-at B O, not (A = B).

  pred manages o:person, o:person.
  manages M P :- reports-to P M.
  manages M P :- reports-to P X, manages M X.
}%
-- ANCHOR_END: rules

-- ANCHOR: colleague-query
set_option elpi.solutions 10 in
/-- info: A = anna, B = marco
---
info: A = marco, B = anna -/
#guard_msgs in
#elpi office lp%{ colleague A B }%
-- ANCHOR_END: colleague-query

-- ANCHOR: chain-query
set_option elpi.solutions 10 in
/-- info: M = marco
---
info: M = anna -/
#guard_msgs in
#elpi office lp%{ manages M sofia }%
-- ANCHOR_END: chain-query

-- ANCHOR: modes
elpi_accumulate office lp%{
  pred boss-of i:person, o:person.
  boss-of marco anna.
  boss-of taras lena.
  boss-of sofia marco.
}%

/-- info: M = anna -/
#guard_msgs in
#elpi office lp%{ boss-of marco M }%

/-- error: query has no solution -/
#guard_msgs in
#elpi office lp%{ boss-of P anna }%
-- ANCHOR_END: modes

-- ANCHOR: lists
/-- info: P = marco -/
#guard_msgs in
#elpi office lp%{
  std.mem [anna, marco] P, not (P = anna)
}%

/-- info: L = [anna, marco, lena] -/
#guard_msgs in
#elpi office lp%{ std.append [anna, marco] [lena] L }%
-- ANCHOR_END: lists

-- ANCHOR: findall
/-- info: L = [manages marco sofia,
  manages anna sofia], N = 2 -/
#guard_msgs (whitespace := lax) in
#elpi office lp%{
  std.findall (manages _ sofia) L, std.length L N
}%
-- ANCHOR_END: findall

-- ANCHOR: cut
elpi_accumulate office lp%{
  pred first-boss i:person, o:person.
  first-boss P M :- manages M P, !.
}%

set_option elpi.solutions 10 in
/-- info: M = marco -/
#guard_msgs in
#elpi office lp%{ first-boss sofia M }%
-- ANCHOR_END: cut

-- ANCHOR: arith
/-- info: N = 1440 -/
#guard_msgs in
#elpi office lp%{ N is 24 * 60 }%
-- ANCHOR_END: arith

end Ch10.Basics
