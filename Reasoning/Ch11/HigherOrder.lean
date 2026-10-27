import Elpi
import Knowledge.Memory

/-!
# Chapter 11: higher-order logic programming

Predicates as arguments, rules about rules, properties of
relations checked generically, and λ-terms (HOAS) for
structured descriptions of memories.
-/

open Elpi.Cmd

namespace Ch11
open Memory

-- ANCHOR: derive
deriving instance Elpi for Person
deriving instance Elpi for City
deriving instance Elpi for EventKind
deriving instance Elpi for Org
-- ANCHOR_END: derive

/-! ## The facts, mirrored from `Memory.World` -/

-- ANCHOR: facts
elpi_program ch11_ho
elpi_accumulate ch11_ho lp%{
  pred reports o:person, o:person.
  reports marco anna.
  reports taras lena.

  pred works-at o:person, o:org.
  works-at anna acme.   works-at marco acme.
  works-at taras kyivTech. works-at lena lumen.

  % events: 1 = kickoff, 2 = review
  pred attended o:int, o:person.
  attended 1 anna. attended 1 marco.
  attended 2 anna. attended 2 taras.

  pred kind-of o:int, o:eventKind.
  kind-of 1 meeting. kind-of 2 call.
}%
-- ANCHOR_END: facts

-- ANCHOR: relations
elpi_accumulate ch11_ho lp%{
  % met in person: same event, a physical meeting
  pred met o:person, o:person.
  met X Y :- attended E X, kind-of E meeting,
             attended E Y, not (X = Y).

  % spoke on a call
  pred spoke o:person, o:person.
  spoke X Y :- attended E X, kind-of E call,
               attended E Y, not (X = Y).

  % in contact: either of the two
  pred contact o:person, o:person.
  contact X Y :- met X Y.
  contact X Y :- spoke X Y.
}%
-- ANCHOR_END: relations

/-! ## Predicates as arguments -/

-- ANCHOR: closure
elpi_accumulate ch11_ho lp%{
  % one closure rule for every relation R
  pred closure i:(A -> A -> prop), o:A, o:A.
  closure R X Y :- R X Y.
  closure R X Z :- R X Y, closure R Y Z.
}%
-- ANCHOR_END: closure

-- ANCHOR: closure_query
/-- info: Y = anna -/
#guard_msgs in
#elpi ch11_ho lp%{ closure reports marco Y }%
-- ANCHOR_END: closure_query

-- ANCHOR: compose
elpi_accumulate ch11_ho lp%{
  % relational composition: R then S
  pred compose i:(A -> B -> prop), i:(B -> C -> prop),
               o:A, o:C.
  compose R S X Z :- R X Y, S Y Z.
}%

/-- info: O = acme -/
#guard_msgs in
#elpi ch11_ho lp%{ compose reports works-at marco O }%
-- ANCHOR_END: compose

/--
error: reports has type person -> person -> prop but is used with type org -> person -> prop
-/
#guard_msgs in
-- ANCHOR: compose_bad
#elpi ch11_ho lp%{ compose works-at reports marco O }%
-- ANCHOR_END: compose_bad

-- ANCHOR: filter
/-- info: L = [anna, marco] -/
#guard_msgs in
#elpi ch11_ho lp%{
  std.filter [anna, marco, lena, taras, sofia]
    (p\ works-at p acme) L }%
-- ANCHOR_END: filter

/-! ## Rules about rules -/

-- ANCHOR: properties
elpi_accumulate ch11_ho lp%{
  % properties of relations, stated as facts
  pred transitive o:(person -> person -> prop).
  pred symmetric  o:(person -> person -> prop).
  transitive under.
  symmetric met. symmetric spoke. symmetric contact.

  pred under o:person, o:person.
  under X Y :- closure reports X Y.

  % one generic rule that uses them
  pred holds i:(person -> person -> prop),
             o:person, o:person.
  holds R X Y :- R X Y.
  holds R X Y :- symmetric R, R Y X.
  holds R X Z :- transitive R, R X Y, holds R Y Z.
}%
-- ANCHOR_END: properties

-- ANCHOR: holds_query
/-- info: X = anna -/
#guard_msgs in
#elpi ch11_ho lp%{ holds met X marco }%

/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_ho lp%{ holds contact marco taras }%
-- ANCHOR_END: holds_query

-- ANCHOR: check_property
elpi_accumulate ch11_ho lp%{
  % a counterexample to "R is transitive"
  pred not-transitive i:(person -> person -> prop),
                      o:person, o:person, o:person.
  not-transitive R X Y Z :-
    R X Y, R Y Z, not (X = Z), not (R X Z).
}%

/-- info: X = marco, Y = anna, Z = taras -/
#guard_msgs in
#elpi ch11_ho lp%{ not-transitive contact X Y Z }%

/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_ho lp%{ not-transitive under X Y Z }%
-- ANCHOR_END: check_property

/-! ## λ-terms: binders as data -/

-- ANCHOR: beta
/-- info: F = c0 \ works-at c0 acme, R = works-at marco acme -/
#guard_msgs in
#elpi ch11_ho lp%{
  F = (x\ works-at x acme), R = F marco }%
-- ANCHOR_END: beta

-- ANCHOR: pattern
/-- info: F = c0 \ works-at c0 acme -/
#guard_msgs in
#elpi ch11_ho lp%{ pi x\ F x = works-at x acme }%

/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_ho lp%{ pi x\ Y = works-at x acme }%
-- ANCHOR_END: pattern

-- ANCHOR: suspended
/-- info: F = X0
 X0 marco = works-at marco acme  /* suspended on X0 */ -/
#guard_msgs in
#elpi ch11_ho lp%{ F marco = works-at marco acme }%
-- ANCHOR_END: suspended

/-! ## HOAS: descriptions with bound participants -/

-- ANCHOR: desc
elpi_accumulate ch11_ho lp%{
  kind desc type.
  type attends  person -> int -> desc.
  type employed person -> org -> desc.
  type reports-to person -> person -> desc.
  type both     desc -> desc -> desc.
  type implies  desc -> desc -> desc.
  type someone  (person -> desc) -> desc.
  type everyone (person -> desc) -> desc.
}%
-- ANCHOR_END: desc

-- ANCHOR: sat
elpi_accumulate ch11_ho lp%{
  pred person o:person.
  person anna. person marco. person lena.
  person taras. person sofia.

  % is a description true in the memory?
  pred sat i:desc.
  sat (attends P E)    :- attended E P.
  sat (employed P O)   :- works-at P O.
  sat (reports-to P Q) :- reports P Q.
  sat (both A B)       :- sat A, sat B.
  sat (implies A B)    :- not (sat A) ; sat B.
  sat (someone F)      :- person X, sat (F X).
  sat (everyone F)     :- not (person X, not (sat (F X))).

  % which person makes the body true?
  pred witness i:desc, o:person.
  witness (someone F) X :- person X, sat (F X).
}%
-- ANCHOR_END: sat

-- ANCHOR: sat_query
/-- info: X = marco -/
#guard_msgs in
#elpi ch11_ho lp%{
  witness (someone x\ both (employed x acme)
                           (reports-to x anna)) X }%

/-- info: true -/
#guard_msgs in
#elpi ch11_ho lp%{
  sat (everyone x\ implies (reports-to x anna)
                           (attends x 1)) }%

/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_ho lp%{
  sat (everyone x\ implies (employed x acme)
                           (attends x 2)) }%
-- ANCHOR_END: sat_query

end Ch11
