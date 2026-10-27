import Elpi
import Knowledge.Memory

/-!
# Chapter 2: first rules in λProlog

Small ELPI programs over the agent's memory, run through
lean-elpi. Chapter 10 explains the machinery; here we only
look at what facts, rules and queries do.
-/

open Elpi.Cmd

namespace Ch02

-- ANCHOR: facts
elpi_program team
elpi_accumulate team lp%{
  kind person type.
  type anna, marco, lena, taras, sofia person.
  kind event type.
  type kickoff, review event.

  pred reports o:person, o:person.
  reports marco anna.
  reports taras lena.

  pred attended o:event, o:person.
  attended kickoff anna.
  attended kickoff marco.
  attended review anna.
  attended review taras.
}%
-- ANCHOR_END: facts

-- ANCHOR: sync
open Memory.World in
example :
    store.reportsTo = [(.marco, .anna), (.taras, .lena)] ∧
    kickoff.who = [.anna, .marco] ∧
    review.who = [.anna, .taras] :=
  ⟨rfl, rfl, rfl⟩
-- ANCHOR_END: sync

-- ANCHOR: query
/-- info: X = marco -/
#guard_msgs in
#elpi team lp%{ reports X anna }%
-- ANCHOR_END: query

-- ANCHOR: many
/--
info: X = anna
---
info: X = marco
-/
#guard_msgs in
set_option elpi.solutions 5 in
#elpi team lp%{ attended kickoff X }%
-- ANCHOR_END: many

-- ANCHOR: no
/-- error: query has no solution -/
#guard_msgs in
#elpi team lp%{ reports taras anna }%
-- ANCHOR_END: no

-- ANCHOR: typed
/--
error: kickoff has type event but is used with type person
-/
#guard_msgs in
#elpi team lp%{ reports kickoff anna }%
-- ANCHOR_END: typed

-- ANCHOR: capital
/-- info: Anna = taras -/
#guard_msgs in
#elpi team lp%{ reports Anna lena }%
-- ANCHOR_END: capital

-- ANCHOR: rules
elpi_accumulate team lp%{
  pred team_at i:person, i:event.
  team_at M E :- not (reports P M, not (attended E P)).
}%
-- ANCHOR_END: rules

-- ANCHOR: team_at
/-- info: true -/
#guard_msgs in
#elpi team lp%{ team_at anna kickoff }%

/-- error: query has no solution -/
#guard_msgs in
#elpi team lp%{ team_at anna review }%
-- ANCHOR_END: team_at

-- ANCHOR: closure
elpi_accumulate team lp%{
  pred closure i:(A -> A -> prop), o:A, o:A.
  closure R X Y :- R X Y.
  closure R X Z :- R X Y, closure R Y Z.
}%
-- ANCHOR_END: closure

-- ANCHOR: chain_query
/-- info: X = anna -/
#guard_msgs in
set_option elpi.solutions 5 in
#elpi team lp%{ closure reports marco X }%
-- ANCHOR_END: chain_query

-- ANCHOR: assume
/--
info: X = anna
---
info: X = sofia
-/
#guard_msgs in
set_option elpi.solutions 5 in
#elpi team lp%{
  reports anna sofia => closure reports marco X }%

/-- error: query has no solution -/
#guard_msgs in
#elpi team lp%{ closure reports marco sofia }%
-- ANCHOR_END: assume

-- ANCHOR: pi
/-- info: true -/
#guard_msgs in
#elpi team lp%{
  pi p\ reports p anna => closure reports p anna }%
-- ANCHOR_END: pi

end Ch02
