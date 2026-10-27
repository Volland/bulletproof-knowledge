import Elpi
import Knowledge.Memory

/-!
# Chapter 11: reasoning over the metagraph

Statements are terms, so a statement can be the argument
of another statement (a metaedge). Belief is computed
with a provenance chain, under a trust policy that is
itself a predicate passed as an argument.
-/

open Elpi.Cmd

namespace Ch11
open Memory

deriving instance Elpi for Person
deriving instance Elpi for City

-- ANCHOR: stmt
elpi_program ch11_meta
elpi_accumulate ch11_meta lp%{
  kind stmt type.
  % edges between atoms
  type present  person -> city -> stmt.
  type agreed   person -> person -> stmt.
  type approved person -> string -> stmt.
  % metaedges: their arguments are edges
  type during   stmt -> int -> stmt.
  type said     person -> stmt -> stmt.
}%
-- ANCHOR_END: stmt

-- ANCHOR: memory
elpi_accumulate ch11_meta lp%{
  % what the agent itself recorded
  pred asserted o:stmt.
  asserted (during (agreed anna marco) 1).
  asserted (said marco
             (during (approved anna "budget") 1)).
  asserted (said lena
             (during (approved taras "hiring") 1)).

  % the inner subgraph of event metavertex 1
  pred inside o:int, o:stmt.
  inside 1 (present anna lisbon).
  inside 1 (present marco lisbon).

  pred attended o:int, o:person.
  attended 1 anna. attended 1 marco.
}%
-- ANCHOR_END: memory

-- ANCHOR: prov
elpi_accumulate ch11_meta lp%{
  % how a belief was obtained
  kind prov type.
  type stated  prov.                  % recorded by us
  type within  int -> prov.           % inside event E
  type context int -> prov -> prov.   % held during E
  type claimed person -> prov -> prov. % P said so
}%
-- ANCHOR_END: prov

-- ANCHOR: believe
elpi_accumulate ch11_meta lp%{
  typeabbrev policy (person -> stmt -> prop).

  % S is believed under trust policy T, with chain W
  pred believe i:policy, o:stmt, o:prov.
  believe T S W :- asserted A, unpack T A stated S W.
  believe _ S (within E) :- inside E S.

  % walk into an asserted element, growing the chain
  pred unpack i:policy, i:stmt, i:prov,
              o:stmt, o:prov.
  unpack _ S W S W.
  unpack T (during S E) W S1 W1 :-
    unpack T S (context E W) S1 W1.
  unpack T (said P S) W S1 W1 :-
    T P S, unpack T S (claimed P W) S1 W1.
}%
-- ANCHOR_END: believe

-- ANCHOR: policies
elpi_accumulate ch11_meta lp%{
  % trust nobody's word: only our own records
  pred nobody i:person, i:stmt.
  nobody _ _ :- fail.

  % trust a claim about an event from someone
  % who was there
  pred witness i:person, i:stmt.
  witness P (during _ E) :- attended E P.
}%
-- ANCHOR_END: policies

-- ANCHOR: believe_query
/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_meta lp%{
  believe nobody (approved anna "budget") W }%

/-- info: W = context 1 (claimed marco stated) -/
#guard_msgs in
#elpi ch11_meta lp%{
  believe witness (approved anna "budget") W }%
-- ANCHOR_END: believe_query

-- ANCHOR: hearsay
/-- error: query has no solution -/
#guard_msgs in
#elpi ch11_meta lp%{
  believe witness (approved taras "hiring") W }%
-- ANCHOR_END: hearsay

-- ANCHOR: within
/-- info: W = within 1 -/
#guard_msgs in
#elpi ch11_meta lp%{
  believe nobody (present marco lisbon) W }%
-- ANCHOR_END: within

/-! ## The rule from the hook: whatever held, is minuted -/

-- ANCHOR: minutes
elpi_accumulate ch11_meta lp%{
  % document 10 holds the minutes of event 1
  pred minutes-of o:int, o:int.
  minutes-of 1 10.

  % any statement that held during a meeting
  % belongs in that meeting's minutes
  pred in-minutes i:policy, o:stmt, o:int.
  in-minutes T S M :-
    minutes-of E M, believe T (during S E) _.

  % all of them, as a list
  pred minuted i:policy, i:int, o:list stmt.
  minuted T M L :-
    std.findall (in-minutes T _ M) Sols,
    std.map Sols (s\ x\ s = in-minutes _ x _) L.
}%
-- ANCHOR_END: minutes

-- ANCHOR: minutes_query
/-- info: L = [agreed anna marco] -/
#guard_msgs in
#elpi ch11_meta lp%{ minuted nobody 10 L }%

/-- info: L = [agreed anna marco, approved anna "budget"] -/
#guard_msgs in
#elpi ch11_meta lp%{ minuted witness 10 L }%
-- ANCHOR_END: minutes_query

/-! ## A generic claim, proved for every statement -/

-- ANCHOR: generic
/-- info: W = context 1 (claimed marco stated) -/
#guard_msgs in
#elpi ch11_meta lp%{
  pi s\ asserted (said marco (during s 1))
          => believe witness s W }%
-- ANCHOR_END: generic

end Ch11
