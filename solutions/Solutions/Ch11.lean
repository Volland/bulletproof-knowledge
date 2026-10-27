import Elpi
import Knowledge.Memory

/-!
# Solutions to the exercises of Chapter 11

Self-contained: the facts and rules each exercise needs
are repeated here.
-/

/-! ## Exercise 4: an LF certificate for colleagues

LF commands run outside any namespace (see
`Reasoning/Ch11/Certificates.lean`). -/

open Elpi.LFCmd

lf_signature colleagues lp%{
  #lf
  person : type.
  anna : person.
  marco : person.
  lena : person.
  org : type.
  acme : org.
  lumen : org.
  works : person -> org -> type.
  w_anna  : works anna acme.
  w_marco : works marco acme.
  w_lena  : works lena lumen.
  colleagues : person -> person -> type.
  same_org : colleagues A B <- works A O <- works B O.
}%

lf_export colleagues

lf_certify colleagues Solutions.Ch11.anna_marco
  lp%{ colleagues anna marco }%

/-- info: 'Solutions.Ch11.anna_marco' does not depend on any axioms -/
#guard_msgs in
#print axioms Solutions.Ch11.anna_marco

/-- error: query has no solution -/
#guard_msgs in
lf_certify colleagues Solutions.Ch11.anna_lena
  lp%{ colleagues anna lena }%

open Elpi.Cmd

namespace Solutions.Ch11
open Memory

deriving instance Elpi for Person
deriving instance Elpi for City
deriving instance Elpi for EventKind

/-! ## Exercise 1: is a relation symmetric? -/

elpi_program sol11_ho
elpi_accumulate sol11_ho lp%{
  pred reports o:person, o:person.
  reports marco anna.
  reports taras lena.

  pred attended o:int, o:person.
  attended 1 anna. attended 1 marco.
  attended 2 anna. attended 2 taras.

  pred kind-of o:int, o:eventKind.
  kind-of 1 meeting. kind-of 2 call.

  pred met o:person, o:person.
  met X Y :- attended E X, kind-of E meeting,
             attended E Y, not (X = Y).

  % a counterexample to "R is symmetric"
  pred not-symmetric i:(person -> person -> prop),
                     o:person, o:person.
  not-symmetric R X Y :- R X Y, not (R Y X).
}%

/-- error: query has no solution -/
#guard_msgs in
#elpi sol11_ho lp%{ not-symmetric met X Y }%

/-- info: X = marco, Y = anna -/
#guard_msgs in
#elpi sol11_ho lp%{ not-symmetric reports X Y }%

/-! ## Exercise 2: what if Taras had joined the kickoff? -/

elpi_program sol11_hyp
elpi_accumulate sol11_hyp lp%{
  pred ev o:int, o:eventKind, o:city, o:int, o:int.
  ev 1 meeting lisbon 2880600 2880660.
  ev 2 call    kyiv   2880600 2880660.

  pred attended o:int, o:person.
  attended 1 anna. attended 1 marco.
  attended 2 anna. attended 2 taras.

  pred physical i:eventKind.
  physical meeting. physical talk. physical trip.

  pred bilocated o:person, o:int, o:int.
  bilocated P E1 E2 :-
    attended E1 P, attended E2 P, E1 < E2,
    ev E1 K1 C1 S1 T1, ev E2 K2 C2 S2 T2,
    physical K1, physical K2, not (C1 = C2),
    S1 < T2, S2 < T1.
}%

-- The review was a call, so Taras may join the
-- Lisbon kickoff at the same time: no violation.
/-- error: query has no solution -/
#guard_msgs in
#elpi sol11_hyp lp%{ attended 1 taras => bilocated P A B }%

-- Had the review been a meeting in Kyiv, he could not.
/-- info: P = taras, A = 1, B = 2 -/
#guard_msgs in
#elpi sol11_hyp lp%{
  [ attended 1 taras, ev 2 meeting kyiv 2880600 2880660 ]
  => bilocated P A B }%

/-! ## Exercise 3: a policy that trusts everyone -/

elpi_program sol11_meta
elpi_accumulate sol11_meta lp%{
  kind stmt type.
  type agreed   person -> person -> stmt.
  type approved person -> string -> stmt.
  type during   stmt -> int -> stmt.
  type said     person -> stmt -> stmt.

  pred asserted o:stmt.
  asserted (during (agreed anna marco) 1).
  asserted (said marco
             (during (approved anna "budget") 1)).
  asserted (said lena
             (during (approved taras "hiring") 1)).

  kind prov type.
  type stated  prov.
  type context int -> prov -> prov.
  type claimed person -> prov -> prov.

  typeabbrev policy (person -> stmt -> prop).
  pred believe i:policy, o:stmt, o:prov.
  believe T S W :- asserted A, unpack T A stated S W.
  pred unpack i:policy, i:stmt, i:prov,
              o:stmt, o:prov.
  unpack _ S W S W.
  unpack T (during S E) W S1 W1 :-
    unpack T S (context E W) S1 W1.
  unpack T (said P S) W S1 W1 :-
    T P S, unpack T S (claimed P W) S1 W1.

  pred inner i:prop, o:stmt.
  inner (believe _ (during S _) _) S.

  pred minuted i:policy, i:int, o:list stmt.
  minuted T E L :-
    std.findall (believe T (during _ E) _) Sols,
    std.map Sols inner L.

  % the answer: every claim is accepted
  pred anyone i:person, i:stmt.
  anyone _ _.
}%

/--
info: L = [agreed anna marco, approved anna "budget", approved taras "hiring"]
-/
#guard_msgs in
#elpi sol11_meta lp%{ minuted anyone 1 L }%

end Solutions.Ch11
