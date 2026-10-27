import Elpi
import Knowledge.Memory

/-!
# Chapter 10: the type bridge

The agent's Lean types become ELPI types (`deriving Elpi`),
the agent's Lean facts become ELPI predicates (`elpi_extern`),
and a shared database (`elpi_db`) turns them into relations.
Nothing about people, places or employment is written twice.
-/

open Elpi.Cmd
open Memory

-- ANCHOR: derive
deriving instance Elpi for Person
deriving instance Elpi for City
deriving instance Elpi for Country
deriving instance Elpi for Org
deriving instance Elpi for EventKind
-- ANCHOR_END: derive

-- ANCHOR: signature
/-- info: kind person type.
type anna person.
type marco person.
type lena person.
type taras person.
type sofia person. -/
#guard_msgs in
#elpi_signature Person
-- ANCHOR_END: signature

-- ANCHOR: no-proofs
/-- error: deriving Elpi: no ToElpi instance
  for the field type Memory.Interval -/
#guard_msgs (whitespace := lax) in
deriving instance Elpi for Event
-- ANCHOR_END: no-proofs

namespace Ch10

open Memory.World (day hour kickoff review)

-- ANCHOR: world
/-- Lena gives a talk in Porto; Marco and Sofia attend. -/
def talk : Event :=
  { id := 3, kind := .talk
    who := [.lena, .marco, .sofia], place := .porto
    span := .mk! (day 2001 + hour 14)
                 (day 2001 + hour 15) }

/-- Taras travels to Berlin for a day. -/
def trip : Event :=
  { id := 4, kind := .trip
    who := [.taras], place := .berlin
    span := .mk! (day 2002) (day 2003) }

/-- Chapter 1's world, plus Sofia at Acme and two events. -/
def store : Store :=
  { World.store with
    worksAt   := World.store.worksAt ++ [(.sofia, .acme)]
    reportsTo := World.store.reportsTo ++ [(.sofia, .marco)]
    events    := [trip, talk, review, kickoff] }

theorem store_consistent : Consistent store := by decide

def memory : Certified := ⟨store, store_consistent⟩
-- ANCHOR_END: world

-- ANCHOR: row
/-- An event without its proof field: plain data that
    can cross into ELPI. -/
structure EventRow where
  id    : Nat
  kind  : EventKind
  who   : List Person
  place : City
  start : Nat
  stop  : Nat
  deriving Repr, Elpi

def EventRow.of (e : Event) : EventRow :=
  ⟨e.id, e.kind, e.who, e.place, e.span.start, e.span.stop⟩
-- ANCHOR_END: row

-- ANCHOR: views
/-- The facts ELPI may read: projections of `memory`. -/
def worksAtFacts : List (Person × Org) :=
  memory.store.worksAt
def reportsToFacts : List (Person × Person) :=
  memory.store.reportsTo
def eventFacts : List EventRow :=
  memory.events.map EventRow.of
def bornAt (p : Person) : Nat := memory.store.born p
def countryOf (c : City) : Country := c.country
def physical (k : EventKind) : Bool := k.physical
-- ANCHOR_END: views

end Ch10

-- ANCHOR: extern
elpi_extern many Ch10.worksAtFacts as "mem.works-at"
elpi_extern many Ch10.reportsToFacts as "mem.reports-to"
elpi_extern many Ch10.eventFacts as "mem.event"
elpi_extern Ch10.bornAt as "mem.born"
elpi_extern Ch10.countryOf as "mem.country"
elpi_extern Ch10.physical as "mem.physical"
-- ANCHOR_END: extern

namespace Ch10

-- ANCHOR: db
elpi_db memdb
elpi_accumulate memdb lp%{
  % The closed world: every individual, listed once.
  pred person o:person.
  person P :- std.mem [anna, marco, lena, taras, sofia] P.
  pred org o:org.
  org O :- std.mem [acme, lumen, kyivTech] O.
  pred city o:city.
  city C :- std.mem [kyiv, lviv, lisbon, porto, berlin] C.
  pred country o:country.
  country C :- std.mem [ukraine, portugal, germany] C.
  pred event-kind o:eventKind.
  event-kind K :- std.mem [meeting, call, talk, trip] K.

  % Relations, read from the Lean store.
  pred works-at o:person, o:org.
  works-at P O :- mem.works-at (pr P O).
  pred reports-to o:person, o:person.
  reports-to P M :- mem.reports-to (pr P M).
  pred event o:int, o:eventKind, o:city, o:int, o:int.
  event Id K C S E :-
    mem.event (eventRow.mk Id K _ C S E).
  pred attended o:int, o:person.
  attended Id P :-
    mem.event (eventRow.mk Id _ Who _ _ _),
    std.mem Who P.
}%
-- ANCHOR_END: db

-- ANCHOR: probe-program
elpi_program bridge
elpi_accumulate bridge db memdb
-- ANCHOR_END: probe-program

-- ANCHOR: probe
/-- info: O = acme -/
#guard_msgs in
#elpi bridge lp%{ works-at sofia O }%

/-- info: C = portugal -/
#guard_msgs in
#elpi bridge lp%{ mem.country porto C }%

/-- info: T = 1440000 -/
#guard_msgs in
#elpi bridge lp%{ mem.born sofia T }%

set_option elpi.solutions 10 in
/-- info: P = lena
---
info: P = marco
---
info: P = sofia -/
#guard_msgs in
#elpi bridge lp%{ attended 3 P }%
-- ANCHOR_END: probe

-- ANCHOR: typed-extern
/-- error: lisbon has type city but is used with type person -/
#guard_msgs in
#elpi bridge lp%{ mem.born lisbon T }%
-- ANCHOR_END: typed-extern

end Ch10
