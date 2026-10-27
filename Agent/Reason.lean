import Elpi
import Agent.Check

/-!
# Derived answers in λProlog

A few ELPI rules, self-contained: they do not depend on the
Chapter 10 and 11 modules. The certified store is handed to
ELPI as hypothetical clauses (`facts => goal`) for one query
at a time, so the rules never see a fact that Lean did not
accept, and nothing persists between queries.
-/

open Elpi.Cmd Memory

-- ANCHOR: bridge
deriving instance Elpi for Person
deriving instance Elpi for City
deriving instance Elpi for Country
deriving instance Elpi for EventKind

-- Lean's own functions become ELPI predicates: one source
-- of truth for geography and for "physical".
elpi_extern Memory.City.country as "country"
elpi_extern Memory.EventKind.physical as "physical"
-- ANCHOR_END: bridge

-- ANCHOR: rules
elpi_program agentRules
elpi_accumulate agentRules lp%{
  % Facts arrive with each query, from the certified store.
  pred event o:int, o:eventKind, o:city.
  pred attends o:int, o:person.
  pred reports o:person, o:person.

  % P and Q met if both attended one physical event E.
  pred met i:person, o:person, o:int.
  met P Q E :-
    attends E P, event E K _, physical K tt,
    attends E Q, not (P = Q).

  % P was in country C during the physical event E.
  pred was_in i:person, i:country, o:int.
  was_in P C E :-
    attends E P, event E K X, physical K tt,
    country X C.

  % The management chain above P, bottom up.
  pred chain i:person, o:list person.
  chain P [M | Ms] :- reports P M, !, chain M Ms.
  chain _ [].
}%
-- ANCHOR_END: rules

namespace Agent

open Lean
open Elpi (Solution ElpiError)

-- ANCHOR: render
/-- The store as ELPI clauses, one string per fact. -/
def storeFacts (s : Store) : List String :=
  let ev (e : Event) :=
    s!"event {e.id} {kinds.name e.kind} \
       {cities.name e.place}" ::
    e.who.map fun p => s!"attends {e.id} {people.name p}"
  s.events.flatMap ev ++
    s.reportsTo.map fun (p, m) =>
      s!"reports {people.name p} {people.name m}"

/-- `[f₁, f₂, …] => goal`: the facts hold for this one
    query only (Chapter 11's `=>`). -/
def withStore (s : Store) (goal : String) : String :=
  "[" ++ ", ".intercalate (storeFacts s) ++ "] => " ++ goal
-- ANCHOR_END: render

-- ANCHOR: solve
/-- Run a goal against the certified store: at most `n`
    solutions, and a fuel budget so that a cyclic reporting
    line cannot hang the agent. -/
def solve (s : Store) (goal : String) (n : Nat := 20) :
    MetaM (List (Except ElpiError Solution)) := do
  let sols ← Elpi.query agentRules (withStore s goal)
    (fuel := 100000)
  return sols.take n
-- ANCHOR_END: solve

-- ANCHOR: reasoner
/-- The loop runs in `IO`; ELPI queries need `MetaM` and an
    environment that contains `agentRules`. A `Reasoner`
    hides that plumbing. -/
structure Reasoner where
  run : {α : Type} → MetaM α → IO α

def Reasoner.ofEnv (env : Environment) : Reasoner where
  run act := do
    let ctx : Core.Context :=
      { fileName := "<agent>", fileMap := default }
    let (a, _) ← (act.run' {} {}).toIO ctx { env }
    return a
-- ANCHOR_END: reasoner

/-! ## Checks -/

/-- The rules on the book's world: whom did Anna meet? -/
def demoMet : MetaM (List (Option Person × Option Nat)) := do
  let sols ← solve World.store "met anna Q E"
  return sols.map fun
    | .ok sol => (sol.get? "Q", sol.get? "E")
    | .error _ => (none, none)

-- ANCHOR: demo
/-- info: [(some (Memory.Person.marco), some 1)] -/
#guard_msgs in
#eval demoMet
-- ANCHOR_END: demo

/-- The names Lean writes are the names ELPI reads back:
    each person survives the trip through the engine. -/
def namesAgree : MetaM Bool := do
  let ps := [Person.anna, .marco, .lena, .taras, .sofia]
  let ok ← ps.allM fun p => do
    let sols ← Elpi.query agentRules
      s!"X = {people.name p}"
    return match sols.head? with
      | some (.ok sol) => (sol.get? "X" : Option Person) == p
      | _ => false
  return ok

/-- info: true -/
#guard_msgs in
#eval namesAgree

-- ANCHOR: cycle
/-- A cyclic reporting line passes every axiom of
    Chapter 7, and the chain rule would recurse forever.
    The fuel budget turns that into an error value. -/
def cyclic : Store :=
  { World.store with
    reportsTo := [(.anna, .marco), (.marco, .anna)] }

example : Consistent cyclic := by decide

/-- info: ["resource error: out of fuel"] -/
#guard_msgs in
#eval show MetaM _ from do
  let sols ← solve cyclic "chain anna L"
  return sols.map fun
    | .ok _    => "solution"
    | .error e => toString e
-- ANCHOR_END: cycle

end Agent
