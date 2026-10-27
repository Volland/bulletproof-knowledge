import Reasoning.Ch10.Rules

/-!
# Chapter 10: calling ELPI from Lean

`Elpi.query` runs a query in `MetaM` and returns a lazy
stream of solutions. We decode the answers into Lean
values, check them against Lean propositions, and combine
ELPI's explanations with Lean's verdicts.
-/

open Lean Meta
open Elpi.Cmd
open Memory

namespace Ch10

-- ANCHOR: answers
/-- The values of variable `v` in the first `limit`
    solutions of `q`, decoded at type `α`. -/
def answers {α : Type} [Elpi.FromElpi α]
    (q v : String) (limit : Nat := 50) :
    MetaM (List α) := do
  let sols ← Elpi.query rules q
  (sols.take limit).mapM fun
    | .ok s => match s.get? v with
      | some a => pure a
      | none => throwError "cannot decode {v}"
    | .error e => throwError "ELPI: {e}"
-- ANCHOR_END: answers

-- ANCHOR: answers-eval
/-- info: [Memory.Person.marco, Memory.Person.anna] -/
#guard_msgs in
#eval answers (α := Person) "manages M sofia" "M"
-- ANCHOR_END: answers-eval

-- ANCHOR: pairs
/-- Like `answers`, for two variables at once. -/
def pairs {α β : Type} [Elpi.FromElpi α] [Elpi.FromElpi β]
    (q x y : String) (limit : Nat := 50) :
    MetaM (List (α × β)) := do
  let sols ← Elpi.query rules q
  (sols.take limit).mapM fun
    | .ok s => match s.get? x, s.get? y with
      | some a, some b => pure (a, b)
      | _, _ => throwError "cannot decode {x}, {y}"
    | .error e => throwError "ELPI: {e}"

/-- Everyone above `p` in the reporting chain. -/
def managersOf (p : Person) : MetaM (List Person) := do
  let ps ← pairs (α := Person) (β := Person)
    "manages M P" "M" "P"
  return ps.filterMap fun (m, q) =>
    if q = p then some m else none

/-- info: [Memory.Person.marco, Memory.Person.anna] -/
#guard_msgs in
#eval managersOf .sofia
-- ANCHOR_END: pairs

-- ANCHOR: lazy
/-- info: [Memory.Person.anna] -/
#guard_msgs in
#eval answers (α := Person) "visited P C" "P" (limit := 1)
-- ANCHOR_END: lazy

-- ANCHOR: met-spec
/-- Lean's own definition of "met": two different people
    at the same remembered event. -/
def Met (s : Store) (a b : Person) : Prop :=
  a ≠ b ∧ ∃ e ∈ s.events, a ∈ e.who ∧ b ∈ e.who

instance (s : Store) (a b : Person) :
    Decidable (Met s a b) := by
  unfold Met; infer_instance
-- ANCHOR_END: met-spec

-- ANCHOR: checked
/-- People `p` met, found by ELPI and checked by Lean.
    An answer Lean cannot confirm is an error. -/
def metChecked (p : Person) : MetaM (List Person) := do
  let found ← pairs (α := Person) (β := Person)
    "met A B" "A" "B"
  let mine := found.filterMap fun (a, b) =>
    if a = p then some b else none
  for q in mine do
    unless decide (Met store p q) do
      throwError "unjustified answer: {repr q}"
  return mine.eraseDups

/-- info: [Memory.Person.lena, Memory.Person.sofia,
  Memory.Person.anna] -/
#guard_msgs (whitespace := lax) in
#eval metChecked .marco
-- ANCHOR_END: checked

-- ANCHOR: met-proof
example : Met store .marco .lena := by decide
-- ANCHOR_END: met-proof

-- ANCHOR: explain
/-- Lean decides whether the phantom meeting may enter
    memory; ELPI explains who clashes with which event. -/
def explainPhantom : MetaM (Option (Person × Nat)) := do
  match memory.insert World.phantom with
  | .ok _ => return none
  | .error _ =>
    let why ← pairs (α := Person) (β := Nat)
      "suspicious P Id" "P" "Id"
    return why.head?

/-- info: some (Memory.Person.anna, 1) -/
#guard_msgs in
#eval explainPhantom
-- ANCHOR_END: explain

-- ANCHOR: verdict
deriving instance Repr for Verdict

/-- info: [Ch10.Verdict.reject 1] -/
#guard_msgs in
#eval answers (α := Verdict)
  "mem.proposed E, verdict-of E V" "V"
-- ANCHOR_END: verdict

-- ANCHOR: fuel
elpi_program loopy
elpi_accumulate loopy db memdb
elpi_accumulate loopy lp%{
  % Left recursion: the rule calls itself first.
  pred above o:person, o:person.
  above M P :- above M X, reports-to P X.
  above M P :- reports-to P M.
}%

/-- First answer of `q` in `loopy`, with a step budget. -/
def firstAnswer (q : String) (fuel : Nat) :
    MetaM String := do
  let sols ← Elpi.query loopy q (fuel := fuel)
  match sols.take 1 with
  | [.ok s] => return toString s
  | [.error e] => return s!"{e}"
  | _ => return "no solution"

/-- info: "resource error: out of fuel" -/
#guard_msgs in
#eval firstAnswer "above M sofia" (fuel := 100000)
-- ANCHOR_END: fuel

end Ch10
