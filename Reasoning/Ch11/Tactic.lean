import Elpi
import Knowledge.Memory

/-!
# Chapter 11: an ELPI tactic for goals about the memory

The tactic searches in λProlog and builds a Lean proof
term. Lean checks the term; the kernel checks the
theorem. A wrong search, or a wrong hint, is rejected.

`reorg`, `edge` and `Under` repeat the definitions of
`Certificates.lean` in their own namespace, so that this
module stands alone.
-/

open Elpi.Cmd

namespace Ch11.Tac
open Memory

def reorg : Store :=
  { World.store with
    reportsTo := (.anna, .lena) :: World.store.reportsTo }

def edge (s : Store) (a b : Person) : Bool :=
  s.reportsTo.contains (a, b)

inductive Under (s : Store) : Person → Person → Prop
  | one {a b : Person} :
      edge s a b = true → Under s a b
  | step {a b c : Person} :
      edge s a b = true → Under s b c → Under s a c

-- ANCHOR: by_hand
example : Under reorg .marco .lena :=
  .step (b := .anna) rfl (.one rfl)
-- ANCHOR_END: by_hand

-- ANCHOR: search
elpi_program ch11_tac
elpi_accumulate ch11_tac lp%{
  accumulate lean.

  % candidate middle links, as Lean terms
  pred person o:term.
  person {{Memory.Person.anna}}.
  person {{Memory.Person.marco}}.
  person {{Memory.Person.lena}}.
  person {{Memory.Person.taras}}.
  person {{Memory.Person.sofia}}.

  % ask Lean: does `edge S A B` compute to true?
  pred edge i:term, i:term, i:term.
  edge S A B :-
    lean.mk_app {{@Ch11.Tac.edge}} [S, A, B] E,
    lean.defeq E {{true}}.
}%
-- ANCHOR_END: search

-- ANCHOR: build
elpi_accumulate ch11_tac lp%{
  % search a chain of at most N + 1 links and
  % build the proof term on the way back
  pred under i:int, i:term, i:term, i:term, o:term.
  under _ S A B P :- edge S A B,
    lean.mk_app {{@Ch11.Tac.Under.one}}
      [S, A, B, {{Eq.refl true}}] P.
  under N S A C P :- N > 0, person B, edge S A B,
    N1 is N - 1, under N1 S B C Q,
    lean.mk_app {{@Ch11.Tac.Under.step}}
      [S, A, B, C, {{Eq.refl true}}, Q] P.
}%
-- ANCHOR_END: build

-- ANCHOR: solve
elpi_accumulate ch11_tac lp%{
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal _ P
          {{Ch11.Tac.Under lp:{{S}} lp:{{A}} lp:{{B}}}})
        _ [] :-
    under 4 S A B P.
}%
elpi_tactic chain_search := ch11_tac
-- ANCHOR_END: solve

-- ANCHOR: use
theorem marco_under_lena : Under reorg .marco .lena := by
  elpi chain_search

theorem taras_under_lena : Under reorg .taras .lena := by
  elpi chain_search
-- ANCHOR_END: use

/--
info: theorem Ch11.Tac.marco_under_lena : Under reorg Person.marco Person.lena :=
Under.step (Eq.refl true) (Under.one (Eq.refl true))
-/
#guard_msgs in
-- ANCHOR: print
#print marco_under_lena
-- ANCHOR_END: print

-- ANCHOR: fail
/-- error: tactic chain_search failed: solve has no solution -/
#guard_msgs in
example : Under World.store .marco .lena := by
  elpi chain_search
-- ANCHOR_END: fail

/-! ## A hint from outside, checked by Lean -/

-- ANCHOR: hint
elpi_program ch11_hint
elpi_accumulate ch11_hint lp%{
  accumulate lean.
  % trust the hint: a two-link chain through M,
  % with no check of our own
  pred solve i:goal, i:list argument, o:list goal.
  solve (goal _ P
          {{Ch11.Tac.Under lp:{{S}} lp:{{A}} lp:{{B}}}})
        [trm M] [] :-
    lean.mk_app {{@Ch11.Tac.Under.one}}
      [S, M, B, {{Eq.refl true}}] Q,
    lean.mk_app {{@Ch11.Tac.Under.step}}
      [S, A, M, B, {{Eq.refl true}}, Q] P.
}%
elpi_tactic chain_hint := ch11_hint
-- ANCHOR_END: hint

-- ANCHOR: hint_ok
example : Under reorg .marco .lena := by
  elpi chain_hint Person.anna
-- ANCHOR_END: hint_ok

/--
error: (kernel) application type mismatch
  Under.step (Eq.refl true)
argument has type
  true = true
but function has type
  edge reorg Person.marco Person.taras = true →
    Under reorg Person.taras Person.lena → Under reorg Person.marco Person.lena
-/
#guard_msgs in
-- ANCHOR: hint_bad
example : Under reorg .marco .lena := by
  elpi chain_hint Person.taras
-- ANCHOR_END: hint_bad

end Ch11.Tac

/-- info: 'Ch11.Tac.marco_under_lena' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ch11.Tac.marco_under_lena
