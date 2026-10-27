import Elpi
import Knowledge.Memory

/-!
# Chapter 11: certificates from the LF layer

An LF signature states judgments as types and rules as
constants. The engine searches for a derivation, records
it as a proof term, and `lf_certify` hands that term to
the Lean kernel. A soundness theorem, proved once in
Lean, carries every certificate over to the memory.

The LF commands run outside any namespace: in lean-elpi
v0.3.3, `lf_certify` refers to the exported names from
the root namespace.
-/

open Elpi.LFCmd

/-! ## The signature and its proof terms -/

-- ANCHOR: signature
lf_signature chain "chain.elpi"
-- ANCHOR_END: signature

-- ANCHOR: query
/-- info: proof: under_one marco anna r_marco -/
#guard_msgs in
#lf_query chain lp%{ under marco anna }%
-- ANCHOR_END: query

/-- info: proof: under_step marco lena anna (under_one anna lena r_anna) r_marco -/
#guard_msgs in
-- ANCHOR: query2
#lf_query chain lp%{ under marco lena }%
-- ANCHOR_END: query2

-- ANCHOR: query_open
/-- info: B = anna
proof: under_one marco anna r_marco -/
#guard_msgs in
#lf_query chain lp%{ under marco B }%
-- ANCHOR_END: query_open

/-! ## Export to Lean -/

-- ANCHOR: export
lf_export chain
-- ANCHOR_END: export

/--
info: inductive Chain.Under : Chain.Person → Chain.Person → Prop
number of parameters: 0
constructors:
Chain.Under.under_one : ∀ {X Y : Chain.Person}, Chain.Reports X Y → Chain.Under X Y
Chain.Under.under_step : ∀ {X Z Y : Chain.Person}, Chain.Under Y Z → Chain.Reports X Y → Chain.Under X Z
-/
#guard_msgs in
-- ANCHOR: exported
#print Chain.Under
-- ANCHOR_END: exported

/-! ## Kernel-checked certificates -/

-- ANCHOR: certify
lf_certify chain Ch11.marco_under_lena_lf
  lp%{ under marco lena }%
-- ANCHOR_END: certify

/--
info: theorem Ch11.marco_under_lena_lf : Chain.Under Chain.Person.marco Chain.Person.lena :=
Chain.Under.under_step (Chain.Under.under_one Chain.Reports.r_anna) Chain.Reports.r_marco
-/
#guard_msgs in
-- ANCHOR: certify_print
#print Ch11.marco_under_lena_lf
-- ANCHOR_END: certify_print

/-- info: 'Ch11.marco_under_lena_lf' does not depend on any axioms -/
#guard_msgs in
-- ANCHOR: certify_axioms
#print axioms Ch11.marco_under_lena_lf
-- ANCHOR_END: certify_axioms

-- ANCHOR: certify_fail
/-- error: query has no solution -/
#guard_msgs in
lf_certify chain Ch11.lena_under_marco_lf
  lp%{ under lena marco }%
-- ANCHOR_END: certify_fail

/-! ## Hypothetical judgments: found, not yet exported -/

-- ANCHOR: hyp_sig
lf_signature hyp lp%{
  #lf
  person : type.
  anna : person.
  marco : person.
  reports : person -> person -> type.
  r_marco : reports marco anna.
  under : person -> person -> type.
  under_one  : under X Y <- reports X Y.
  under_step : under X Z <- reports X Y <- under Y Z.
  % every possible report of M is below B
  team_under : person -> person -> type.
  team_all : team_under M B
    <- (pi x:person\ reports x M -> under x B).
}%
-- ANCHOR_END: hyp_sig

/--
info: proof: team_all marco anna (x0\ x1\ under_step x0 anna marco (under_one marco anna r_marco) x1)
-/
#guard_msgs in
-- ANCHOR: hyp_query
#lf_query hyp lp%{ team_under marco anna }%
-- ANCHOR_END: hyp_query

/--
error: lp%:13:2: in declaration 'team_all': outside the exportable fragment: a hypothetical premise over a family without binders
-/
#guard_msgs in
-- ANCHOR: hyp_export
lf_export hyp
-- ANCHOR_END: hyp_export

namespace Ch11
open Memory

/-! ## From the LF world to the memory -/

-- ANCHOR: reorg
/-- The memory after a reorganization:
    Anna now reports to Lena. -/
def reorg : Store :=
  { World.store with
    reportsTo := (.anna, .lena) :: World.store.reportsTo }

theorem reorg_consistent : Consistent reorg := by
  decide
-- ANCHOR_END: reorg

-- ANCHOR: under
/-- Is `(a, b)` a reporting line in `s`? -/
def edge (s : Store) (a b : Person) : Bool :=
  s.reportsTo.contains (a, b)

/-- `a` is somewhere under `b` in the reporting
    chain of `s`. -/
inductive Under (s : Store) : Person → Person → Prop
  | one {a b : Person} :
      edge s a b = true → Under s a b
  | step {a b c : Person} :
      edge s a b = true → Under s b c → Under s a c
-- ANCHOR_END: under

-- ANCHOR: toMem
/-- The LF people are the memory's people. -/
def toMem : Chain.Person → Person
  | .anna => .anna   | .marco => .marco
  | .lena => .lena   | .taras => .taras
  | .sofia => .sofia
-- ANCHOR_END: toMem

-- ANCHOR: sound
/-- Every LF reporting fact is in the store. -/
theorem reports_sound {a b : Chain.Person}
    (h : Chain.Reports a b) :
    edge reorg (toMem a) (toMem b) = true := by
  cases h <;> rfl

/-- Every LF derivation is a chain in the store. -/
theorem under_sound {a b : Chain.Person} :
    Chain.Under a b → Under reorg (toMem a) (toMem b)
  | .under_one r => .one (reports_sound r)
  | .under_step h r =>
      .step (reports_sound r) (under_sound h)
-- ANCHOR_END: sound

-- ANCHOR: transfer
theorem marco_under_lena :
    Under reorg .marco .lena :=
  under_sound marco_under_lena_lf
-- ANCHOR_END: transfer

-- ANCHOR: liar
/--
error: Tactic `decide` proved that the proposition
  edge reorg Person.sofia Person.anna = true
is false
-/
#guard_msgs in
example : edge reorg .sofia .anna = true := by
  decide
-- ANCHOR_END: liar

end Ch11
