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
/-- info: proof: above_one marco anna r_marco -/
#guard_msgs in
#lf_query chain lp%{ above marco anna }%
-- ANCHOR_END: query

/-- info: proof: above_step marco lena anna (above_one anna lena r_anna) r_marco -/
#guard_msgs in
-- ANCHOR: query2
#lf_query chain lp%{ above marco lena }%
-- ANCHOR_END: query2

-- ANCHOR: query_open
/-- info: B = anna
proof: above_one marco anna r_marco -/
#guard_msgs in
#lf_query chain lp%{ above marco B }%
-- ANCHOR_END: query_open

/-! ## Export to Lean -/

-- ANCHOR: export
lf_export chain
-- ANCHOR_END: export

/--
info: inductive Chain.Above : Chain.Person → Chain.Person → Prop
number of parameters: 0
constructors:
Chain.Above.above_one : ∀ {X Y : Chain.Person}, Chain.Reports X Y → Chain.Above X Y
Chain.Above.above_step : ∀ {X Z Y : Chain.Person}, Chain.Above Y Z → Chain.Reports X Y → Chain.Above X Z
-/
#guard_msgs in
-- ANCHOR: exported
#print Chain.Above
-- ANCHOR_END: exported

/-! ## Kernel-checked certificates -/

-- ANCHOR: certify
lf_certify chain Ch11.marco_above_lena_lf
  lp%{ above marco lena }%
-- ANCHOR_END: certify

/--
info: theorem Ch11.marco_above_lena_lf : Chain.Above Chain.Person.marco Chain.Person.lena :=
Chain.Above.above_step (Chain.Above.above_one Chain.Reports.r_anna) Chain.Reports.r_marco
-/
#guard_msgs in
-- ANCHOR: certify_print
#print Ch11.marco_above_lena_lf
-- ANCHOR_END: certify_print

/-- info: 'Ch11.marco_above_lena_lf' does not depend on any axioms -/
#guard_msgs in
-- ANCHOR: certify_axioms
#print axioms Ch11.marco_above_lena_lf
-- ANCHOR_END: certify_axioms

-- ANCHOR: certify_fail
/-- error: query has no solution -/
#guard_msgs in
lf_certify chain Ch11.lena_above_marco_lf
  lp%{ above lena marco }%
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
  above : person -> person -> type.
  above_one  : above X Y <- reports X Y.
  above_step : above X Z <- reports X Y <- above Y Z.
  % every possible report of M is below B
  under : person -> person -> type.
  under_all : under M B
    <- (pi x:person\ reports x M -> above x B).
}%
-- ANCHOR_END: hyp_sig

/--
info: proof: under_all marco anna (x0\ x1\ above_step x0 anna marco (above_one marco anna r_marco) x1)
-/
#guard_msgs in
-- ANCHOR: hyp_query
#lf_query hyp lp%{ under marco anna }%
-- ANCHOR_END: hyp_query

/--
error: lp%:13:2: in declaration 'under_all': outside the exportable fragment: a hypothetical premise over a family without binders
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

-- ANCHOR: above
/-- Is `(a, b)` a reporting line in `s`? -/
def edge (s : Store) (a b : Person) : Bool :=
  s.reportsTo.contains (a, b)

/-- `a` is somewhere below `b` in the reporting
    chain of `s`. -/
inductive Above (s : Store) : Person → Person → Prop
  | one {a b : Person} :
      edge s a b = true → Above s a b
  | step {a b c : Person} :
      edge s a b = true → Above s b c → Above s a c
-- ANCHOR_END: above

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
theorem above_sound {a b : Chain.Person} :
    Chain.Above a b → Above reorg (toMem a) (toMem b)
  | .above_one r => .one (reports_sound r)
  | .above_step h r =>
      .step (reports_sound r) (above_sound h)
-- ANCHOR_END: sound

-- ANCHOR: transfer
theorem marco_above_lena :
    Above reorg .marco .lena :=
  above_sound marco_above_lena_lf
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
