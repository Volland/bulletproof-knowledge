import Knowledge.Memory

/-!
# Chapter 8 — The place hierarchy

Cities are part of countries, countries are part of
regions. `PartOf` is an inductive relation: its proofs
are paths up the hierarchy. From the store and the
hierarchy we derive, and prove, where people were.
-/

namespace Ch08

open Memory Memory.World

-- ANCHOR: region
/-- The top level of the place hierarchy. -/
inductive Region where
  | iberia | easternEurope | centralEurope
  deriving DecidableEq, Repr

/-- Every country lies in exactly one region. -/
def regionOf : Country → Region
  | .ukraine  => .easternEurope
  | .portugal => .iberia
  | .germany  => .centralEurope
-- ANCHOR_END: region

-- ANCHOR: place
/-- One type for all levels, so that a single
    relation can connect them. -/
inductive Place where
  | city    (c : City)
  | country (k : Country)
  | region  (r : Region)
  deriving DecidableEq, Repr
-- ANCHOR_END: place

-- ANCHOR: directly
/-- The asserted edges, computed from the two
    functions. Nothing else is directly in anything. -/
inductive DirectlyIn : Place → Place → Prop
  | city    (c : City) :
      DirectlyIn (.city c) (.country c.country)
  | country (k : Country) :
      DirectlyIn (.country k) (.region (regionOf k))
-- ANCHOR_END: directly

-- ANCHOR: partof
/-- Proper parthood: one or more direct steps up. -/
inductive PartOf : Place → Place → Prop
  | direct {a b : Place} :
      DirectlyIn a b → PartOf a b
  | step {a b c : Place} :
      DirectlyIn a b → PartOf b c → PartOf a c
-- ANCHOR_END: partof

-- ANCHOR: trans
/-- Parthood is transitive: chain two paths. -/
theorem PartOf.trans {a b c : Place} :
    PartOf a b → PartOf b c → PartOf a c := by
  intro h₁ h₂
  induction h₁ with
  | direct d => exact .step d h₂
  | step d _ ih => exact .step d (ih h₂)
-- ANCHOR_END: trans

-- ANCHOR: lisbon
/-- Lisbon is part of Iberia: city → country →
    region. The proof term *is* the path. -/
theorem lisbon_in_iberia :
    PartOf (.city .lisbon) (.region .iberia) :=
  .step (.city .lisbon) (.direct (.country .portugal))
-- ANCHOR_END: lisbon

-- ANCHOR: level
/-- Height in the hierarchy. -/
def Place.level : Place → Nat
  | .city _    => 0
  | .country _ => 1
  | .region _  => 2

theorem DirectlyIn.level_lt {a b : Place} :
    DirectlyIn a b → a.level < b.level := by
  intro d
  cases d <;> simp [Place.level]

/-- Every step goes up, so every path goes up. -/
theorem PartOf.level_lt {a b : Place} :
    PartOf a b → a.level < b.level := by
  intro h
  induction h with
  | direct d => exact d.level_lt
  | step d _ ih => exact Nat.lt_trans d.level_lt ih

/-- No place is part of itself. -/
theorem PartOf.irrefl (a : Place) : ¬ PartOf a a :=
  fun h => Nat.lt_irrefl _ h.level_lt
-- ANCHOR_END: level

-- ANCHOR: inverted
/-- "Portugal is in Lisbon" has no proof, and we can
    prove that it has none. -/
theorem portugal_not_in_lisbon :
    ¬ PartOf (.country .portugal) (.city .lisbon) :=
  fun h => absurd h.level_lt (by decide)
-- ANCHOR_END: inverted

-- ANCHOR: mereology
/-- A class that carries laws. An instance must
    supply a relation *and* prove both properties. -/
class Mereology (α : Type) where
  Part   : α → α → Prop
  trans  : ∀ {a b c : α}, Part a b → Part b c → Part a c
  irrefl : ∀ a : α, ¬ Part a a

instance : Mereology Place :=
  ⟨PartOf, PartOf.trans, PartOf.irrefl⟩

/-- Proven once for every lawful hierarchy. -/
theorem Mereology.asymm {α : Type} [Mereology α]
    {a b : α} (h : Part a b) : ¬ Part b a :=
  fun h' => irrefl a (trans h h')

/-- Place inherits asymmetry without new work. -/
theorem iberia_not_in_lisbon :
    ¬ PartOf (.region .iberia) (.city .lisbon) :=
  Mereology.asymm (α := Place) lisbon_in_iberia
-- ANCHOR_END: mereology

-- ANCHOR: ancestors
/-- Everything a place is part of, nearest first. -/
def Place.ancestors : Place → List Place
  | .city c    => [.country c.country,
                   .region (regionOf c.country)]
  | .country k => [.region (regionOf k)]
  | .region _  => []

-- ANCHOR_END: ancestors

-- ANCHOR: to-list
/-- From a path to list membership. -/
theorem PartOf.mem_ancestors {a b : Place}
    (h : PartOf a b) : b ∈ a.ancestors := by
  induction h with
  | direct d => cases d <;> simp [Place.ancestors]
  | step d _ ih =>
    cases d with
    | city c =>
      simp [Place.ancestors] at ih ⊢
      exact Or.inr ih
    | country k => simp [Place.ancestors] at ih
-- ANCHOR_END: to-list

-- ANCHOR: from-list
/-- From list membership to a path. -/
theorem PartOf.of_mem_ancestors {a b : Place}
    (h : b ∈ a.ancestors) : PartOf a b := by
  cases a with
  | city c =>
    simp [Place.ancestors] at h
    rcases h with rfl | rfl
    · exact .direct (.city c)
    · exact .step (.city c) (.direct (.country _))
  | country k =>
    simp [Place.ancestors] at h
    subst h
    exact .direct (.country k)
  | region r => simp [Place.ancestors] at h
-- ANCHOR_END: from-list

-- ANCHOR: partof-decidable
/-- The function and the relation agree ... -/
theorem partOf_iff {a b : Place} :
    PartOf a b ↔ b ∈ a.ancestors :=
  ⟨PartOf.mem_ancestors, PartOf.of_mem_ancestors⟩

/-- ... so list membership decides parthood. -/
instance (a b : Place) : Decidable (PartOf a b) :=
  decidable_of_iff _ partOf_iff.symm
-- ANCHOR_END: partof-decidable

-- ANCHOR: decide
example : PartOf (.city .porto) (.region .iberia) := by
  decide

/-- "Lisbon is in Germany": refuted by computation. -/
example : ¬ PartOf (.city .lisbon) (.country .germany) := by
  decide
-- ANCHOR_END: decide

-- ANCHOR: inside
/-- At a place or anywhere inside it. -/
def Inside (a b : Place) : Prop := a = b ∨ PartOf a b

instance (a b : Place) : Decidable (Inside a b) :=
  inferInstanceAs (Decidable (_ ∨ _))
-- ANCHOR_END: inside

-- ANCHOR: wasin
/-- `p` was physically somewhere inside `pl`: some
    recorded in-person event placed them there. -/
def WasIn (s : Store) (p : Person) (pl : Place) :
    Prop :=
  ∃ e ∈ s.events,
    e.kind.physical = true ∧ p ∈ e.who ∧
    Inside (.city e.place) pl

instance (s : Store) (p : Person) (pl : Place) :
    Decidable (WasIn s p pl) := by
  unfold WasIn; infer_instance
-- ANCHOR_END: wasin

-- ANCHOR: portugal
/-- The derived fact, with its certificate spelled
    out: which event, and which path up the map. -/
theorem anna_in_portugal :
    WasIn store .anna (.country .portugal) :=
  ⟨kickoff, by decide, rfl, by decide,
   .inr (.direct (.city .lisbon))⟩

/-- The same kind of fact, found by computation. -/
theorem marco_in_iberia :
    WasIn store .marco (.region .iberia) := by
  decide
-- ANCHOR_END: portugal

-- ANCHOR: not-ukraine
/-- The review was a *call* placed in Kyiv. It does
    not put Anna in Ukraine, and the kernel agrees. -/
theorem anna_not_in_ukraine :
    ¬ WasIn store .anna (.country .ukraine) := by
  decide
-- ANCHOR_END: not-ukraine

-- ANCHOR: lena-false
/--
error: Tactic `decide` proved that the proposition
  WasIn store Person.lena (Place.region Region.iberia)
is false
-/
#guard_msgs in
example : WasIn store .lena (.region .iberia) := by
  decide
-- ANCHOR_END: lena-false

-- ANCHOR: within-class
/-- Tempting: containment as a type class. -/
class Within (Small Big : Type) where
  up : Small → Big

instance : Within City Country := ⟨City.country⟩
instance : Within Country Region := ⟨regionOf⟩
-- ANCHOR_END: within-class

-- ANCHOR: within-trans
/--
error: cannot find synthesization order for instance
@withinTrans with type
  {A B C : Type} → [Within A B] → [Within B C] →
    Within A C
all remaining arguments have metavariables:
  Within A ?B
  Within ?B C
-/
#guard_msgs (whitespace := lax) in
instance withinTrans {A B C : Type}
    [Within A B] [Within B C] : Within A C :=
  ⟨fun a => Within.up (Within.up a : B)⟩
-- ANCHOR_END: within-trans

end Ch08
