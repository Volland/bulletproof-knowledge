import Knowledge.Memory

/-!
# Chapter 3: reasoning with the graph

Reachability as an inductive relation, a proof of a
concrete path, and a checker that answers "yes" or "no"
with a proof either way.

The vertices are people to keep the book's code free of
type-class arguments. Nothing below depends on that
choice: any vertex type with decidable equality works.
Chapter 2's `Chain` is the non-reflexive cousin of
`Reach` (one or more steps instead of zero or more).
-/

namespace Ch03

open Memory

-- ANCHOR: graph
/-- A directed graph of people: a list of edges. -/
abbrev Graph := List (Person × Person)

/-- Who talked to whom: every ordered pair of
    distinct people at the same event. -/
def talked (s : Store) : Graph :=
  s.events.flatMap fun e =>
    e.who.flatMap fun p =>
      (e.who.filter (· ≠ p)).map fun q => (p, q)

/-- info: [(Memory.Person.anna, Memory.Person.taras),
 (Memory.Person.taras, Memory.Person.anna),
 (Memory.Person.anna, Memory.Person.marco),
 (Memory.Person.marco, Memory.Person.anna)] -/
#guard_msgs in
#eval talked World.store
-- ANCHOR_END: graph

-- ANCHOR: reach
/-- `Reach g a b`: a path leads from `a` to `b`. -/
inductive Reach (g : Graph) :
    Person → Person → Prop where
  /-- everyone reaches themselves: zero steps -/
  | here (a : Person) : Reach g a a
  /-- take one edge, then keep going -/
  | step (a b c : Person) :
      (a, b) ∈ g → Reach g b c → Reach g a c
-- ANCHOR_END: reach

-- ANCHOR: path_proof
/-- News from the kickoff can reach Taras:
    Marco talked to Anna, Anna talked to Taras. -/
theorem marco_reaches_taras :
    Reach (talked World.store) .marco .taras :=
  .step .marco .anna .taras (by decide)
    (.step .anna .taras .taras (by decide)
      (.here .taras))
-- ANCHOR_END: path_proof

/-- A path can be extended by one edge at the end. -/
theorem Reach.snoc (g : Graph) (a b c : Person)
    (h : Reach g a b) (e : (b, c) ∈ g) :
    Reach g a c := by
  induction h with
  | here => exact .step _ _ _ e (.here _)
  | step _ _ _ e' _ ih => exact .step _ _ _ e' (ih e)

-- ANCHOR: reachable
/-- One round: add every target of an edge
    whose source is already in `S`. -/
def expand (g : Graph) (S : List Person) :
    List Person :=
  S ++ (g.filter fun p => p.1 ∈ S).map (·.2)

/-- Repeat `n` rounds, starting from `S`. -/
def reachable (g : Graph) :
    Nat → List Person → List Person
  | 0,     S => S
  | n + 1, S => reachable g n (expand g S)
-- ANCHOR_END: reachable

-- ANCHOR: sound
/-- Everything `reachable` collects is reachable. -/
theorem reachable_sound (g : Graph) (a : Person) :
    ∀ (n : Nat) (S : List Person),
      (∀ x ∈ S, Reach g a x) →
      ∀ x ∈ reachable g n S, Reach g a x
-- ANCHOR_END: sound
    := by
  intro n
  induction n with
  | zero => intro S h; exact h
  | succ n ih =>
    intro S h
    apply ih
    intro x hx
    simp only [expand, List.mem_append,
      List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hx
    rcases hx with hx | ⟨⟨y, z⟩, ⟨he, hy⟩, rfl⟩
    · exact h x hx
    · exact Reach.snoc _ _ _ _ (h y hy) he

-- ANCHOR: sound

/-- The starting person is never dropped. -/
theorem reachable_keeps (g : Graph) (a : Person) :
    ∀ (n : Nat) (S : List Person),
      a ∈ S → a ∈ reachable g n S
-- ANCHOR_END: sound
    := by
  intro n
  induction n with
  | zero => intro S h; exact h
  | succ n ih =>
    intro S h
    exact ih _ (List.mem_append_left _ h)

-- ANCHOR: sealed
/-- `S` is sealed: no edge leaves it. -/
abbrev Sealed (g : Graph) (S : List Person) : Prop :=
  ∀ p ∈ g, p.1 ∈ S → p.2 ∈ S

/-- If `a` is inside a sealed set and `b` is
    outside it, no path leads from `a` to `b`. -/
theorem not_reach_of_sealed (g : Graph)
    (S : List Person) (a b : Person) :
    Sealed g S → a ∈ S → b ∉ S → ¬ Reach g a b
-- ANCHOR_END: sealed
    := by
  intro hs ha hb h
  induction h with
  | here => exact hb ha
  | step _ _ _ e _ ih => exact ih (hs _ e ha) hb

/-- The start reaches itself (helper for `check`). -/
theorem start_reaches (g : Graph) (a : Person) :
    ∀ x ∈ [a], Reach g a x := by
  intro x hx
  simp at hx
  subst hx
  exact .here _

/-- The start is collected (helper for `check`). -/
theorem start_kept (g : Graph) (a : Person)
    (n : Nat) : a ∈ reachable g n [a] :=
  reachable_keeps g a n [a] (by simp)

-- ANCHOR: verdict
/-- An answer to "does `a` reach `b`?" that
    carries its evidence. -/
inductive Verdict (g : Graph) (a b : Person) where
  | yes (h : Reach g a b)
  | no  (h : ¬ Reach g a b)
  | gaveUp

/-- Decide reachability on a finite graph. -/
def check (g : Graph) (a b : Person) :
    Verdict g a b :=
  let S := reachable g (g.length + 1) [a]
  if hb : b ∈ S then
    .yes (reachable_sound g a _ [a]
      (start_reaches g a) b hb)
  else if hs : Sealed g S then
    .no (not_reach_of_sealed g S a b hs
      (start_kept g a _) hb)
  else .gaveUp
-- ANCHOR_END: verdict

/-- A verdict as text. The proofs are erased at run
    time, so there is no path left to print. -/
def Verdict.show {g : Graph} {a b : Person} :
    Verdict g a b → String
  | .yes _  => "yes, with a path"
  | .no _   => "no, with a sealed set"
  | .gaveUp => "out of fuel"

-- ANCHOR: ask
/-- info: "yes, with a path" -/
#guard_msgs in
#eval (check (talked World.store) .marco .taras).show

/-- info: "no, with a sealed set" -/
#guard_msgs in
#eval (check (talked World.store) .marco .lena).show
-- ANCHOR_END: ask

-- ANCHOR: lena
/-- Nobody the agent recorded ever talked to Lena. -/
theorem marco_not_reaches_lena :
    ¬ Reach (talked World.store) .marco .lena :=
  not_reach_of_sealed _ [.marco, .anna, .taras]
    .marco .lena (by decide) (by decide) (by decide)
-- ANCHOR_END: lena

-- ANCHOR: chain
/-- The reporting graph: an edge from each person
    to their manager, so `(taras, lena)` reads
    "Taras reports to Lena". -/
def reportsGraph (s : Store) : Graph :=
  s.reportsTo

/-- info: "yes, with a path" -/
#guard_msgs in
#eval (check (reportsGraph World.store) .marco .anna).show

/-- info: "no, with a sealed set" -/
#guard_msgs in
#eval (check (reportsGraph World.store) .taras .anna).show
-- ANCHOR_END: chain

end Ch03
