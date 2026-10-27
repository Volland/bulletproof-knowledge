import Knowledge.Memory

/-!
# Chapter 3: reasoning with the graph

Reachability as an inductive relation, proofs of
concrete paths, and a checker that answers "yes" or
"no" with a proof either way.
-/

namespace Ch03

open Memory

-- ANCHOR: graph
/-- A directed graph as a list of edges. -/
abbrev Graph (α : Type) := List (α × α)

/-- Who talked to whom: every ordered pair of
    distinct people at the same event. -/
def talked (s : Store) : Graph Person :=
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
/-- `Reach g a b`: there is a path from `a` to `b`. -/
inductive Reach {α : Type} (g : Graph α) :
    α → α → Prop where
  /-- every vertex reaches itself -/
  | here (a : α) : Reach g a a
  /-- take one edge, then keep going -/
  | step {a b c : α} :
      (a, b) ∈ g → Reach g b c → Reach g a c
-- ANCHOR_END: reach

-- ANCHOR: path_proof
/-- News from the kickoff can reach Taras:
    Marco talked to Anna, Anna talked to Taras. -/
theorem marco_reaches_taras :
    Reach (talked World.store) .marco .taras :=
  .step (b := .anna) (by decide)
    (.step (b := .taras) (by decide)
      (.here _))
-- ANCHOR_END: path_proof

section
variable {α : Type}

-- ANCHOR: snoc
/-- A path can be extended by one edge at the end. -/
theorem Reach.snoc {g : Graph α} {a b c : α}
    (h : Reach g a b) (e : (b, c) ∈ g) :
    Reach g a c := by
  induction h with
  | here => exact .step e (.here _)
  | step e' _ ih => exact .step e' (ih e)
-- ANCHOR_END: snoc

-- ANCHOR: closure
/-- One round: add every target of an edge
    whose source is already in `S`. -/
def expand [DecidableEq α] (g : Graph α)
    (S : List α) : List α :=
  S ++ (g.filter fun p => p.1 ∈ S).map (·.2)

/-- Repeat `n` rounds, starting from `S`. -/
def closure [DecidableEq α] (g : Graph α) :
    Nat → List α → List α
  | 0,     S => S
  | n + 1, S => closure g n (expand g S)
-- ANCHOR_END: closure

-- ANCHOR: sound
/-- Everything the closure collects is reachable. -/
theorem closure_sound [DecidableEq α]
    {g : Graph α} {a : α} :
    ∀ (n : Nat) (S : List α),
      (∀ x ∈ S, Reach g a x) →
      ∀ x ∈ closure g n S, Reach g a x := by
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
    · exact (h y hy).snoc he
-- ANCHOR_END: sound

theorem closure_keeps [DecidableEq α]
    {g : Graph α} {a : α} :
    ∀ (n : Nat) (S : List α),
      a ∈ S → a ∈ closure g n S := by
  intro n
  induction n with
  | zero => intro S h; exact h
  | succ n ih =>
    intro S h
    exact ih _ (List.mem_append_left _ h)

-- ANCHOR: closed
/-- `S` is closed: no edge leaves it. -/
def Closed (g : Graph α) (S : List α) : Prop :=
  ∀ p ∈ g, p.1 ∈ S → p.2 ∈ S

instance [DecidableEq α] (g : Graph α) (S : List α) :
    Decidable (Closed g S) := by
  unfold Closed; infer_instance

/-- If `a` is inside a closed set and `b` is
    outside it, no path leads from `a` to `b`. -/
theorem not_reach_of_closed {g : Graph α}
    {S : List α} {a b : α} (hc : Closed g S)
    (ha : a ∈ S) (hb : b ∉ S) : ¬ Reach g a b := by
  intro h
  induction h with
  | here => exact hb ha
  | step e _ ih => exact ih (hc _ e ha) hb
-- ANCHOR_END: closed

-- ANCHOR: verdict
/-- An answer that carries its evidence. -/
inductive Verdict (P : Prop) where
  | yes (h : P)
  | no  (h : ¬ P)
  | gaveUp

def Verdict.show {P : Prop} : Verdict P → String
  | .yes _  => "yes, with a path"
  | .no _   => "no, with a closed set"
  | .gaveUp => "out of fuel"

/-- Decide reachability on a finite graph. -/
def check [DecidableEq α] (g : Graph α) (a b : α) :
    Verdict (Reach g a b) :=
  let S := closure g (g.length + 1) [a]
  if hb : b ∈ S then
    .yes (closure_sound _ [a]
      (by simp; exact .here a) b hb)
  else if hc : Closed g S then
    .no (not_reach_of_closed hc
      (closure_keeps _ _ (by simp)) hb)
  else .gaveUp
-- ANCHOR_END: verdict

end

-- ANCHOR: ask
/-- info: "yes, with a path" -/
#guard_msgs in
#eval (check (talked World.store) .marco .taras).show

/-- info: "no, with a closed set" -/
#guard_msgs in
#eval (check (talked World.store) .marco .lena).show
-- ANCHOR_END: ask

-- ANCHOR: lena
/-- Nobody the agent recorded ever talked to Lena.
    The closed set `[marco, anna, taras]` is the
    whole proof; `decide` checks its three sides. -/
theorem marco_not_reaches_lena :
    ¬ Reach (talked World.store) .marco .lena :=
  not_reach_of_closed
    (S := [.marco, .anna, .taras])
    (by decide) (by decide) (by decide)
-- ANCHOR_END: lena

-- ANCHOR: chain
/-- Management chains: the transitive part of
    `reportsTo`, read as a graph. -/
def manages (s : Store) : Graph Person :=
  s.reportsTo

/-- info: "no, with a closed set" -/
#guard_msgs in
#eval (check (manages World.store) .taras .anna).show
-- ANCHOR_END: chain

end Ch03
