import Agent.Json

/-!
# The checker

Two jobs, both in Lean:

1. *Facts.* Every proposed fact goes through a certified
   insert. A rejection names the broken axiom, and a plain
   function turns it into feedback text for the LLM.
2. *Answers.* Every claim the agent makes about its memory
   is a decidable proposition, and the agent states it only
   when the decision procedure returns a proof.
-/

namespace Agent

open Memory

/-! ## Facts -/

-- ANCHOR: add_report
/-- Reporting lines are not events, so `Certified.insert`
    does not cover them. Same pattern: change the store,
    decide `Consistent`, keep the proof or name the axiom. -/
def addReport (m : Certified) (p q : Person) :
    Except Violation Certified :=
  let s' := { m.store with
              reportsTo := (p, q) :: m.store.reportsTo }
  if h : Consistent s' then .ok ⟨s', h⟩
  else .error ((diagnose s').getD .singleManager)

def Fact.insert (m : Certified) :
    Fact → Except Violation Certified
  | .event e     => m.insert e
  | .reports p q => addReport m p q
-- ANCHOR_END: add_report

-- ANCHOR: commit
/-- Where a batch of facts failed: the store at that point,
    the fact, and the axiom it would break. -/
structure Rejection where
  store  : Store
  index  : Nat
  fact   : Fact
  broken : Violation

/-- Insert all facts or none. `m` is an immutable value,
    so "none" simply means: keep the old `m`. -/
def commit (m : Certified) (facts : List Fact) :
    Except Rejection Certified :=
  go m (facts.zip (List.range facts.length))
where
  go (m : Certified) :
      List (Fact × Nat) → Except Rejection Certified
    | [] => .ok m
    | (f, i) :: rest =>
      match f.insert m with
      | .ok m'   => go m' rest
      | .error v => .error ⟨m.store, i + 1, f, v⟩
-- ANCHOR_END: commit

/-! ## Feedback for the LLM -/

def axiomName : Violation → String
  | .bornBefore    => "BornBefore"
  | .noBilocation  => "NoBilocation"
  | .singleManager => "SingleManager"
  | .uniqueIds     => "UniqueIds"

def statement : Violation → String
  | .bornBefore    => "nobody attends an event before \
                       they are born"
  | .noBilocation  => "nobody is physically in two \
                       cities at overlapping times"
  | .singleManager => "each person reports to at most \
                       one manager"
  | .uniqueIds     => "event identifiers are unique"

def names (ps : List Person) : String :=
  ", ".intercalate (ps.map people.name)

/-- `#3 meeting in berlin, day 2000 10:00-12:00: anna, lena` -/
def showSpan (i : Interval) : String :=
  let (a, b) := (showTime i.start, showTime i.stop)
  if i.start / 1440 == i.stop / 1440
  then s!"{a}-{(b.splitOn " ").getLastD b}" else s!"{a} to {b}"

def describeEvent (e : Event) : String :=
  s!"#{e.id} {kinds.name e.kind} in {cities.name e.place}, \
     {showSpan e.span}: {names e.who}"

def Fact.describe : Fact → String
  | .event e     => describeEvent e
  | .reports p q =>
    s!"{people.name p} reports to {people.name q}"

def nextId (s : Store) : Nat :=
  (s.events.map (·.id)).foldl max 0 + 1

-- ANCHOR: explain
/-- The evidence behind a rejection, in words. This text is
    advice for the LLM; nothing here needs to be trusted,
    because the accept/reject decision was already made by
    `Certified.insert`. -/
def explain (s : Store) : Fact → Violation → String
  | .event e, .bornBefore =>
    let early := e.who.filter fun p =>
      e.span.start < s.born p
    String.intercalate "; " <| early.map fun p =>
      s!"{people.name p} is born at {showTime (s.born p)}"
  | .event e, .noBilocation =>
    let clash := s.events.filter fun e₂ =>
      e₂.kind.physical && e.kind.physical &&
      e₂.place != e.place &&
      decide (Interval.Overlaps e.span e₂.span) &&
      e.who.any (· ∈ e₂.who)
    String.intercalate "; " <| clash.map fun e₂ =>
      s!"{names (e.who.filter (· ∈ e₂.who))} \
         already at {describeEvent e₂}"
  | .event e, .uniqueIds =>
    s!"id {e.id} is taken; the next free id is {nextId s}"
  | .reports p _, .singleManager =>
    let ms := (s.reportsTo.filter (·.1 == p)).map (·.2)
    s!"{people.name p} already reports to {names ms}"
  | _, v => statement v
-- ANCHOR_END: explain

-- ANCHOR: feedback
def Rejection.reason (r : Rejection) : String :=
  s!"REJECTED. Fact {r.index} ({r.fact.describe}) violates \
     the axiom {axiomName r.broken}: {statement r.broken}. \
     Evidence: {explain r.store r.fact r.broken}."

def ParseError.reason (e : ParseError) : String :=
  let hint := match e with
    | .unknown "person" _ =>
      s!" Known people: {", ".intercalate people.names}."
    | .unknown "city" _ =>
      s!" Known cities: {", ".intercalate cities.names}."
    | _ => ""
  s!"UNPARSABLE: {e.explain}.{hint}"

/-- Appended to every reason before it goes to the LLM. -/
def instruction : String :=
  "Nothing was recorded. Reply with one corrected JSON \
   object and no other text. Leave out anything the \
   user's message does not state."
-- ANCHOR_END: feedback

/-! ## Claims the agent may make -/

-- ANCHOR: claims
/-- `p` and `q` were both at the physical event `i`. -/
def MetAt (s : Store) (p q : Person) (i : Nat) : Prop :=
  ∃ e ∈ s.events, e.id = i ∧ e.kind.physical = true ∧
    p ∈ e.who ∧ q ∈ e.who ∧ p ≠ q

/-- Everyone `p` met in person is in `qs`. -/
def MetOnly (s : Store) (p : Person)
    (qs : List Person) : Prop :=
  ∀ e ∈ s.events, e.kind.physical = true → p ∈ e.who →
    ∀ q ∈ e.who, q = p ∨ q ∈ qs

/-- `p` was in a city of country `c` during event `i`. -/
def InCountryAt (s : Store) (p : Person) (c : Country)
    (i : Nat) : Prop :=
  ∃ e ∈ s.events, e.id = i ∧ e.kind.physical = true ∧
    p ∈ e.who ∧ e.place.country = c

/-- No recorded event puts `p` in country `c`. -/
def NeverIn (s : Store) (p : Person) (c : Country) : Prop :=
  ∀ e ∈ s.events, e.kind.physical = true → p ∈ e.who →
    e.place.country ≠ c

def AttendedAt (s : Store) (p : Person) (i : Nat) : Prop :=
  ∃ e ∈ s.events, e.id = i ∧ p ∈ e.who

/-- Event `i` is recorded and `p` is not among its
    attendees. -/
def AbsentAt (s : Store) (p : Person) (i : Nat) : Prop :=
  ∃ e ∈ s.events, e.id = i ∧ p ∉ e.who
-- ANCHOR_END: claims

/-! Each claim is decidable, by the same one-line proofs
    as the axioms in `Memory.Axioms`. -/
section
variable (s : Store) (p q : Person) (i : Nat)
  (c : Country) (qs : List Person)
instance : Decidable (MetAt s p q i) := by
  unfold MetAt; infer_instance
instance : Decidable (MetOnly s p qs) := by
  unfold MetOnly; infer_instance
instance : Decidable (InCountryAt s p c i) := by
  unfold InCountryAt; infer_instance
instance : Decidable (NeverIn s p c) := by
  unfold NeverIn; infer_instance
instance : Decidable (AttendedAt s p i) := by
  unfold AttendedAt; infer_instance
instance : Decidable (AbsentAt s p i) := by
  unfold AbsentAt; infer_instance
end

-- ANCHOR: chain
/-- `ms` is the complete management chain above `p`:
    each step is a recorded reporting line, and the last
    manager reports to nobody. -/
def Chain (s : Store) : Person → List Person → Prop
  | p, []      => ∀ r ∈ s.reportsTo, r.1 ≠ p
  | p, m :: ms => (p, m) ∈ s.reportsTo ∧ Chain s m ms
-- ANCHOR_END: chain

/-- Decide `Chain` by walking the list, step by step. -/
instance chainDec (s : Store) :
    (p : Person) → (ms : List Person) →
    Decidable (Chain s p ms)
  | p, [] =>
    inferInstanceAs (Decidable (∀ r ∈ s.reportsTo, r.1 ≠ p))
  | p, m :: ms =>
    have := chainDec s m ms
    inferInstanceAs (Decidable ((p, m) ∈ s.reportsTo ∧ _))

-- ANCHOR: cert
/-- A certificate: a claim about the store `s`, a readable
    rendering of it, and a proof. -/
structure Cert (s : Store) where
  text  : String
  claim : Prop
  proof : claim

/-- Ask the decision procedure. A certificate exists only
    if it returns a proof. -/
def certify (s : Store) (text : String) (P : Prop)
    [Decidable P] : Option (Cert s) :=
  if h : P then some ⟨text, P, h⟩ else none
-- ANCHOR_END: cert

/-! ## Why a "no" can be trusted -/

theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (hab ▸ List.mem_map_of_mem hb') h.1
    · exact absurd (hab.symm ▸ List.mem_map_of_mem ha') h.1
    · exact eq_of_mem_of_nodup_map h.2 ha' hb' hab

-- ANCHOR: absent_sound
/-- In a consistent store, "event `i` is recorded and `p`
    is not on it" really means "`p` did not attend `i`".
    The proof needs `UniqueIds`: with two events numbered
    `i`, one could list `p` and the other not. -/
theorem absent_sound {s : Store} {p : Person} {i : Nat}
    (ok : Consistent s) (h : AbsentAt s p i) :
    ¬ AttendedAt s p i := by
  intro ⟨e₁, m₁, id₁, att⟩
  obtain ⟨e₂, m₂, id₂, nat⟩ := h
  have : e₁ = e₂ :=
    eq_of_mem_of_nodup_map ok.uniqueIds m₁ m₂
      (id₁.trans id₂.symm)
  exact nat (this ▸ att)
-- ANCHOR_END: absent_sound

end Agent

namespace Agent
open Memory

-- ANCHOR: commit_demo
/-- The phantom from Chapter 1, sent through `commit`. -/
def phantomVerdict : String :=
  match commit World.memory [.event World.phantom] with
  | .ok _    => "accepted"
  | .error r => s!"{axiomName r.broken}: \
                   {explain r.store r.fact r.broken}"

/--
info: "NoBilocation: anna already at #1 meeting in lisbon,
  day 2000 10:00-11:00: anna, marco"
-/
#guard_msgs (whitespace := lax) in
#eval phantomVerdict
-- ANCHOR_END: commit_demo

end Agent
