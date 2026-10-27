import Agent.Check

/-!
# Chapter 12 — solutions
-/

namespace Ch12

open Memory Agent

/-! ## Exercise 1: no cycles in the reporting line -/

/-- The managers above `p`, following at most `n` steps. -/
def climb (s : Store) : Person → Nat → List Person
  | _, 0 => []
  | p, n + 1 =>
    match s.reportsTo.find? (·.1 == p) with
    | some (_, m) => m :: climb s m n
    | none => []

def allPeople : List Person :=
  [.anna, .marco, .lena, .taras, .sofia]

/-- Nobody is their own (indirect) manager. Five people,
    so five steps are enough to find any cycle. -/
def Acyclic (s : Store) : Prop :=
  ∀ p ∈ allPeople, p ∉ climb s p allPeople.length

instance (s : Store) : Decidable (Acyclic s) := by
  unfold Acyclic; infer_instance

/-- `addReport` plus the new check. -/
def addReport' (m : Certified) (p q : Person) :
    Except String Certified :=
  match addReport m p q with
  | .error v => .error (axiomName v)
  | .ok m' =>
    if Acyclic m'.store then .ok m' else .error "Acyclic"

/-- info: ["Acyclic", "ok"] -/
#guard_msgs in
#eval [addReport' World.memory .anna .marco,
       addReport' World.memory .lena .anna].map fun
  | .ok _    => "ok"
  | .error e => e

/-! ## Exercise 2: an attendee listed twice -/

/-- A parse-level check: reject duplicate attendees. -/
def noDuplicates (e : Event) : Except String Event :=
  if e.who.Nodup then .ok e
  else .error s!"an attendee is listed twice in #{e.id}"

/-- info: Except.error "an attendee is listed twice in #1" -/
#guard_msgs in
#eval (noDuplicates { World.kickoff with
         who := [.anna, .anna] }).map (·.id)

/-! ## Exercise 3: a forged certificate -/

-- Anna and Taras were on the review *call*: not a physical
-- meeting, so the claim is false and `decide` refuses it.
/--
error: Tactic `decide` proved that the proposition
  MetAt World.store Person.anna Person.taras 2
is false
-/
#guard_msgs in
example : MetAt World.store .anna .taras 2 := by decide

end Ch12
