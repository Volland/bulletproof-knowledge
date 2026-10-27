/-!
# An open set of people

`Memory.Person` is a closed inductive: a new person means a
new constructor and a recompile. Chapter 7 sketched the
production alternative: typed identifiers plus a proof that
each identifier is registered. This module turns that into
a store axiom. The certified-insert pattern does not
change; only the axiom does.
-/

namespace Agent.Registry

-- ANCHOR: registry
/-- A person's identifier: any string, but its own type. -/
structure PersonId where
  val : String
  deriving DecidableEq, Repr

/-- People the agent knows, and who attended which event. -/
structure OpenStore where
  people  : List PersonId
  attends : List (Nat × PersonId)

/-- The new axiom: every attendee is registered. -/
def Registered (s : OpenStore) : Prop :=
  ∀ a ∈ s.attends, a.2 ∈ s.people

instance (s : OpenStore) : Decidable (Registered s) := by
  unfold Registered; infer_instance

structure Certified where
  store : OpenStore
  ok    : Registered store

/-- Registering a person always preserves the axiom, and
    the proof says why: old attendees stay registered. -/
def Certified.register (m : Certified) (p : PersonId) :
    Certified :=
  ⟨{ m.store with people := p :: m.store.people },
   fun a h => List.mem_cons_of_mem p (m.ok a h)⟩

/-- Recording attendance is checked, exactly like
    `Memory.Certified.insert`. -/
def Certified.attend (m : Certified) (i : Nat)
    (p : PersonId) : Except String Certified :=
  let s' := { m.store with
              attends := (i, p) :: m.store.attends }
  if h : Registered s' then .ok ⟨s', h⟩
  else .error s!"{p.val} is not registered"
-- ANCHOR_END: registry

-- ANCHOR: registry_demo
def empty : Certified :=
  ⟨⟨[⟨"lena"⟩], []⟩, by decide⟩

def oksana : PersonId := ⟨"oksana"⟩

/-- info: ["oksana is not registered", "ok"] -/
#guard_msgs in
#eval [empty.attend 7 oksana,
       (empty.register oksana).attend 7 oksana].map fun
  | .ok _    => "ok"
  | .error e => e
-- ANCHOR_END: registry_demo

end Agent.Registry
