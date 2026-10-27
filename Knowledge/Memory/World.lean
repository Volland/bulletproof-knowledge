import Knowledge.Memory.Certified

/-!
# A concrete world

The small, fictional world used throughout the book.
Times are minutes since the epoch; `day` and `hour`
keep the examples readable.
-/

namespace Memory.World

open Memory

def hour (h : Nat) : Time := 60 * h
def day (d : Nat) : Time := 24 * 60 * d

-- ANCHOR: world
def born : Person → Time
  | .sofia => day 1000  -- joins the world late: a trap
  | _      => 0

def kickoff : Event :=
  { id := 1, kind := .meeting
    who := [.anna, .marco], place := .lisbon
    span := .mk! (day 2000 + hour 10)
                 (day 2000 + hour 11) }

def review : Event :=
  { id := 2, kind := .call
    who := [.anna, .taras], place := .kyiv
    span := .mk! (day 2000 + hour 10)
                 (day 2000 + hour 11) }

def store : Store :=
  { born
    worksAt   := [(.anna, .acme), (.marco, .acme),
                  (.taras, .kyivTech), (.lena, .lumen)]
    reportsTo := [(.marco, .anna), (.taras, .lena)]
    events    := [review, kickoff] }
-- ANCHOR_END: world

-- ANCHOR: certify
/-- The kernel evaluates every axiom on the concrete
    store: a certificate by computation. -/
theorem store_consistent : Consistent store := by
  decide

def memory : Certified := ⟨store, store_consistent⟩
-- ANCHOR_END: certify

-- ANCHOR: hallucination
/-- An LLM "remembers" Anna in Berlin
    during the Lisbon kickoff. -/
def phantom : Event :=
  { id := 3, kind := .meeting
    who := [.anna, .lena], place := .berlin
    span := .mk! (day 2000 + hour 10)
                 (day 2000 + hour 12) }

/-- info: Except.error (Memory.Violation.noBilocation) -/
#guard_msgs in
#eval (memory.insert phantom).map (·.events.length)
-- ANCHOR_END: hallucination

end Memory.World
