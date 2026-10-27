import Knowledge.Memory

/-!
# Chapter 5: the boundary pattern

Input from outside the agent is open-world: fields may be
missing and attendance may be unknown. A `Report` says so
honestly with `Option` and a three-valued `Belief`. The
boundary turns a report into an `Event` only when nothing
is left open, then hands it to `Certified.insert`. Only
certified facts enter the closed-world store.
-/

namespace Ch05

open Memory Memory.World

-- ANCHOR: belief
/-- What an outside source says about one fact:
    three answers, not two. -/
inductive Belief where
  | yes | no | unknown
  deriving DecidableEq, Repr
-- ANCHOR_END: belief

-- ANCHOR: report
/-- An event as it arrives from outside: from an LLM,
    another agent, or a calendar feed. -/
structure Report where
  id      : Nat
  kind    : EventKind
  place   : Option City
  start   : Option Time
  stop    : Option Time
  present : Person → Belief
-- ANCHOR_END: report

-- ANCHOR: rejection
/-- Why a report did not enter memory. -/
inductive Rejection where
  | missing (field : String)
  | backwards
  | undecided (p : Person)
  | violates (v : Violation)
  deriving Repr
-- ANCHOR_END: rejection

/-- The people the agent knows (the type is closed,
    so this list can be complete). -/
def roster : List Person :=
  [.anna, .marco, .lena, .taras, .sofia]

-- ANCHOR: to_event
/-- Close a report: every field present, the span the
    right way round, and every person decided. -/
def Report.toEvent (r : Report) :
    Except Rejection Event := do
  let some place := r.place
    | throw (.missing "place")
  let some start := r.start
    | throw (.missing "start")
  let some stop := r.stop
    | throw (.missing "stop")
  if h : start ≤ stop then
    match roster.find? (r.present · == .unknown) with
    | some p => throw (.undecided p)
    | none =>
      let who := roster.filter (r.present · == .yes)
      pure { id := r.id, kind := r.kind, who, place
             span := ⟨start, stop, h⟩ }
  else throw .backwards
-- ANCHOR_END: to_event

-- ANCHOR: ingest
/-- The only door into memory: close the report, then
    let the certified store check the axioms. -/
def ingest (m : Certified) (r : Report) :
    Except Rejection Certified := do
  let e ← r.toEvent
  match m.insert e with
  | .ok m'   => pure m'
  | .error v => throw (.violates v)
-- ANCHOR_END: ingest

-- ANCHOR: reports
/-- Marco's calendar: a complete record. -/
def lunch : Report :=
  { id := 3, kind := .meeting, place := some .porto
    start := some (day 2001 + hour 12)
    stop  := some (day 2001 + hour 13)
    present := fun
      | .marco | .taras => .yes
      | _ => .no }

/-- An LLM summary: "Anna and Lena met in Berlin;
    Taras may have joined." -/
def maybeTaras : Report :=
  { id := 4, kind := .meeting, place := some .berlin
    start := some (day 2002 + hour 9)
    stop  := some (day 2002 + hour 10)
    present := fun
      | .anna | .lena => .yes
      | .taras => .unknown
      | _ => .no }

/-- "Anna had a meeting at noon." Where? -/
def noPlace : Report :=
  { id := 5, kind := .meeting, place := none
    start := some (day 2003 + hour 12)
    stop  := some (day 2003 + hour 13)
    present := fun
      | .anna => .yes
      | _ => .no }

/-- The phantom again, now as an outside report. -/
def phantomReport : Report :=
  { id := 6, kind := .meeting, place := some .berlin
    start := some (day 2000 + hour 10)
    stop  := some (day 2000 + hour 12)
    present := fun
      | .anna | .lena => .yes
      | _ => .no }
-- ANCHOR_END: reports

-- ANCHOR: run
/-- What the boundary says about one report. -/
def verdict (r : Report) : String :=
  match ingest memory r with
  | .ok m    => s!"{r.id}: stored, {m.events.length} events"
  | .error x => s!"{r.id}: refused, {repr x}"

/--
info: 3: stored, 3 events
4: refused, Ch05.Rejection.undecided (Memory.Person.taras)
5: refused, Ch05.Rejection.missing "place"
6: refused, Ch05.Rejection.violates
  (Memory.Violation.noBilocation)
-/
#guard_msgs (whitespace := lax) in
#eval for r in [lunch, maybeTaras, noPlace,
                phantomReport] do
  IO.println (verdict r)
-- ANCHOR_END: run

-- ANCHOR: ask
/-- Ask the closed store about attendance. A recorded
    event answers yes or no. An event the agent never
    recorded lies outside its record: unknown. -/
def ask (m : Certified) (id : Nat) (p : Person) :
    Belief :=
  match m.events.find? (·.id == id) with
  | some e => if p ∈ e.who then .yes else .no
  | none   => .unknown

/--
info: [Ch05.Belief.yes, Ch05.Belief.no,
  Ch05.Belief.unknown]
-/
#guard_msgs (whitespace := lax) in
#eval [ask memory 1 .anna, ask memory 1 .lena,
       ask memory 9 .lena]
-- ANCHOR_END: ask

-- ANCHOR: claim
/-- Another agent's claim conflicts with our record
    when one says yes and the other says no. -/
def conflicts (m : Certified) (id : Nat)
    (p : Person) (claim : Belief) : Bool :=
  match ask m id p, claim with
  | .yes, .no | .no, .yes => true
  | _, _ => false

/-- info: (true, false) -/
#guard_msgs in
#eval (conflicts memory 1 .lena .yes,
       conflicts memory 9 .lena .yes)
-- ANCHOR_END: claim

end Ch05
