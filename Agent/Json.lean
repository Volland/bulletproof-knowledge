import Lean.Data.Json
import Knowledge.Memory

/-!
# From LLM text to typed facts

The LLM replies with text. This module turns that text into
values of the memory's types, or into a typed `ParseError`.
Parsing is the first checker: a reply that names an unknown
person, or a span that ends before it starts, never becomes
an `Event` at all.
-/

namespace Agent

open Lean Memory

-- ANCHOR: vocab
/-- The names the LLM may use for the values of a closed
    type, one entry per value. -/
structure Vocab (α : Type) where
  entries : List (String × α)

namespace Vocab
variable {α : Type}

def parse? (v : Vocab α) (s : String) : Option α :=
  v.entries.lookup s

def name [BEq α] (v : Vocab α) (a : α) : String :=
  match v.entries.find? (·.2 == a) with
  | some (n, _) => n
  | none        => "?"

def names (v : Vocab α) : List String :=
  v.entries.map (·.1)
end Vocab

def people : Vocab Person :=
  ⟨[("anna", .anna), ("marco", .marco), ("lena", .lena),
    ("taras", .taras), ("sofia", .sofia)]⟩
-- ANCHOR_END: vocab

def cities : Vocab City :=
  ⟨[("kyiv", .kyiv), ("lviv", .lviv),
    ("lisbon", .lisbon), ("porto", .porto),
    ("berlin", .berlin)]⟩

def countries : Vocab Country :=
  ⟨[("ukraine", .ukraine), ("portugal", .portugal),
    ("germany", .germany)]⟩

def kinds : Vocab EventKind :=
  ⟨[("meeting", .meeting), ("call", .call),
    ("talk", .talk), ("trip", .trip)]⟩

-- ANCHOR: vocab_complete
/-- Every person has a name, and the name parses back
    to that person: the vocabulary covers the closed
    world exactly. -/
theorem people_roundtrip (p : Person) :
    people.parse? (people.name p) = some p := by
  cases p <;> decide

theorem cities_roundtrip (c : City) :
    cities.parse? (cities.name c) = some c := by
  cases c <;> decide
-- ANCHOR_END: vocab_complete

theorem countries_roundtrip (c : Country) :
    countries.parse? (countries.name c) = some c := by
  cases c <;> decide

theorem kinds_roundtrip (k : EventKind) :
    kinds.parse? (kinds.name k) = some k := by
  cases k <;> decide

-- ANCHOR: proposal
/-- A fact the LLM wants the agent to remember. -/
inductive Fact where
  | event   (e : Event)
  | reports (who manager : Person)

/-- A question the memory can answer. -/
inductive Query where
  | met      (p : Person)
  | wasIn    (p : Person) (c : Country)
  | chain    (p : Person)
  | attended (p : Person) (id : Nat)

/-- What one LLM reply asks the agent to do. -/
inductive Proposal where
  | remember (facts : List Fact)
  | ask      (q : Query)
  /-- A question about something outside the
      vocabulary: the answer is "I don't know". -/
  | outside  (why : String)
-- ANCHOR_END: proposal

-- ANCHOR: parse_error
/-- Why a reply did not even become a proposal. -/
inductive ParseError where
  | notJson  (msg : String)
  | shape    (msg : String)
  | unknown  (what name : String)
  | badClock (text : String)
  | badSpan  (start stop : Time)
-- ANCHOR_END: parse_error

/-- `day D, HH:MM`, for messages and transcripts. -/
def showTime (t : Time) : String :=
  let d := t / 1440
  let m := t % 1440
  let pad (n : Nat) :=
    if n < 10 then s!"0{n}" else toString n
  s!"day {d} {pad (m / 60)}:{pad (m % 60)}"

def ParseError.explain : ParseError → String
  | .notJson m => s!"the reply is not JSON ({m})"
  | .shape m => s!"the JSON has the wrong shape: {m}"
  | .unknown w n => s!"unknown {w} \"{n}\""
  | .badClock t => s!"\"{t}\" is not a clock time HH:MM"
  | .badSpan a b =>
    s!"the span ends ({showTime b}) before it \
       starts ({showTime a})"

/-- Parsing can fail with a `ParseError`. -/
abbrev Parse := Except ParseError

-- ANCHOR: fields
def field (j : Json) (k : String) : Parse Json :=
  match j.getObjVal? k with
  | .ok v    => pure v
  | .error _ => throw (.shape s!"missing field \"{k}\"")

def str (j : Json) (k : String) : Parse String := do
  match (← field j k).getStr? with
  | .ok s    => pure s
  | .error _ => throw (.shape s!"\"{k}\" is not a string")

def nat (j : Json) (k : String) : Parse Nat := do
  match (← field j k).getNat? with
  | .ok n    => pure n
  | .error _ => throw (.shape s!"\"{k}\" is not a number")

def strs (j : Json) (k : String) : Parse (List String) := do
  match (← field j k).getArr? with
  | .error _ => throw (.shape s!"\"{k}\" is not a list")
  | .ok xs => xs.toList.mapM fun x =>
    match x.getStr? with
    | .ok s    => pure s
    | .error _ => throw (.shape s!"\"{k}\" has a non-string")

/-- Look a name up in a vocabulary; unknown is an error. -/
def entity {α : Type} (v : Vocab α) (what : String)
    (s : String) : Parse α :=
  match v.parse? s with
  | some a => pure a
  | none   => throw (.unknown what s)
-- ANCHOR_END: fields

-- ANCHOR: span
/-- `"HH:MM"` to minutes after midnight. -/
def clock (s : String) : Parse Nat :=
  match s.splitOn ":" with
  | [h, m] =>
    match h.toNat?, m.toNat? with
    | some h, some m =>
      if h < 24 ∧ m < 60 then pure (60 * h + m)
      else throw (.badClock s)
    | _, _ => throw (.badClock s)
  | _ => throw (.badClock s)

/-- The only way to get an `Interval` is to supply the
    proof `start ≤ stop`; `if h : …` produces it. -/
def interval (start stop : Time) : Parse Interval :=
  if h : start ≤ stop then pure ⟨start, stop, h⟩
  else throw (.badSpan start stop)
-- ANCHOR_END: span

-- ANCHOR: event
def parseEvent (j : Json) : Parse Event := do
  let id    ← nat j "id"
  let kind  ← entity kinds "event kind" (← str j "kind")
  let who   ← (← strs j "who").mapM (entity people "person")
  let place ← entity cities "city" (← str j "place")
  let d     ← nat j "day"
  let t₁    ← clock (← str j "from")
  let t₂    ← clock (← str j "to")
  let span  ← interval (World.day d + t₁) (World.day d + t₂)
  return { id, kind, who, place, span }
-- ANCHOR_END: event

def parseFact (j : Json) : Parse Fact := do
  if let .ok e := j.getObjVal? "event" then
    return .event (← parseEvent e)
  if let .ok r := j.getObjVal? "reportsTo" then
    let p ← entity people "person" (← str r "person")
    let m ← entity people "person" (← str r "manager")
    return .reports p m
  throw (.shape "a fact needs \"event\" or \"reportsTo\"")

def parseQuery (j : Json) : Parse Query := do
  if let .ok p := j.getObjVal? "met" then
    match p.getStr? with
    | .ok s => return .met (← entity people "person" s)
    | .error _ => throw (.shape "\"met\" takes a name")
  if let .ok p := j.getObjVal? "chain" then
    match p.getStr? with
    | .ok s => return .chain (← entity people "person" s)
    | .error _ => throw (.shape "\"chain\" takes a name")
  if let .ok w := j.getObjVal? "wasIn" then
    let p ← entity people "person" (← str w "person")
    let c ← entity countries "country" (← str w "country")
    return .wasIn p c
  if let .ok a := j.getObjVal? "attended" then
    let p ← entity people "person" (← str a "person")
    return .attended p (← nat a "event")
  throw (.shape "unknown kind of question")

-- ANCHOR: reply
/-- The whole boundary: text in, typed proposal out. -/
def parseReply (text : String) : Parse Proposal := do
  let j ← match Json.parse text with
    | .ok j    => pure j
    | .error e => throw (.notJson e)
  if let .ok fs := j.getObjVal? "facts" then
    match fs.getArr? with
    | .ok xs => return .remember (← xs.toList.mapM parseFact)
    | .error _ => throw (.shape "\"facts\" is not a list")
  if let .ok q := j.getObjVal? "ask" then
    if let .ok why := q.getObjValAs? String "unsupported" then
      return .outside why
    match parseQuery q with
    | .ok q => return .ask q
    -- an unknown name in a *question* is not an error:
    -- the honest answer is "I don't know"
    | .error (.unknown w n) =>
      return .outside s!"I have no {w} called \"{n}\""
    | .error e => throw e
  throw (.shape "expected {\"facts\": …} or {\"ask\": …}")
-- ANCHOR_END: reply

end Agent

namespace Agent

-- ANCHOR: parse_demo
def explainReply (text : String) : String :=
  match parseReply text with
  | .ok _    => "parsed"
  | .error e => e.explain

/-- info: "unknown person \"oksana\"" -/
#guard_msgs in
#eval explainReply "{\"facts\": [{\"event\": {\"id\": 7, \
  \"kind\": \"meeting\", \"who\": [\"lena\", \"oksana\"], \
  \"place\": \"lviv\", \"day\": 2004, \
  \"from\": \"10:00\", \"to\": \"11:00\"}}]}"
-- ANCHOR_END: parse_demo

/-- info: "the span ends (day 2003 04:30) before it
    starts (day 2003 15:00)" -/
#guard_msgs (whitespace := lax) in
#eval explainReply "{\"facts\": [{\"event\": {\"id\": 6, \
  \"kind\": \"meeting\", \"who\": [\"anna\"], \
  \"place\": \"porto\", \"day\": 2003, \
  \"from\": \"15:00\", \"to\": \"04:30\"}}]}"

end Agent
