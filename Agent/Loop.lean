import Agent.Llm
import Agent.Reason

/-!
# The agent loop

propose → parse → check → (feedback → retry)* → commit,
and for questions: search (ELPI) → check (Lean) → answer.
The LLM never writes to memory and never phrases an answer.
-/

namespace Agent

open Memory
open Elpi (Solution)

/-! ## Printing -/

/-- Greedy word wrap. -/
def wrap (width : Nat) (text : String) : List String :=
  let words := (text.splitOn " ").filter (· ≠ "")
  let step := fun (acc : List String × String) w =>
    let (ls, cur) := acc
    if cur.isEmpty then (ls, w)
    else if cur.length + 1 + w.length ≤ width
    then (ls, cur ++ " " ++ w)
    else (ls ++ [cur], w)
  let (ls, cur) := words.foldl step ([], "")
  if cur.isEmpty then ls else ls ++ [cur]

/-- One transcript entry: a tag column, then wrapped text,
    64 columns in all. -/
def say (tag text : String) : IO Unit := do
  let pad := "".pushn ' ' (7 - tag.length)
  match wrap 57 text with
  | [] => IO.println tag
  | l :: ls =>
    IO.println (tag ++ pad ++ l)
    for l in ls do IO.println ("       " ++ l)

def Query.describe : Query → String
  | .met p => s!"met({people.name p})"
  | .chain p => s!"chain({people.name p})"
  | .wasIn p c =>
    s!"wasIn({people.name p}, {countries.name c})"
  | .attended p i => s!"attended({people.name p}, #{i})"

def Proposal.describe : Proposal → String
  | .remember fs =>
    "; ".intercalate (fs.map Fact.describe)
  | .ask q => s!"ask {q.describe}"
  | .outside why => s!"ask (outside the memory): {why}"

/-! ## The prompt -/

-- ANCHOR: prompt
/-- The system prompt is built from the same vocabularies
    the parser uses, so the two cannot drift apart. -/
def systemPrompt (s : Store) : String :=
  let list := ", ".intercalate
  "\n".intercalate <| [
    "You turn the user's message into JSON for the memory \
     of an assistant agent. Reply with exactly one JSON \
     object and nothing else.",
    "To record facts: {\"facts\": [F, ...]}, F is \
     {\"event\": {\"id\": N, \"kind\": K, \"who\": [P], \
     \"place\": C, \"day\": D, \"from\": \"HH:MM\", \
     \"to\": \"HH:MM\"}} or {\"reportsTo\": \
     {\"person\": P, \"manager\": P}}.",
    "To ask: {\"ask\": Q}, Q is {\"met\": P}, \
     {\"chain\": P}, {\"wasIn\": {\"person\": P, \
     \"country\": X}}, {\"attended\": {\"person\": P, \
     \"event\": N}}, or {\"unsupported\": \"why\"}.",
    s!"People P: {list people.names}.",
    s!"Cities C: {list cities.names}.",
    s!"Countries X: {list countries.names}.",
    s!"Kinds K: {list kinds.names}.",
    "Recorded events:"] ++
    s.events.reverse.map describeEvent ++
    ["Reporting lines:"] ++
    s.reportsTo.map (fun (p, m) =>
      s!"{people.name p} reports to {people.name m}") ++
    [s!"The next free event id is {nextId s}."]
-- ANCHOR_END: prompt

/-! ## Answers -/

-- ANCHOR: answer_type
/-- Three answers, and two of them carry certificates.
    `unknown` is the boundary of the closed world. -/
inductive Answer (s : Store) where
  | yes     (text : String) (certs : List (Cert s))
  | no      (text : String) (cert : Cert s)
  | unknown (why : String)
-- ANCHOR_END: answer_type

def Answer.verdict {s : Store} : Answer s → String
  | .yes .. => "yes" | .no .. => "no"
  | .unknown _ => "unknown"

def Answer.certs {s : Store} : Answer s → List (Cert s)
  | .yes _ cs => cs | .no _ c => [c] | .unknown _ => []

/-- Lean syntax for a person, as in `.anna`. -/
def lp (p : Person) : String := "." ++ people.name p

def lps (ps : List Person) : String :=
  "[" ++ ", ".intercalate (ps.map lp) ++ "]"

/-- `a`, `a and b`, `a, b and c`. -/
def andList : List String → String
  | [] => "nobody"
  | [a] => a
  | xs => ", ".intercalate xs.dropLast ++ " and " ++
          xs.getLastD ""

/-- Print what the decision procedure said about a claim. -/
def report {s : Store} (text : String) :
    Option (Cert s) → IO Unit
  | some _ => say "lean" s!"{text}: proved"
  | none   => say "lean" s!"{text}: NOT provable"

/-- The decoded solutions, or the first engine error. -/
def decodeAll {α : Type} (sols : List (Except Elpi.ElpiError
    Solution)) (f : Solution → Option α) :
    Except String (List α) :=
  sols.foldr (init := .ok []) fun
    | .ok sol, .ok xs =>
      match f sol with
      | some x => .ok (x :: xs)
      | none   => .error "undecodable solution"
    | .error e, _ => .error (toString e)
    | _, .error e => .error e

-- ANCHOR: answer_met
/-- ELPI proposes who met `p`; Lean checks each pair and
    then checks that nobody is missing from the list. -/
def answerMet (r : Reasoner) (s : Store) (p : Person) :
    IO (Answer s) := do
  let sols ← r.run (solve s s!"met {people.name p} Q E")
  let pair (sol : Solution) : Option (Person × Nat) :=
    match sol.get? "Q", sol.get? "E" with
    | some q, some i => some (q, i)
    | _, _ => none
  let .ok found := decodeAll sols pair
    | return .unknown "the search failed"
  say "elpi" <| s!"{found.length} solutions: " ++
    ", ".intercalate (found.map fun (q, i) =>
      s!"{people.name q} #{i}")
  -- one witness per person is enough
  let firsts := found.foldl (init := []) fun acc (q, i) =>
    if acc.any (·.1 == q) then acc else acc ++ [(q, i)]
  let mut certs : List (Cert s) := []
  let mut qs : List Person := []
  for (q, i) in firsts do
    let text := s!"MetAt store {lp p} {lp q} {i}"
    let c := certify s text (MetAt s p q i)
    report text c
    if let some c := c then
      certs := certs ++ [c]; qs := qs ++ [q]
  let text := s!"MetOnly store {lp p} {lps qs}"
  let only := certify s text (MetOnly s p qs)
  report text only
  let who := andList <| firsts.filterMap fun (q, i) =>
    if q ∈ qs then some s!"{people.name q} (#{i})" else none
  match only, qs with
  | none, _ => return .unknown "the search missed someone"
  | some c, [] =>
    return .no s!"{people.name p} met nobody in person." c
  | some c, _ =>
    return .yes s!"{people.name p} met {who} in person, \
                   and nobody else." (certs ++ [c])
-- ANCHOR_END: answer_met

-- ANCHOR: answer_was_in
def answerWasIn (r : Reasoner) (s : Store) (p : Person)
    (c : Country) : IO (Answer s) := do
  let (pn, cn) := (people.name p, countries.name c)
  let sols ← r.run (solve s s!"was_in {pn} {cn} E" 1)
  let .ok found := decodeAll sols (·.get? "E" : _ → Option Nat)
    | return .unknown "the search failed"
  match found with
  | i :: _ =>
    say "elpi" s!"E = {i}"
    let text := s!"InCountryAt store {lp p} .{cn} {i}"
    let cert := certify s text (InCountryAt s p c i)
    report text cert
    match cert with
    | some k =>
      return .yes s!"Yes: {pn} was in {cn} during #{i}." [k]
    | none   => return .unknown "ELPI's witness did not check"
  | [] =>
    -- negation as failure is not a proof; the closed
    -- world plus a decision procedure is
    say "elpi" "no solution"
    let text := s!"NeverIn store {lp p} .{cn}"
    let cert := certify s text (NeverIn s p c)
    report text cert
    match cert with
    | some k =>
      return .no s!"No: no recorded event puts {pn} \
                    in {cn}." k
    | none => return .unknown "the search missed an event"
-- ANCHOR_END: answer_was_in

def answerChain (r : Reasoner) (s : Store) (p : Person) :
    IO (Answer s) := do
  let sols ← r.run (solve s s!"chain {people.name p} L" 1)
  match decodeAll sols (·.get? "L" : _ → Option (List Person))
  with
  | .error e => return .unknown s!"the search failed: {e}"
  | .ok [] => return .unknown "the search found no chain"
  | .ok (ms :: _) =>
    say "elpi" s!"L = [{names ms}]"
    let text := s!"Chain store {lp p} {lps ms}"
    let cert := certify s text (Chain s p ms)
    report text cert
    let steps := (p :: ms).zip ms |>.map fun (a, b) =>
      s!"{people.name a} reports to {people.name b}"
    let top := (ms.getLast?).getD p
    match cert with
    | some k =>
      return .yes ("; ".intercalate steps ++
        s!"; {people.name top} reports to nobody.") [k]
    | none => return .unknown "ELPI's chain did not check"

def answerAttended (s : Store) (p : Person) (i : Nat) :
    IO (Answer s) := do
  let pn := people.name p
  let yes := s!"AttendedAt store {lp p} {i}"
  if let some k := certify s yes (AttendedAt s p i) then
    report yes (some k)
    return .yes s!"Yes: {pn} attended #{i}." [k]
  let no := s!"AbsentAt store {lp p} {i}"
  if let some k := certify s no (AbsentAt s p i) then
    report no (some k)
    return .no s!"No: #{i} is recorded and {pn} is \
                  not on it." k
  return .unknown s!"no event #{i} is recorded"

def answer (r : Reasoner) (s : Store) :
    Query → IO (Answer s)
  | .met p        => answerMet r s p
  | .wasIn p c    => answerWasIn r s p c
  | .chain p      => answerChain r s p
  | .attended p i => answerAttended s p i

/-! ## One turn -/

-- ANCHOR: outcome
/-- What a turn did, for the transcript and for evaluation:
    one verdict per attempt, the new memory, and the
    certificates of any answer. -/
structure Outcome where
  memory   : Certified
  verdicts : List String
  certs    : List String
-- ANCHOR_END: outcome

-- ANCHOR: attempt
/-- At most `fuel` attempts. Each failed attempt appends the
    LLM's reply and our feedback to the conversation. -/
def attempt (llm : Provider) (r : Reasoner) (m : Certified)
    (verdicts : List String) :
    (fuel : Nat) → List Msg → IO Outcome
  | 0, _ => do
    say "agent" "I could not record that. Memory unchanged."
    return ⟨m, verdicts ++ ["gave up"], []⟩
  | fuel + 1, msgs => do
    let .ok reply ← llm.complete (systemPrompt m.store) msgs
      | say "agent" "The model is unavailable."
        return ⟨m, verdicts ++ ["no reply"], []⟩
    let retry (verdict reason : String) := do
      say "check" reason
      let feedback := reason ++ " " ++ instruction
      attempt llm r m (verdicts ++ [verdict]) fuel
        (msgs ++ [⟨"assistant", reply⟩, ⟨"user", feedback⟩])
    match parseReply reply with
    | .error e =>
      say "llm" (if reply.length > 53
        then (reply.take 50).toString ++ "..." else reply)
      retry "parse" e.reason
    | .ok p =>
      say "llm" p.describe
      match p with
      | .remember facts =>
        match commit m facts with
        | .error rej =>
          retry (axiomName rej.broken) rej.reason
        | .ok m' =>
          say "check" s!"ACCEPTED. The store now has \
            {m'.store.events.length} events and a new proof \
            of Consistent."
          return ⟨m', verdicts ++ ["committed"], []⟩
      | .ask q =>
        let a ← answer r m.store q
        match a with
        | .yes t _ | .no t _ => say "agent" t
        | .unknown why => say "agent" s!"I don't know: {why}."
        return ⟨m, verdicts ++ [a.verdict],
                a.certs.map (·.text)⟩
      | .outside why =>
        say "agent" s!"I don't know: {why}."
        return ⟨m, verdicts ++ ["unknown"], []⟩
-- ANCHOR_END: attempt

/-- One user message, at most three attempts. -/
def turn (llm : Provider) (r : Reasoner) (m : Certified)
    (user : String) : IO Outcome := do
  say "user" user
  attempt llm r m [] 3 [⟨"user", user⟩]

end Agent
