import Agent.Export

/-!
# `lake exe agent`

Replays the scripted session in `replay/` (the default:
offline, deterministic, used in CI), or runs the same user
messages against the real model with `--live`.

    lake exe agent                  -- replay
    lake exe agent --live           -- Anthropic API
    lake exe agent --certs out.lean -- export certificates
-/

open Lean Memory Agent

-- ANCHOR: scenario
/-- One recorded turn: the user's message, the LLM replies
    in order, and the verdicts we expect, one per attempt. -/
structure Scenario where
  file    : String
  user    : String
  replies : List String
  expect  : List String

def loadScenario (path : System.FilePath) : IO Scenario := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let get {α : Type} [FromJson α] (k : String) : IO α :=
    IO.ofExcept (j.getObjValAs? α k)
  -- a reply is recorded as JSON when it was JSON,
  -- and as a string when it was not
  let replies := (← get (α := Array Json) "replies").toList
    |>.map fun | .str s => s | r => r.compress
  return { file := path.fileName.getD "?", replies,
           user := ← get "user", expect := ← get "expect" }
-- ANCHOR_END: scenario

def loadScript (dir : System.FilePath) :
    IO (List Scenario) := do
  let paths := (← dir.readDir).toList.map (·.path)
    |>.filter (·.extension == some "json")
    |>.mergeSort (·.toString ≤ ·.toString)
  paths.mapM loadScenario

def rule (title : String) : String :=
  let head := s!"── {title} "
  head.pushn '─' (64 - head.length)

def isRejection (v : String) : Bool :=
  v ∈ ["parse", "BornBefore", "NoBilocation",
       "SingleManager", "UniqueIds"]

-- ANCHOR: evaluate
/-- The numbers that say how the loop did. -/
def evaluate (live : Bool)
    (rows : List (Scenario × Outcome)) : IO Bool := do
  let vs := rows.flatMap (·.2.verdicts)
  let count (p : String → Bool) := (vs.filter p).length
  let bad := rows.filter fun (sc, o) => sc.expect != o.verdicts
  IO.println (rule "evaluation")
  IO.println s!"turns {rows.length}, LLM replies {vs.length}"
  IO.println s!"rejected {count isRejection} \
    (parse {count (· == "parse")}, \
    axioms {count fun v => isRejection v && v != "parse"})"
  IO.println s!"committed {count (· == "committed")}, \
    gave up {count (· == "gave up")}"
  IO.println s!"answers: yes {count (· == "yes")}, \
    no {count (· == "no")}, unknown {count (· == "unknown")}"
  IO.println s!"certificates \
    {(rows.flatMap (·.2.certs)).length}"
  if live then
    IO.println "live run: verdicts are measured, not compared"
    return true
  for (sc, o) in bad do
    IO.println s!"UNEXPECTED in {sc.file}: {o.verdicts}"
  IO.println s!"as expected: {rows.length - bad.length}\
    /{rows.length}"
  return bad.isEmpty
-- ANCHOR_END: evaluate

-- ANCHOR: main
/-- `unsafe` because loading a Lean environment at run time
    runs the initializers of the imported modules. -/
unsafe def main (args : List String) : IO UInt32 := do
  let live := args.contains "--live"
  -- the ELPI rules live in a Lean environment: load it
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Agent.Reason }] {}
    (loadExts := true)
  let reasoner := Reasoner.ofEnv env
  let script ← loadScript "replay"
  let llm? ← if live then some <$> Agent.live else pure none
  let mut memory := World.memory
  let mut rows := []
  for sc in script do
    IO.println (rule sc.file)
    let llm ← match llm? with
      | some l => pure l
      | none   => replay sc.replies
    let o ← turn llm reasoner memory sc.user
    memory := o.memory
    rows := rows ++ [(sc, o)]
  let ok ← evaluate live rows
  -- ANCHOR_END: main
  if let _ :: path :: _ := args.dropWhile (· != "--certs") then
    let answers := (rows.zip (List.range rows.length))
      |>.filterMap fun ((_, o), n) =>
        if o.certs.isEmpty then none
        else some (n + 1, o.memory.store, o.certs)
    IO.FS.writeFile path (certFile answers)
    IO.println s!"wrote {answers.length} sections to {path}"
  return if ok then 0 else 1
