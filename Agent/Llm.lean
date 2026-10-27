import Lean.Data.Json

/-!
# The neural component

The LLM is behind a `Provider`: a function from a
conversation to the text of the next reply. Two
implementations: `live` calls the Anthropic Messages API
with `curl`, `replay` returns recorded replies. The rest of
the agent cannot tell them apart.
-/

namespace Agent

open Lean

-- ANCHOR: provider
/-- One message of the conversation with the LLM. -/
structure Msg where
  role : String  -- "user" or "assistant"
  text : String

/-- Anything that can produce the next reply. -/
structure Provider where
  name     : String
  complete : (system : String) → List Msg →
             IO (Except String String)
-- ANCHOR_END: provider

-- ANCHOR: request
def model    : String := "claude-sonnet-5-5"
def endpoint : String :=
  "https://api.anthropic.com/v1/messages"

/-- The body of a Messages API request. -/
def requestBody (system : String) (msgs : List Msg) : Json :=
  Json.mkObj [
    ("model", toJson model),
    ("max_tokens", toJson (4096 : Nat)),
    ("system", toJson system),
    ("messages", Json.arr <| msgs.toArray.map fun m =>
      Json.mkObj [("role", toJson m.role),
                  ("content", toJson m.text)])]
-- ANCHOR_END: request

-- ANCHOR: response
/-- The text of a Messages API response: the concatenated
    `text` blocks of `content`. Errors and refusals are
    values, not exceptions. -/
def replyText (raw : String) : Except String String := do
  let j ← Json.parse raw
  if let .ok err := j.getObjVal? "error" then
    let msg := (err.getObjValAs? String "message").toOption
    throw s!"API error: {msg.getD err.compress}"
  if let .ok "refusal" := j.getObjValAs? String "stop_reason"
  then throw "the model declined to answer (refusal)"
  let blocks ← j.getObjValAs? (Array Json) "content"
  let texts := blocks.toList.filterMap fun b =>
    match b.getObjValAs? String "type" with
    | .ok "text" => (b.getObjValAs? String "text").toOption
    | _ => none
  return String.join texts
-- ANCHOR_END: response

-- ANCHOR: response_demo
/-- A response in the documented shape, trimmed. -/
def sample : String :=
  "{\"type\": \"message\", \"role\": \"assistant\", \
   \"content\": [{\"type\": \"text\", \"text\": \"Hi\"}], \
   \"stop_reason\": \"end_turn\"}"

/-- info: Except.ok "Hi" -/
#guard_msgs in
#eval replyText sample

/-- info: Except.error "API error: Overloaded" -/
#guard_msgs in
#eval replyText "{\"type\": \"error\", \"error\": \
  {\"type\": \"overloaded_error\", \
  \"message\": \"Overloaded\"}}"
-- ANCHOR_END: response_demo

-- ANCHOR: curl
/-- POST a body with `curl`. The API key travels on curl's
    standard input (`-H @-`), so it never appears in the
    process list. -/
def post (key body : String) (url := endpoint) :
    IO String := do
  let child ← IO.Process.spawn {
    cmd := "curl"
    args := #["-sS", "--max-time", "120", url,
      "-H", "content-type: application/json",
      "-H", "anthropic-version: 2023-06-01",
      "-H", "@-", "--data-binary", body]
    stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr s!"x-api-key: {key}\n"
  stdin.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then
    throw (IO.userError s!"curl failed ({code}): {err}")
  return out
-- ANCHOR_END: curl

-- ANCHOR: live
/-- The real model. Needs `ANTHROPIC_API_KEY`. -/
def live : IO Provider := do
  let some key ← IO.getEnv "ANTHROPIC_API_KEY"
    | throw (IO.userError "set ANTHROPIC_API_KEY for --live")
  return {
    name := s!"live ({model})"
    complete := fun system msgs => do
      let raw ← post key (requestBody system msgs).compress
      return replyText raw }
-- ANCHOR_END: live

-- ANCHOR: replay
/-- Recorded replies, returned in order, whatever the
    conversation says. Deterministic and offline. -/
def replay (replies : List String) : IO Provider := do
  let queue ← IO.mkRef replies
  return {
    name := "replay"
    complete := fun _ _ => do
      match ← queue.get with
      | [] => return .error "no recorded reply left"
      | r :: rest => queue.set rest; return .ok r }
-- ANCHOR_END: replay

end Agent
