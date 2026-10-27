import Agent.Loop

/-!
# Certificates for the kernel

At run time a certificate is the verdict of a compiled
decision procedure; the proof term itself is erased. To have
the kernel check the answers, the agent can write them out
as a Lean file: each store it answered from, and each claim
as a theorem proved `by decide`. Anyone can re-check that
file, with no trust in the agent:

    lake env lean certs.lean
-/

namespace Agent

open Memory

-- ANCHOR: export
def leanEvent (e : Event) : String :=
  "\n".intercalate [
    s!"    ⟨{e.id}, .{kinds.name e.kind}, {lps e.who},",
    s!"     .{cities.name e.place}, \
       .mk! {e.span.start} {e.span.stop}⟩"]

def leanStore (name : String) (s : Store) : String :=
  let reps := s.reportsTo.map fun (p, m) =>
    s!"({lp p}, {lp m})"
  "\n".intercalate [
    s!"def {name} : Store :=",
    "  { World.store with",
    "    reportsTo := [" ++ ",\n      ".intercalate reps ++ "]",
    "    events := [",
    ",\n".intercalate (s.events.map leanEvent) ++ "] }",
    "",
    s!"theorem {name}_consistent : Consistent {name} := by",
    "  decide", ""]

/-- One section per answered question: the store it was
    answered from, then its certificates as theorems. -/
def certFile (answers : List (Nat × Store × List String)) :
    String := Id.run do
  let mut out := "import Agent.Check\nopen Memory Agent\n\n"
  let mut last : Option (Nat × Nat) := none
  let mut name := ""
  for (n, s, claims) in answers do
    -- memory only grows, so its size identifies it
    let size := (s.events.length, s.reportsTo.length)
    if last != some size then
      name := s!"store{n}"
      out := out ++ leanStore name s ++ "\n"
      last := some size
    for (c, k) in claims.zip (List.range claims.length) do
      let c := c.replace "store " (name ++ " ")
      out := out ++ s!"theorem turn{n}_{k + 1} :\n    \
        {c} := by\n  decide\n\n"
  return out
-- ANCHOR_END: export

end Agent
