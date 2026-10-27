import Lake

open System Lake DSL

/-!
Companion code for *Bulletproof Knowledge: Building Hallucination-Resistant
Neurosymbolic Agents with Lean and Logic Programming*.

Three libraries, one per part of the book:

* `Knowledge` — Parts I and II, pure Lean 4 (never imports `Elpi`).
* `Reasoning` — Part III, logic programming with lean-elpi.
* `Agent`     — Chapter 12, the hallucination-resistant agent (also an executable).
-/

package «bulletproof-knowledge» where
  version := v!"0.1.0"
  description := "Companion code for the book Bulletproof Knowledge: certified ontologies in Lean 4 and λProlog."
  license := "Apache-2.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lean-elpi» from git "https://github.com/Volland/lean-elpi" @ "v0.3.3"

@[default_target] lean_lib Knowledge where
  globs := #[.andSubmodules `Knowledge]

@[default_target] lean_lib Reasoning where
  globs := #[.andSubmodules `Reasoning]

@[default_target] lean_lib Agent where
  globs := #[.submodules `Agent]

lean_lib Solutions where
  srcDir := "solutions"
  globs := #[.submodules `Solutions]

@[default_target] lean_exe agent where
  root := `Agent.Main
  supportInterpreter := true
