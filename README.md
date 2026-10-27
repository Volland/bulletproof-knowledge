# Bulletproof Knowledge — companion code

Runnable code for the book
**Bulletproof Knowledge: Building Hallucination-Resistant Neurosymbolic Agents
with Lean and Logic Programming** by Volodymyr Pavlyshyn.

Every snippet printed in the book is pulled from these files, and every printed
output is checked by `#guard_msgs` when the project builds. If it is in the book,
it compiles.

## Requirements

- [elan](https://github.com/leanprover/elan) (installs the pinned Lean, **v4.35.0**)
- git, curl
- No Mathlib. The only dependency is
  [lean-elpi](https://github.com/Volland/lean-elpi) **v0.3.3** (λProlog inside Lean 4).

## Build

```bash
git clone https://github.com/Volland/bulletproof-knowledge
cd bulletproof-knowledge
lake build          # all chapters, solutions excluded
lake build Solutions
lake exe agent      # Chapter 12 agent, replay mode (offline)
```

`lake exe agent -- --live` calls the Anthropic API and needs `ANTHROPIC_API_KEY`.

## Layout

| Path | Contents | Book |
|---|---|---|
| `Knowledge/Memory/` | the shared running example: an assistant agent's memory of people, places, organizations and events, with axioms and a certified store | all chapters |
| `Knowledge/Ch01`–`Ch09` | pure Lean 4, no λProlog | Parts I–II |
| `Reasoning/Ch02`, `Ch10`, `Ch11` | logic programming with lean-elpi | Parts I, III |
| `Agent/` | the hallucination-resistant agent (`lake exe agent`) | Chapter 12 |
| `replay/` | recorded LLM responses for deterministic runs | Chapter 12 |
| `solutions/` | solutions to the exercises | Chapters 6–12 |

All people, organizations and events in the examples are fictional.

## License

Apache-2.0.
