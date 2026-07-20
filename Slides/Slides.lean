import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

#doc (Slides) "LeanAide" =>

# Lean{class "grad"}[Aide]

_Extensible Autoformalization by Combinator Code Generation_

Ajay Kumar Nair

Department of Mathematics, Indian Institute of Science, Bangalore

:::notes
Short paper, CVIT 2016 (placeholder venue in the template). Funded by
Renaissance Philanthropy's AI for Math Fund.
:::

# The {class "grad"}[Team]

- Siddhartha Gadgil — Dept. of Mathematics, IISc Bangalore
- Anirudh Gupta — Dept. of Mathematics, IISc Bangalore
- Malhar Alpesh Patel — IISER Pune
- Swarnava Chakraborty — Dept. of Mathematics, IISc Bangalore

# What is {class "grad"}[Autoformalization?]

The translation of natural language mathematics into a formal
language that is machine-verifiable — in our case, *Lean*.

- Statements and definitions
- Theorems _with_ proofs
- Whole documents with multiple theorems and proofs

:::fragment
LeanAide does all three, using LLMs, metaprogramming, and Lean's own
proof automation.
:::

# LeanAide in {class "grad"}[One Line]

:::::stretch
:::class "r-fit-text"
An extensible, modular framework for autoformalization using
large language models, metaprogramming, and proof automation in Lean.
:::
:::::

The central idea: *Combinator Code Generation* — combining handlers
for different mathematical constructs, the way combinator _parsers_
combine parsers for different grammar rules.

:::fragment
Every piece of that sentence gets unpacked as we go: the translation
pipeline, combinator code generation itself, how agentic it really is,
and how to set it up yourself.
:::

# Two Scales of {class "grad"}[Translation]
%%%
vertical := true
%%%

LeanAide formalizes at two scales, with the second built on the first.

## Statements & Definitions

Translate a single natural-language statement or definition into
Lean syntax that type-checks.

_(Earlier work in this project.)_

## Proofs & Documents

Given a theorem (with or without proof), or a whole document with
several theorems and proofs, translate the *entire* argument —
using statement/definition translation as a subroutine.

We can even start from just a statement and _generate and translate_
the proof itself.

# Statement & Definition {class "grad"}[Translation]

An LLM pipeline with prompt engineering and post-processing:

- Retrieve similar Mathlib/Lean *docstrings* via embeddings
  (OpenAI, swappable for `leansearch.net`/`moogle.ai`)
- Ask for `8` *candidate* translations in one API call
- *Parse and type-check* every candidate — reject failures
- *Majority vote* — group candidates `grind` can prove equivalent

:::fragment
Systematic syntactic errors LLMs tend to make are patched
automatically via metaprogramming.
:::

# Our {class "grad"}[Running Example]

One real example, followed through every stage below
_(from `LeanAideExamples`, `WithoutSorries/Example_4.lean`)_:

Let $`(a_n)` be a sequence with $`a_0 = c` and $`a_{n+1} = a_n` for
all $`n`. Then $`a_n = c` for all $`n`.

:::fragment
Small enough to fit on one slide at every stage — sketch, JSON,
handler, generated code — but with a real base case and a real
inductive step.
:::

# Proofs & Documents: {class "grad"}[Four Stages]
%%%
vertical := true
%%%

Navigate _down_ through the four stages of the pipeline, following
our running example at each one.

## Stage 1 — Formalization-Friendly Sketch

Ask the LLM to rewrite the natural-language proof into a more
_formalization-friendly_ sketch, with the constants — and their
docstrings — injected as context. For our example:

_"…suppose that $`a_0 = c` and that for every natural number $`n` we
have $`a_{n+1} = a_n`. The proof proceeds by induction on $`n`. First,
consider the base case $`n = 0`… Next, assume the inductive
hypothesis $`a_k = c`, and prove $`a_{k+1} = c`."_

:::fragment
One completion, no retry: currently the pipeline's main failure point.
:::

## Stage 2 — Structured JSON Proof

Translate the sketch into a *structured JSON* representation of the
proof, based on how mathematical proofs are actually structured —
here, for our running example:

```code json
{ "type": "Theorem", "hypothesis": [
    { "type": "let_statement", "variable_name": "a_n", ... },
    { "type": "assume_statement", "assumption": "a_0 = c." },
    { "type": "assume_statement",
      "assumption": "For all n, a_{n+1} = a_n." }
  ],
  "claim": "Then a_n = c for all natural numbers n.",
  "proof": { "type": "induction_proof", "on": "n",
    "base_case_proof": [ ... ], "induction_step_proof": [ ... ] } }
```

:::fragment
The schema is extensible via `#schema_element`/`#schema_group`
commands — the same environment-extension pattern as `@[codegen]`.
_(How agentic is the JSON step itself? Coming up.)_
:::

## Stage 3 — Monadic Combinator Code Generation

The heart of the system: translate the JSON proof into Lean code
using a collection of composable *handlers*, one per construct — for
our example, dispatching on `"induction_proof"`.

_(Full deep dive next.)_

## Stage 4 — Proof Completion via Automation

The earlier stages leave sub-goals: lemma bodies, induction cases,
final gaps. Lean's proof automation — especially the `grind` tactic —
fills these in.

:::fragment
For our example, `grind` alone closes both the base case and the
inductive step — no lemma chain needed.
:::

# Is It Actually {class "grad"}[Agentic?]

Depends which of *two* JSON producers you mean:

- Inside Lean (`json_structured`/`structured_json_proof`): single-shot,
  no retry when parsing fails
- Standalone (`mathdoc_agent`, Python, OpenAI Agents SDK): a real
  *iterate-until-done* worklist loop over 25+ specialized agents, not
  wired into the Lean server — you run it yourself and feed its
  output JSON to `lake exe codegen`

:::fragment
Its audit/repair tail really *patches* the JSON tree — but each pass
runs once, in a fixed sequence, not until clean.
:::

# Combinator {class "grad"}[Code Generation]

Like *combinator parsing*: small parsers for individual grammar rules
combine into a parser for a whole grammar. Here: small *handlers* for
individual proof/statement constructs combine into a generator for
whole proofs and documents — top-level `theorem`s or nested `have`s
alike.

Handlers register against a `"type"` tag via the `@[codegen ...]`
attribute — several can share one key, tried in order as a fallback
chain — all reached through one recursive entry point, `getCode`. For
our example's `"induction_proof"` node:

```code lean
@[codegen "induction_proof"]
def inductionCode (translator : CodeGenerator := {}) :
    Option MVarId → (kind : SyntaxNodeKinds) → Json →
    TranslateM (Option (TSyntax kind))
  | some goal, `tacticSeq, js => goal.withContext do
    -- fields: "on", "base_case_proof", "induction_step_proof"
    -- getCode is called recursively on each sub-proof; the new goal
    -- threads into the next step, until `grind`/`hammer` closes it
    -- or a `sorry` is left
    ...
```

:::fragment
Dispatch is by name + reflection (`unsafe evalConst`), not a
first-class function table — that's what lets a handler register
itself anywhere with just an attribute. The same monadic threading
carries a *document*'s sequence of lemmas from one declaration to the
next, and is what the *partial output* feature streams from.
:::

# Why {class "grad"}[LeanAide?]

Systems like `Aristotle`, `Gauss`, and `AxiomProver` are powerful —
but monolithic and closed-source.

:::table +colHeaders +rowSeps
*
  * Property
  * LeanAide
*
  * Modular & extensible
  * New handlers combine with existing ones
*
  * Open source
  * Inspect, modify, extend freely
*
  * Rides on external progress
  * Improves as LLMs and `grind` improve
*
  * Structured IR
  * JSON schema, handles complex documents
:::

:::fragment
Also *composable* (swap in other systems' translators) and *scalable*
(decompose large documents, generate JSON in stages).
:::

# Our Running Example: {class "grad"}[The Result]

Real, live-checked Lean — hover or click any identifier below.

```lean
theorem eq_const_of_succ_eq_self :
    ∀ {α : Type u} (a : Nat → α) (c : α),
    a 0 = c → (∀ n, a (n + 1) = a n) → ∀ n, a n = c := by
  intro α a c h0 hstep n
  induction n with
  | zero => grind
  | succ n ih => grind
```

:::fragment
Every stage above — sketch, JSON, handler, automation — fed into this
one theorem, start to finish.
:::

# When {class "grad"}[Automation Isn't Enough]

If an $`n \times n` real matrix $`A` satisfies $`A^2 = -I_n`, then
$`n` is even. _(From `LeanAideExamples`, `WithSorries/Example_5.lean`.)_
The full argument needs minimal polynomials, diagonalization over
$`\mathbb{C}`, and eigenvalue counting — automation alone couldn't
close it.

```code lean
theorem even_of_matrix_sq_eq_neg_one :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A ^ 2 = (-1 : Matrix (Fin n) (Fin n) ℝ) → Even n := by
  intro n A hA
  sorry
```

:::fragment
The *statement* still type-checks correctly — a well-formed proof
obligation left for the user, not a wrong or missing claim.
:::

# Getting {class "grad"}[Started]
%%%
vertical := true
%%%

## Run the Server

```code lean
export OPENAI_API_KEY=<key>
python leanaide_server.py
```

Reads `OPENAI_API_KEY` (or `GEMINI_API_KEY`/`OPENROUTER_API_KEY`/
`DEEPINFRA_API_KEY`) straight from your shell, listens on `:7654` by
default — both straight from `leanaide_server.py`/`server/api_server.py`.

:::fragment
Elaborating against Mathlib, `grind`, and `hammer` all happens
*server-side* — that's exactly what your own project gets to skip.
:::

## Depend on It

Add `LeanAideCore` to your `lakefile.toml` — match only its
`lean-toolchain`, not LeanAide's own Mathlib + Hammer toolchain:

```code lean
[[require]]
name = "leanaidecore"
git = "https://github.com/siddhartha-gadgil/LeanAide.git"
subDir = "LeanAideCore"
```

```code lean
import LeanAideCore
open LeanAide

#leanaide_connect                                     -- localhost:7654
#eval LeanAidePipe.response <| json% {"task": "echo"}  -- smoke test

#theorem : "There are infinitely many odd numbers." >> translate_theorem
```

# Future {class "grad"}[Work]

- *Close the loop on self-correction* — `mathdoc_agent`'s audit/repair
  passes already patch real issues; make them re-audit until clean
  instead of running once (the scaffolding for this already exists)
- *Finish wiring the extensible JSON schema* — the registry works,
  but the live prompt path still hardcodes the older static schema
- *User interfaces* — friendlier tools, in Lean and standalone
- *Benchmarking* — compare systematically against other
  autoformalization systems

# Thank {class "grad"}[You]

:::class "pill"
[github.com/siddhartha-gadgil/LeanAide](https://github.com/siddhartha-gadgil/LeanAide)
:::

Funded by Renaissance Philanthropy's _AI for Math_ Fund.

:::fragment
Questions?
:::

:::notes
Point to the repo README for the server-client setup, and to
`LeanCodePrompts/TranslateDemo.lean` for a live code-action demo if
running Lean during Q&A.
:::
