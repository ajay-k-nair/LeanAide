import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

#doc (Slides) "LeanAide" =>

# Lean{class "grad"}[Aide]

_Extensible Autoformalization by Combinator Code Generation_

Siddhartha Gadgil · Anirudh Gupta · Ajay Kumar Nair ·
Malhar Alpesh Patel · Swarnava Chakraborty

Department of Mathematics, Indian Institute of Science, Bangalore
(and IISER Pune)

:::notes
Short paper, CVIT 2016 (placeholder venue in the template). Funded by
Renaissance Philanthropy's AI for Math Fund.
:::

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

- Retrieve similar Mathlib/Lean *docstrings* by embedding similarity
- Use them as few-shot examples in the prompt
- Ask the LLM for several *candidate* translations
- *Parse and type-check* every candidate — reject failures
- *Majority vote*, up to equivalence provable by automation

:::fragment
Systematic syntactic errors LLMs tend to make are patched
automatically via metaprogramming.
:::

# Proofs & Documents: {class "grad"}[Four Stages]
%%%
vertical := true
%%%

Navigate _down_ through the four stages of the pipeline.

## Stage 1 — Formalization-Friendly Sketch

Ask the LLM to rewrite the natural-language proof into a more
_formalization-friendly_ sketch — curtailing the tendency of LLMs to
be too chatty.

## Stage 2 — Structured JSON Proof

Translate the sketch into a *structured JSON* representation of the
proof, based on how mathematical proofs are actually structured.

The schema is extensible: new top-level document elements and new
proof structures can be added.

## Stage 3 — Monadic Combinator Code Generation

The heart of the system: translate the JSON proof into Lean code
using a collection of composable *handlers*, one per construct.

_(Full deep dive next.)_

## Stage 4 — Proof Completion via Automation

The earlier stages leave sub-goals: lemma bodies, induction cases,
final gaps. Lean's proof automation — especially the `grind` tactic —
fills these in.

# Combinator {class "grad"}[Code Generation]
%%%
vertical := true
%%%

:::hstack
Like *combinator parsing*: small parsers for individual grammar
rules are combined into parsers for a whole grammar.

Here: small *handlers* for individual proof/statement constructs
are combined into a generator for whole proofs and documents.
:::

Handlers are registered against a `"type"` tag (e.g.
`"induction_proof"`, `"assertion_statement"`, `"definition"`,
`"document"`) in an environment extension, via the `@[codegen ...]`
attribute.

## A Toy Combinator

"First handler that matches wins" — real Lean, live-checked:

```lean
/-- First success wins — the shape of LeanAide's handler
combination, simplified for illustration. -/
def firstMatch (hs : List (String → Option Nat))
    (tag : String) : Option Nat :=
  hs.foldl (init := none) fun acc h => acc <|> h tag
```

# The `getCode` {class "grad"}[Entry Point]

Every handler — and the whole pipeline — goes through one recursive
function _(reference listing from the real source)_:

```code lean
partial def getCode (translator : CodeGenerator) (goal? : Option MVarId)
    (kind : SyntaxNodeKinds) (source : Json) :
    TranslateM (Option (TSyntax kind))
```

- `goal?` — the current proof goal's local context
- `kind` — `tacticSeq` or `commandSeq`, the expected syntax
- `source` — the JSON for the construct being translated
- result: `TSyntax kind`, or `none` for side effects only

# Example Handler: {class "grad"}[Induction Proofs]

```code lean
@[codegen "induction_proof"]
def inductionCode (translator : CodeGenerator := {}) :
    Option MVarId → (kind : SyntaxNodeKinds) → Json →
    TranslateM (Option (TSyntax kind))
  | some goal, `tacticSeq, js => goal.withContext do
    -- fields: "on", "base_case_proof", "induction_step_proof"
    -- two new metavariables: base case, inductive step
    -- getCode is called recursively on each
    ...
```

Requires JSON fields `"on"`, `"base_case_proof"`,
`"induction_step_proof"` — mirroring what the `induction` tactic
itself needs. _(A separate handler covers `"general_induction_proof"`.)_

# Threading State: {class "grad"}[Lemmas & Sequences]

Proofs are decomposed into sequences of lemmas and definitions —
top-level, or nested inside another proof.

Handlers for `"document"`, `"logicalstepsequence"`, and `"proof"`
generate a *sequence* of steps. The _monadic_ part is essential:

- Tactic sequence → each lemma becomes a `have`/`let`, updating the
  *local context* and producing a new goal metavariable
- Command sequence → each lemma becomes a top-level `theorem`, `def`,
  or `noncomputable def`, updating the *environment*

Each new metavariable/environment feeds the _next_ step in the
sequence.

# Completing Proofs with {class "grad"}[Automation]

`findTactics?` tries, in order: `exact?`, `simp?`, `grind?`,
`hammer?`, `try?` — anything that returns a `Try This`/`Try These`
suggestion.

- Try *before* the first step, and again *after each* step
- Succeed anywhere → skip the rest, return the generated code
- Fail even after the last step → emit `sorry`
- A `sorry`'d *lemma* doesn't stop the document — the rest still generates

:::fragment
Can re-run the generated code to collect every `sorry`'s goal,
for _iterative_ refinement.
:::

# {class "grad"}[Interfaces]

LeanAide is designed to be usable both *inside* Lean and by people
who don't know Lean at all.

- Commands inside Lean for translating statements, definitions,
  proofs, and documents — including _asynchronously_
- A *server-client* architecture: your project depends only on the
  zero-dependency package `LeanAideCore`
- A *web interface* on the server, for users unfamiliar with Lean

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

# Example 1 — {class "grad"}[Simple Induction]
%%%
vertical := true
%%%

## The Statement

Let $`(a_n)` be a sequence with $`a_0 = c` and $`a_{n+1} = a_n` for
all $`n`. Then $`a_n = c` for all $`n`.

Proofs and JSON were generated for both the base case and the
inductive step — but automation alone was enough to close the goal.

## The Generated Code

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

# Example 2 — {class "grad"}[One-Line Automation]
%%%
vertical := true
%%%

## The Statement

Let $`G` be a group and $`a, b \in G`. If $`ab = ba`, then
$`a b a^{-1} = b`.

_(From `LeanAideExamples`, `WithoutSorries/Example_2.lean` — a real
LeanAide run, not a paper excerpt.)_

## The Generated Code

_(Reference listing — needs Mathlib, shown for illustration.)_

```code lean
theorem conj_eq_of_commute :
    ∀ {G : Type*} [Group G] {a b : G},
    a * b = b * a → a * b * a⁻¹ = b := by
  intro G _ a b hab
  exact Eq.symm (eq_mul_inv_of_mul_eq hab.symm)
```

Automation (`exact?`-style search) found this one-liner outright — no
lemma chain needed.

# Example 3 — {class "grad"}[Skew-Symmetric Determinant]
%%%
vertical := true
%%%

## The Statement

If a real matrix $`A` is skew-symmetric ($`A^T = -A`) and its
dimension $`n` is odd, then $`\det(A) = 0`.

A chain of `have` lemmas is generated, each easier than the last —
`grind` closes every remaining gap.

## The Generated Code

_(Reference listing — needs Mathlib, shown for illustration.)_

```code lean
theorem det_eq_zero_of_odd_of_antisymm_matrix_real :
    ∀ {n}, Odd n → ∀ (A : Matrix (Fin n) (Fin n) ℝ),
    A.transpose = -A → A.det = 0 := by
  intro n hodd A hanti
  have hdetT : ∀ M, M.transpose.det = M.det := by
    intro M; simp [Matrix.det_transpose]
  have hAdet : A.det = A.transpose.det := by
    simp [Matrix.det_transpose]
  have hnegdet : A.transpose.det = (-A).det := by grind only
  have hnegpow : (-A).det = (-1 : ℝ) ^ n * A.det := by
    grind only [Odd.neg_pow, Matrix.det_neg, Matrix.det_smul, ...]
  have hodd_pow : (-1 : ℝ) ^ n = (-1 : ℝ) := by simp [*]
  grind only
```

# Example 4 — {class "grad"}[Honest with Sorry]
%%%
vertical := true
%%%

## The Statement

If an $`n \times n` real matrix $`A` satisfies $`A^2 = -I_n`, then
$`n` is even.

_(From `LeanAideExamples`, `WithSorries/Example_5.lean`.)_ The full
argument needs minimal polynomials, diagonalization over $`\mathbb{C}`,
and eigenvalue counting — automation couldn't close it.

## The Generated Code

_(Reference listing — needs Mathlib, shown for illustration.)_

```code lean
theorem even_of_matrix_sq_eq_neg_one :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A ^ 2 = (-1 : Matrix (Fin n) (Fin n) ℝ) → Even n := by
  intro n A hA
  sorry
```

:::fragment
The *statement* still type-checks correctly — exactly the fallback
from "Completing Proofs with Automation": a well-formed proof
obligation for the user to finish, not a wrong or missing claim.
:::

# Getting {class "grad"}[Started]

```code lean
lake exe cache get   -- prebuilt Mathlib binaries
lake build
cd LeanAideCore
lake build
```

Set `OPENAI_API_KEY`, then in any Lean file:

```code lean
#theorem "There are infinitely many primes." >> translate_theorem

#def "A group is sane if every proper normal subgroup is cyclic." >>
  translate_definition
```

...or from the command line:

```code lean
lake exe translate "There are infinitely many primes"
```

# Future {class "grad"}[Work]

- *Multiple-round generation* — feed earlier failures back to the
  LLM; JSON proof generation is currently the main failure point
- *Extending the JSON schema & handlers* — especially
  calculation-heavy proofs
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
