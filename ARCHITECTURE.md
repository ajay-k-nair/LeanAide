# LeanAide Architecture

This document explains seven aspects of how LeanAide is actually built, grounded
in the source code (file paths + line numbers) rather than only the paper's
high-level description. Where the real implementation differs from, extends,
or falls short of the paper/README's description, that's called out explicitly
rather than smoothed over.

---

## 1. Statement & Definition Translation

This is the pipeline that turns a single natural-language statement or
definition into Lean syntax, independent of full proof translation.

**Retrieval.** `LeanAideCore/LeanAideCore/SimilaritySearch.lean:7-49`
(`callSimilaritySearch`) POSTs `{num, query, descField}` to
`{server}/run-sim-search` (default `http://localhost:7654`), falling back to a
local Python script `server/openai_similarity_search.py` if the server is
unreachable. That script embeds the query with **OpenAI's
`text-embedding-3-small`** (`server/openai_similarity_search.py:30,54-58`) and
does in-process cosine search (numpy) over pre-computed embedding JSONL files,
with a pickle cache. A legacy code path in `LeanCodePrompts/StatementGen.lean:37-54`
instead called a `/nearest_prompts` endpoint using `all-mpnet-base-v2` — this
is dead, superseded by the OpenAI-embedding server. Two more retrieval
backends — **leansearch.net** and **moogle.ai** semantic search over Mathlib —
exist as alternative, composable `PromptExampleBuilder`s
(`LeanAideCore/LeanAideCore/PromptBuilder.lean:50-85,195-265`, via `sequence`/`blend`
combinators). This pluggable-retrieval-source design isn't mentioned in the paper.

**Prompt assembly.** `Translator.getMessages`
(`LeanAideCore/LeanAideCore/Translate.lean:95-105`) retrieves doc/type pairs,
converts them to few-shot `ChatPair` examples, and builds an OpenAI
chat-messages array via `MessageBuilder.buildMessages`
(`ChatClient.lean:481-497`) — all examples flattened into one user message,
not a multi-turn conversation.

**Multiple candidates + type-checking.** `Translator` defaults to
`params := {n := 8}` (`LeanAideCore/LeanAideCore/Translator.lean:147`) — 8
candidates requested via OpenAI's native `n` field in **one** API call
(`ChatServer.queryAux'`, `ChatClient.lean:203-221`), not iterative sampling.
Each candidate is parsed/elaborated by `elabThm4`/`elabThm4Aux`
(`TheoremElabCheck.lean:43-97`), a full Lean frontend elaboration pass; only
candidates that produce no errors survive.

**"Majority voting up to automation-provable equivalence."** `bestElab`/`bestElab?`
(`Translate.lean:140-231`) group elaborated candidates via `groupThmExprsSorted`
→ `groupThmExprs` (`TheoremEquality.lean:111-126`), bucketing two statements
together if `provedEquiv` succeeds. `provedEquiv`
(`TheoremEquality.lean:27-37`) tries Lean's **`grind`** tactic on the `Iff` (or
`provedEqual` via `grind` on `Eq`) between the two candidates' types. The
largest group's first member wins. So "the automation" here is literally
`grind`, run inside `MetaM`/`TermElabM` — not an external ATP.

---

## 2. The Agentic JSON-Generation Framework

**Correction (previous version of this document was wrong):** the first pass
of this research only looked at the in-Lean/server-side JSON-generation
tasks and concluded there was no real agentic framework. That's true *for
that specific path*, but it missed an entire, separate, standalone Python
package — `mathdoc_agent/` — that *is* genuinely agentic: real iterative
worklist loops, 25+ specialized per-proof-kind agents, and a document/proof
tree that's mutated in place until no work remains. Both paths coexist in
the repo. This section now covers both, clearly distinguished.

### 2a. The in-Lean/server-side path (single-shot, no retry)

Two earlier stages, invoked from within Lean (via `#theorem`/the server),
turn a natural-language proof into structured JSON: (1) rewriting it into a
more "formalization-friendly" sketch, and (2) translating that sketch into
the structured JSON schema.

**Stage 1 — sketch generation.** The `@[response "prove_for_formalization"]`
task (`LeanAideCore/LeanAideCore/Responses.lean:369-384`) calls
`ChatServer.proveForFormalization` (`ChatClient.lean:555-560`) against template
`prove_theorem_for_formalization` (`Resources.lean:39`), which injects a fixed
rule-set (`Resources.proofGuidelines`, e.g. "declarative over imperative,"
"decompose into lemmas") plus **symbolic dependency context**: `defsBlob? type`
(`Responses.lean:377`, `StatementSyntax.lean:104-118`) walks the constants
occurring in the already-elaborated statement and pulls their docstrings —
this is genuine context injection, but via direct dependency lookup, not
embedding retrieval. Generation is a single completion (`n := 1`) — **no
retry or self-correction loop**.

**Stage 2 — sketch → JSON.** Two parallel mechanisms exist for this, which is
itself a discrepancy worth knowing about:
- `@[response "json_structured"]` (`Responses.lean:407-417`) →
  `ChatServer.jsonStructured` (`ChatClient.lean:562-568`) embeds a full JSON
  Schema (`Resources.paperStructure`) as literal text and asks for one
  completion, parsed via `extractJsonM` (`Aides/Basic.lean:480-492`) — **which
  does not retry on parse failure**, it just logs a warning and wraps the raw
  text as a JSON string.
- `@[response "structured_json_proof"]` (`Responses.lean:422-437`) →
  `ChatServer.structuredProof` (`ChatClient.lean:617-629`) instead uses a
  hand-written schema description (`MathParaStructure.mathDoc` via
  `MathDoc.instructions`, `MathDoc.lean:423-426`).

Neither path uses a structured-output/function-calling API, despite
`LLMClient.lean:126-136,201` defining a `ResponseFormat.jsonSchema` field on
the request type — **that field is never populated at the actual call site**
(`ChatClient.lean:203-221`). So at this specific layer: **there is no agent
loop, tool use, or schema-validated retry** — it's single-shot free-text
generation with regex/code-block extraction.

**Extensibility mechanism.** `DocumentSchema.lean` defines the schema via
`#schema_element "Name" := json% {...}` and `#schema_group "Name" with [...]`
commands (`JsonSchemas.lean:164-247`), registered into a
`SimpleScopedEnvExtension` (`JsonSchemas.lean:125-132`) — architecturally
identical to the `@[codegen]` attribute mechanism used for code generation
(§3). **Gap:** this registry is **not wired into the live prompt path** —
`jsonStructured` still hardcodes the older static `Resources.paperStructure`
blob (`ChatClient.lean:566`). The registry exists and works, but the actual
JSON-generation query doesn't consult it yet.

### 2b. `mathdoc_agent` — a separate, genuinely agentic pipeline

`mathdoc_agent/` is a standalone Python package (OpenAI Agents SDK) with its
own README/`Agents.md`, invoked via CLI or Python API
(`mathdoc_agent.pipeline.generate_math_document_json[_sync]`), that turns a
full natural-language document into the same structured JSON that
`lake exe codegen` consumes. **It is not wired into the Lean server or
`LeanAideCore`/`LeanAide` at all** — a repo-wide grep confirms zero `.lean`
files or other Python modules import or invoke it. The only connection to the
rest of LeanAide is one-way: the JSON file it writes, and an *optional*
`--lean` flag under which `mathdoc_agent` itself starts/POSTs to a running
`leanaide_process` HTTP server (`pipeline.py:198-289,416-457`) — i.e. even
this integration is `mathdoc_agent` reaching outward into Lean, never the
reverse. It supersedes an older, simpler predecessor, `json_agent/` (first
commit 2026-05-13, PR #145), which used OpenAI's native
`chat.completions.parse(response_format=PydanticModel)` structured-output API
directly with one orchestrator pass and one dedicated extraction call per
document element (theorem/definition/section/figure/table) — genuinely
structured output, but no audit/repair passes. `json_agent` has zero
references anywhere else in the repo in either direction.

**What's genuinely agentic:** two independent worklist loops — one over the
document tree, one over each attached proof tree — are real
`for _ in range(max_iterations): node = choose_next(...); if node is None:
break` loops (`orchestration/document_orchestrator.py:107-157`, 20 iterations
by default; `orchestration/proof_orchestrator.py:69-88`, 100 per proof),
**not** a fixed number of stages. Node statuses (`raw → classified/decomposed
→ locally_refined → validated → resolved`, or terminal `opaque`,
`models/base.py:6-14`) are recomputed bottom-up from live children after every
mutation, so a parent's "resolved" state is a real derived property.
Classifying a node can spawn children that re-enter the *same* worklist and
get refined in a later iteration — genuine recursion-via-iteration. Handler
dispatch goes through `DocumentHandlerRegistry`/`ProofHandlerRegistry`
(`registries/`) — plain dict lookups with an `"unknown"` fallback — populated
by `plugins/document_types.py`/`plugins/proof_types.py` with real
per-kind agents: `document_parser_agent`, `proof_classifier_agent`, and
dedicated refiners (`induction_agent`, `cases_agent`, `simple_proof_agent`,
`calculation_agent`, `specialize_agent`, `structured_proof_agent` — the last
covering 27 structured proof kinds like `contradiction`, `pigeonhole`,
`compactness`, `diagram_chase`). A `proof_resolution_agent` (plus
combinatorial/analytic/structural family variants) rewrites proof kinds
without a direct Lean codegen handler into simpler supported ones.

**What looks agentic but is a fixed sequence:** the pipeline's tail —
rewriting `deduced_from_claim` dependencies, auditing `claim` fields
(`claim_audit_agent`), repairing informal notation, auditing then repairing
risky proof-step assertions — genuinely mutates the document via JSON-pointer
patch application (`orchestration/claim_audit.py:136-147` and siblings), not
just logging. But `pipeline.py:566-590` chains these as a **fixed linear
sequence, each stage called exactly once** (notation-repair and
`deduced_from_claim` materialization run at two hardcoded points, which is a
hardcoded two-pass, not a while-loop) — nothing re-audits a repaired output
to check whether the repair introduced a new problem. Tellingly,
`orchestration/repair.py` defines `RepairRequest`/`RepairSpec` models that
look built for a genuine propose-a-fix-and-retry loop keyed off validation
failures — **grep confirms these are never imported anywhere else in the
codebase.** The actual failure path when a worklist node fails validation is
simply marking it `opaque` and moving on, not asking an agent to repair it.
This is the same pattern as `DocumentSchema.lean`'s unused extensibility
registry in §2a: well-designed self-correction scaffolding that exists in the
codebase but isn't wired into the live path.

**Retries:** `mathagents/runner.py:run_agent_typed` retries only on agent-call
*timeout* (default 1 retry, 600s timeout, `MATHDOC_AGENT_AGENT_RETRIES`/
`MATHDOC_AGENT_AGENT_TIMEOUT_SECONDS`). A JSON-parse or Pydantic-validation
failure on the agent's returned output is fatal and unretried, and
`pipeline.py` has no exception handling around any of its 12 documented
stages — an uncaught error from any one of them aborts the whole run.

**Bottom line:** "is it agentic?" depends entirely on which of the two
systems you mean. The in-Lean path (2a) is not. `mathdoc_agent` (2b) really
is, in its core tree-refinement phase — genuine iterate-to-convergence
worklists, real per-kind agent dispatch — but its "self-correction" tail is a
fixed one-pass audit→repair sequence, and a plausible upgrade to a true
retry-until-clean loop already has (unused) scaffolding sitting in the
codebase.

---

## 3. JSON → Lean Translation (Combinator Code Generation)

This stage is the common back-end for *both* JSON producers in §2: JSON
generated in-Lean (§2a) or by `mathdoc_agent`/CLI (§2b, via
`lake exe codegen <file>.json`) is consumed identically from here on.

**Registration.** `@[codegen "induction_proof"]` on a top-level `def` (e.g.
`LeanAideCore/LeanAideCore/PaperCodes.lean:1222`) triggers
`registerBuiltinAttribute` (`CodegenCore.lean:69-97`), which type-checks the
declaration against the expected signature
`CodeGenerator → Option MVarId → (kind : SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))`
and stores the **declaration's name** (not the function itself) into
`codegenExt`, a `SimpleScopedEnvExtension` mapping JSON key string → array of
names (`CodegenCore.lean:44-50`).

**Dispatch.** `getCode` (`CodegenCore.lean:145-184`) extracts the `"type"` key
from the incoming JSON, looks up every registered name for that key, and for
each calls `codeFromFunc` (`CodegenCore.lean:121-138`), which does an `unsafe
evalConst` to reflectively load the compiled definition and apply it. If a
handler throws, the next handler registered under the same key is tried — so
several `@[codegen "x"]` defs can form a silent fallback chain for one key,
which the paper doesn't mention.

**State threading.** `TranslateM := StateT Translate.State TermElabM`
(`TranslateM.lean:171`). Handlers like `inductionCode` run under
`goal.withContext`, split the goal into subgoal metavariables, and recursively
call back into `getCode` for each subgoal's JSON sub-proof — local context and
environment updates ride along in the `TermElabM`/`MetaM` layers underneath.
Top-level command sequences are assembled per-document-item in
`getCodeCommands` (`CodegenCore.lean:311-337`), which loops over JSON sources
and calls `Translate.addCommands` for each successfully generated
`commandSeq` (`CodegenCore.lean:331`) — this is the loop that streams partial
output (see the "Partial Output" note below).

**Automation fallback.** `findTactics?` (`CodegenCore.lean:244-253`) is tried
**before** descending into JSON sources — both per-subgoal
(`getCodeTacticsAux`, line 200) and for the whole goal up front
(`getCodeTactics`, line 275). It builds a list of tactic candidates and
actually runs them, parsing Lean's real "Try this:" suggestion output from
`simp?`/`grind?` (`RunTactics.lean:306-339`). That candidate list is
swappable per project via `#add_auto_tactics` — the core library defaults to
`llm?` (`CodegenCore.lean:31`), while the app-level config in
`LeanAide/Codegen.lean:39` overrides it to `hammer` + `try_this (constructor)
then (grind?)`. So "tries exact?, then simp?, then grind?, then hammer?" is
the *currently configured* list, not a hardcoded sequence.

**Partial/live output.** As of this snapshot, `Translate.addCommands`
(`TranslateM.lean`) also calls `writeCommands`, which appends each
successfully-generated command to `Translate.State.outputFile` if one is
configured — so a long document's generated code streams to
`CodeGen/Live/<name>.lean` incrementally as `getCodeCommands`'s loop
progresses, while the polished final version is written once, at the end, to
`CodeGen/<name>.lean` via `codegen.lean`'s `runCodegen`. See
`codegen.lean:28,116-152` and `live_output_demo.lean` (repo root) for a
minimal, Mathlib-free runnable demonstration of this mechanism in isolation.

---

## 4. Client-Server Architecture

**The server.** `lake exe leanaide_process` (`leanaide_process.lean`) is a
long-lived Lean binary with Mathlib loaded, speaking **one JSON object per
line over stdin/stdout** (`process_loop`, `leanaide_process.lean:177-271`).
`server/api_server.py` is a small stdlib `http.server`/`ThreadingMixIn` HTTP
process (`api_server.py:128-130`) that lazily spawns this binary as a
subprocess (`api_server.py:188-199`), reads its stdout/stderr line-by-line on
background threads into a `queue.Queue` (`api_server.py:82-126`), and on each
POST request writes the body as one JSON line to the child's stdin and
**blocks** on the queue (6000s timeout, `api_server.py:217-221`) for the next
JSON line to come back as the HTTP response. There is no separate REST
resource model or protocol-translation layer — just a stdin/stdout↔HTTP pipe.
`leanaide_server.py` is the top-level launcher: it starts `api_server.py`
plus, optionally, a Streamlit UI (`server/streamlit_ui.py`) — an ordinary
blocking HTTP client of the API server (`server/serv_utils.py:317-322`,
`requests.post`). This Streamlit UI is "the web interface for users
unfamiliar with Lean" mentioned in the paper. `example_server/` (a separate
Flask app for open-source embedding lookups) and `server/postoffice.py`
(explicitly commented as an example ChatGPT-authored reference
implementation) are auxiliary, not the main server.

**The client (`LeanAideCore`).** `LeanAideCore/LeanAideCore/Kernel.lean`
defines `class LeanAidePipe` (line 273) with one method
`queryResponse : Json → MetaM Json`. `LeanAidePipe.fromURL` (lines 283-292) is
the plain blocking client — shells out to `curl` via `IO.Process.run`.
`LeanAidePipe.fromUrlAsync` (lines 322-343) is what's actually wired up by
default: for `"mode":"async"`/`"lookup"` requests it just proxies via `curl`;
for a plain foreground call it polls to completion (see below) so the caller
still sees an apparently-synchronous `MetaM` call. `#leanaide_connect [url]`
(lines 794-811, defaults to `localhost:7654`) is the command a downstream file
writes to establish the connection, verified with a synchronous `"echo"`
ping. Every high-level `Kernel` operation (`translateThm`, `translateDef`,
`jsonStructured`, `codeFromJson`, etc.) has **two** implementations selected
by typeclass resolution: a local one when Mathlib/`LeanAide` is available, and
an HTTP-query one (`Kernel.lean:367-612`) used when only `LeanAideCore` is in
scope — each encodes a small JSON task descriptor, sends it via
`pipe.queryResponse`, and elaborates the returned Lean source text locally.
**The client never elaborates the translation logic itself against Mathlib —
it sends text over HTTP and only elaborates the returned snippet.**

**Async + polling design.** The server keeps
`TasksState := Std.Mutex <| Std.HashMap UInt64 TaskStatus`
(`TaskStatus.lean:8-21`, `running | completed`), keyed by a hash of the
request. `"mode":"async"` (`leanaide_process.lean:196-207`) spawns the task
in the background via genuine OS-thread-pool concurrency
(`TranslateM.runBackgroundChain` with a configurable `Task.Priority`) and
returns `{"status":"background","token":hash}` immediately;
`"mode":"lookup"` (lines 208-213) returns the current `TaskStatus` for a
token. This exact protocol is reused at three layers: the raw process
protocol; the client API (`Deferred`/`queryAsync`/`updateByToken`,
`Kernel.lean:243-268,633-652`, plus `pollServer` — a sleep-and-retry loop,
default 10s, `Kernel.lean:295-343` — that makes the "synchronous"-looking call
actually poll under the hood); and Lean-editor commands
(`#generate`/`#generateToken`/`#lookup`/`#write`, `Kernel.lean:918-1007`),
where the token is reified as a plain `def <name>token := <token>` in the
source file so a human can manually re-run `#lookup` later (via
`Tactic.TryThis.addSuggestion` — the same mechanism behind Lean's "Try this:"
quick-fixes). A **webhook alternative** exists: an optional `response_url`
field (`leanaide_process.lean:54,66-75`) makes the server itself `curl`-POST
the result once the task completes, instead of requiring a poll — used by the
`spawn_worker`/`input_url`+`output_url` pull-work topology
(`leanaide_process.lean:140-169`), matching the example `postoffice.py`
task-queue server.

**Why async+polling rather than one long blocking call or websockets?**
Nothing in the code states this explicitly, but structurally: LLM-backed
elaboration/proof search can take arbitrarily long, and a Lean-editor command
blocking on an HTTP round-trip would freeze the editor. The token/`TasksState`
design lets many tasks run concurrently inside one Lean process while every
individual HTTP request (submit or poll) stays small and near-instant — a
natural fit for `http.server`'s simple threaded model, without needing
persistent connections or a streaming/websocket layer.

---

## 5. The Zero-Dependency `LeanAideCore` Library

`LeanAideCore/lakefile.toml` in full:
```toml
name = "leanaidecore"
defaultTargets = [ "LeanAideCore" ]

[[lean_lib]]
name = "LeanAideCore"

[[lean_lib]]
name = "LeanLog"
```
No `[[require]]` block, confirmed by `LeanAideCore/lake-manifest.json`
(`"packages": []`). Across all 55 `.lean` files under `LeanAideCore/LeanAideCore/`,
the only imports used are plain Lean4 core (`Lean`, `Lean.Meta`,
`Lean.Elab`, `Lean.Parser`, `Lean.Meta.Tactic.TryThis`, `Std`) and
`Lake.Toml` (bundled with the `lake` tool itself). No uncommented Mathlib
import exists anywhere in the tree.

Roughly grouped, `LeanAideCore` contains: config/base plumbing
(`Config.lean`, `ConfigExts.lean`, `Resources.lean`); JSON schema handling
(`JsonSchemas.lean`, `DocumentSchema.lean`); the code-generation core
(`CodegenCore.lean`, `PaperCodes.lean`, `RunTactics.lean`, `LLMTactic.lean`);
the translation/prompt pipeline (`Translate.lean`, `TranslateM.lean`,
`Translator.lean`, `PromptBuilder.lean`, `PromptExampleBuilder.lean`);
elaboration/theorem-checking (`TheoremElab.lean`, `TheoremElabCheck.lean`,
`TheoremEquality.lean`, `Sorries.lean`); the user-facing DSL
(`Syntax/Kernel.lean` — `#theorem`, `#def`, `#doc`, `translate_theorem`,
`#llm_query`, `#codegen_async`); the chat/LLM client (`ChatClient.lean`,
`LLMClient.lean`); and the server-client abstraction (`Kernel.lean`,
`CoreKernel.lean`, `Actor.lean`, `TaskStatus.lean`, `Responses.lean`).

**Why this split matters**, per the README (`README.md:65-67`): "Adding
`LeanAide` as a dependency to your project is brittle and slow... toolchains
need to match exactly. Further, there may be a collision of transitive
dependencies." `LeanAideCore` is the transport/DSL/codegen layer — it builds
request JSON, talks HTTP to a server, and splices returned `Syntax`/`Expr`
into your file. Actually *elaborating* generated code against real
mathematical content (checking `Group`, `Set.Infinite`, or running
`grind`/`hammer` proof search) needs Mathlib (and, for `hammer`,
`LeanHammer`) — that heavy lifting happens server-side, inside
`leanaide_process`, which already has Mathlib loaded once, persistently. A
downstream project's own toolchain/dependency graph never has to embed all of
`LeanAide` + Mathlib + Hammer as *its own* lakefile chain merely to get
autoformalization syntax.

**One real inconsistency found:** `ResponsesExt.lean:3` does `import Qq` — a
genuine external package — despite the zero-dependency manifest. Checking
`.lake/build/ir/`, this file (and `SchemaFiddle.lean`) have **no compiled
artifacts**, unlike all other 55 modules, meaning they're not part of a
currently-successful default build. This is worth a maintainer follow-up
since it's a latent break of the zero-dependency guarantee if it were ever
wired into the default build target.

---

## 6. Setting Up LeanAideCore in Your Own Project

Based on the README and the repo's own (working) `ClientTest/` example
project, which already depends on `LeanAideCore`:

1. **Match the toolchain.** Use `leanprover/lean4:v4.28.0` in your
   `lean-toolchain` file — the version this repo and `ClientTest` are pinned
   to. `LeanAideCore` (and Mathlib, if you add it) are built against this
   exact toolchain.

2. **Add `leanaidecore` as a dependency**, in `lakefile.toml`:
   ```toml
   [[require]]
   name = "leanaidecore"
   git = "https://github.com/siddhartha-gadgil/LeanAide.git"
   rev = "main"
   subDir = "LeanAideCore"
   ```
   (Consider pinning `rev` to a commit SHA rather than `main` for
   reproducibility.) Note: this repo's own `ClientTest/lakefile.toml` instead
   uses a local path (`path = "../LeanAideCore"`), which only works when
   checked out alongside this repo — for a genuinely separate project, use
   the git form above.

3. **Add Mathlib too, if your generated code will use it** (very likely) —
   every file in `ClientTest` does:
   ```toml
   [[require]]
   name = "mathlib"
   git = "https://github.com/leanprover-community/mathlib4.git"
   rev = "v4.28.0"
   ```
   `LeanAideCore` itself does not require Mathlib; you add it for your own code.

4. **Run the server**, from a checked-out copy of this repo:
   ```bash
   pip install -r server/requirements.txt
   export OPENAI_API_KEY=<your-key>      # or create private/OPENAI_API_KEY
   python3 leanaide_server.py             # add --ui for the Streamlit UI
   ```
   Defaults to listening on `http://localhost:7654`.

5. **Minimal working example** in your new project:
   ```lean
   import LeanAideCore
   import LeanAideCore.Syntax   -- for #theorem / #def / #doc / translate_theorem
   import Mathlib               -- if your generated code needs it

   open LeanAide

   #leanaide_connect            -- connects to http://localhost:7654 by default

   #eval LeanAidePipe.response <| json% {"task": "echo"}   -- smoke test

   #theorem : "There are infinitely many odd numbers." >> translate_theorem
   ```

6. **Optional:** for a shared/hosted server, set
   `set_option leanaide.authkey? "<key>"` client-side; for non-OpenAI
   embeddings, run `example_server/` and set `examples_url`.

**README inconsistencies found and flagged**, so they don't cost you time:
- `README.md` shows an example importing `LeanAideTools` — **no such
  package exists anywhere in this repo.** Use `import LeanAideCore` (+
  `LeanAideCore.Syntax`), as every `ClientTest` file actually does.
- The README points at `LeanCodePrompts/TranslateDemo.lean`; the real file is
  at `LeanAideTest/TranslateDemo.lean`.

---

## 7. Is There a Standalone "LeanServer" Using `LeanAideCore` on GitHub?

Checked GitHub's repository search for `LeanServer` and `leanaide server`,
and listed every public repo under the `siddhartha-gadgil` account (the
paper's corresponding author). **No such project was found.** The
`LeanServer`-named repos that exist on GitHub are unrelated (a verified
HTTPS/TLS server written in Lean 4, and a small Lean web micro-framework —
neither references LeanAide). The one LeanAide-adjacent hit was
`shubhamkumar13/js-server-leanaide`, a JavaScript (not Lean) server mirror,
unrelated to `LeanAideCore` as a Lean dependency. Within
`siddhartha-gadgil`'s own repositories, the server-side component is simply
this repository's own `leanaide_process.lean` + `server/api_server.py` +
`leanaide_server.py` (§4) — there is no separate, independently-published
"LeanServer" repo that depends on `LeanAideCore` as an external package. If
one exists, it isn't publicly discoverable via GitHub's search API as of this
check.

---

## Sources

All findings above are grounded in direct reads of this repository's source
at the time of writing (`LeanAideCore/LeanAideCore/*.lean`, `LeanAide/*.lean`,
`server/*.py`, `example_server/`, `ClientTest/`, root `README.md`,
`codegen.lean`, `leanaide_process.lean`, `mathdoc_agent/*.py` and its
`README.md`/`Agents.md`, `json_agent/*.py`), plus a live GitHub repository/code
search for §7. No content here is drawn from the paper's prose alone without
independent code verification.

**Revision note:** §2 was corrected after an initial pass missed
`mathdoc_agent/` entirely (it isn't referenced from any `.lean` file or the
Python server, so it wasn't reachable by tracing outward from the response
tasks first read). If you're skimming rather than reading §2 in full, don't
miss 2b — it's the more interesting half.
