import Lean
import Mathlib
import LeanCodePrompts.Translate
import LeanAide.AesopSyntax
import LeanAide.CheckedSorry
open LeanAide.Meta

/-!
# Lean code from `ProofJSON`

This file contains code to generate Lean code from a JSON structured proof. The plan is to incrementally improve this code to handle more and more complex proofs.

Some of the ingredients are:

* Extracting text from `let`, `assume` for context.
* Extracting text for a theorem statement.
* Translating a theorem object to a theorem and proof.
* Translating a sequence of statements to tactic proofs.
* Rules for `aesop` to complete proofs.

The cases to cover: "define", "assert", "theorem", "problem", "assume", "let", "proof", "cases", "induction", "case", "conclude", "remark". We can have different modes, at least "tactic" and "command".

* **remark**: This is a comment. We can ignore it.
* **define**: This is a definition. We can translate it to a `def` in command mode and `let` in tactic mode.
* **theorem**: This is a lemma. We can translate it to a `theorem` in command mode and `have` in tactic mode. We then pass to the proof in tactic mode. We begin the proof with `intro` statements for the hypotheses. We conclude the theorem with an `aesop` based tactic with fallback.
* **assert**: This is a lemma. We can translate it to a `theorem` in command mode and `have` in tactic mode. We then pass to the proof in tactic mode. We may (or may not) begin the proof with `intro` statements for the hypotheses not already introduced. We build an `aesop` based tactic with fallback and have this as the proof. This includes a search for relevant lemmas.
* **let** and **assume**: These are context statements. We simply add them to the context, so they get used in assertion.
* **induction**: We first look ahead to the proof cases to write this as `induction ...` in tactic mode, with the `case` heads also determined. We then use recursively the proofs in the cases.
* **cases**: We first look ahead to the proof cases to write this as `cases ...`, `by_cases` or `match ...` in tactic mode, with the `case` heads also determined. We then use recursively the proofs in the cases. In the multiple options case, we make claims `p₁ ∨ p₂ ∨ p₃` and `pᵢ → q` and then use `aesop` to complete. Here `q` is the goal.
* **conclude**: We make an assertion and prove it by default `aesop`.
* **contradiction**: Translate the statement to be contradicted to a statement `P`, then prove `P → False` using the given proof (with aesop having contradiction as a tactic). Finally follow the claim with `contradiction` (or `aesop` with contradiction).
-/

def Lean.Json.getObjString? (js: Json) (key: String) : Option String :=
  match js.getObjValAs? String key with
  | Except.ok s => some s
  | _ => none

open Lean Meta Elab Term PrettyPrinter Tactic Parser
def contextStatementOfJson (js: Json) : Option String :=
  match js.getObjString? "type" with
  | some "assume" =>
    match js.getObjValAs? String "statement" with
    | Except.ok s => some <| "Assume that " ++ s ++ "."
    | _ => none
  | some "let" =>
    let varSegment := match js.getObjString? "var" with
      | some "<anonymous>" => "We have "
      | some v => s!"Let {v} be"
      | _ => "We have "
    let kindSegment := match js.getObjString? "kind" with
      | some k => s!"a {k}"
      | _ => ""
    let valueSegment := match js.getObjString? "value" with
      | some v => s!"{v}"
      | _ => ""
    let propertySegment := match js.getObjString? "property" with
      | some p => s!"such that {p}"
      | _ => ""
    return s!"{varSegment} {kindSegment} {valueSegment} {propertySegment}."
  | some "cases" =>
    match js.getObjValAs? String "on" with
    | Except.ok s => some <| "We consider cases based on " ++ s ++ "."
    | _ => none
  | some "induction" =>
    match js.getObjValAs? String "on" with
    | Except.ok s => some <| "We induct on " ++ s ++ "."
    | _ => none
  | some "case" =>
    match js.getObjValAs? String "condition" with
    | Except.ok p =>
      /- one of "induction", "property" and "pattern" -/
      match js.getObjValAs? String "case-kind" with
      | Except.ok "induction" => some <| "Consider the induction case: " ++ p ++ "."
      | Except.ok "property" => some <| "Consider the case " ++ p ++ "."
      | Except.ok "pattern" => some <| "Consider the case of the form " ++ p ++ "."
      | _ => none
    | _ => none
  | _ => none

def localDeclExists (name: Name) (type : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  match lctx.findFromUserName? name with
  | some (.cdecl _ _ _ dtype ..) => isDefEq dtype type
  | _ => return false

partial def dropLocalContext (type: Expr) : MetaM Expr := do
  match type with
  | .forallE name binderType body _ => do
    if ← localDeclExists name binderType then
        dropLocalContext body
    else
      return type
  | _ => return type

variable (server: ChatServer := ChatServer.openAI)(params : ChatParams := {}) (numSim: Nat := 8)(numConcise numDesc : ℕ := 0)
  (dataMap : HashMap String (Array ((String × String × Bool × String) × FloatArray)) := HashMap.empty )


def theoremInContext? (ctx: Array Json)(statement: String): TermElabM (Option Expr) := do
  let mut context := #[]
  for js in ctx do
    match contextStatementOfJson js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) statement
  let type? ← translateToProp?
    fullStatement.trim server params numSim numConcise numDesc simpleChatExample dataMap
  type?.mapM <| fun e => dropLocalContext e

def purgeLocalContext: Syntax.Command →  TermElabM Syntax.Command
| `(command|def $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delab type
  `(command|def $name : $type := $value)
| `(command|theorem $name  : $type := $value) => do
  let typeElab ← elabType type
  let type ← dropLocalContext typeElab
  let type ← delab type
  `(command|theorem $name : $type := $value)
| stx => return stx

def defnInContext? (ctx: Array Json)(statement: String) : TermElabM (Option Syntax.Command) := do
  let mut context := #[]
  for js in ctx do
    match contextStatementOfJson js with
    | some s => context := context.push s
    | none => pure ()
  let fullStatement := context.foldr (· ++ " " ++ ·) statement
  let cmd? ←
    translateDefCmdM? fullStatement server params numSim numConcise numDesc docChatExample dataMap
  let cmd? ← cmd?.mapM purgeLocalContext
  return cmd?

open Lean.Parser.Term
/--
Convert theorem or definition to `have` or `let`
-/
def commandToTactic (cmd: Syntax.Command) : TermElabM Syntax.Tactic := do
  match cmd with
  | `(theorem $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| have $name $letArgs* : $type := $value)
  | `(def $name:ident $args:bracketedBinder* : $type := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs* : $type := $value)
  | `(def $name:ident $args:bracketedBinder* := $value) =>
      let mut letArgs := #[]
      for arg in args do
        let arg' ← `(letIdBinder| $arg:bracketedBinder)
        letArgs := letArgs.push arg'
      `(tactic| let $name $letArgs*  := $value)
  | _ => `(tactic| sorry)

open Lean Meta Tactic
#check binderIdent

def inductionCase (name: String)(condition: String)
    (pf: Array Syntax.Tactic) : TermElabM Syntax.Tactic := do
  match condition with
  | "base" =>
      let zeroId := mkIdent `zero
      let zeroArg ← `(caseArg| $zeroId:ident)
      `(tactic| case $zeroArg => $pf*)
  | _ =>
      let nId := mkIdent name.toName
      let succId := mkIdent `succ
      let succId' ← `(Lean.binderIdent| $succId:ident)
      let ihId := mkIdent `ih
      let ihId' ← `(Lean.binderIdent| $ihId:ident)
      `(tactic| case $succId' $nId:ident $ihId' => $pf*)

def inductionCases (name: String)
    (condPfs : Array (String × Array Syntax.Tactic))
    : TermElabM <| Array Syntax.Tactic := do
  let nId := mkIdent name.toName
  let mut cases := #[← `(tactic| induction $nId:ident)]
  for (cond, pf) in condPfs do
    let caseTac ← inductionCase name cond pf
    cases := cases.push caseTac
  return cases

def conditionCases (cond₁ cond₂ : String)
    (pf₁ pf₂ : Array Syntax.Tactic) : TermElabM <| Array Syntax.Tactic := do
  let condTerm₁ :=
    runParserCategory (← getEnv) `term cond₁ |>.toOption.get!
  let condTerm₂ :=
    runParserCategory (← getEnv) `term cond₂ |>.toOption.get!
  let condTerm₁' : Syntax.Term := ⟨condTerm₁⟩
  let condTerm₂' : Syntax.Term := ⟨condTerm₂⟩
  let ass₂ ← `(tactic| have : $condTerm₂' := by aesop)
  let pf₂' := #[ass₂] ++ pf₂
  let posId := mkIdent `pos
  let negId := mkIdent `neg
  let posId' ← `(caseArg| $posId:ident)
  let negId' ← `(caseArg| $negId:ident)
  return #[← `(tactic| by_cases $condTerm₁'), ← `(tactic| case $posId' => $pf₁*), ← `(tactic| case $negId' => $pf₂'*)]

def matchAltTac := Term.matchAlt (rhsParser := matchRhs)

def matchCases (discr: String)
    (pat_pfs: Array <| String × Array Syntax.Tactic) : TermElabM Syntax.Tactic := do
  let mut alts : Array <| TSyntax ``matchAltTac := #[]
  for (pat, pf) in pat_pfs do
    let patTerm :=
      runParserCategory (← getEnv) `term pat |>.toOption.get!
    let patTerm' : Syntax.Term := ⟨patTerm⟩
    let m ← `(matchAltTac| | $patTerm' => $pf*)
    alts := alts.push m
  let alts' : Array <| TSyntax ``matchAlt := alts.map fun alt => ⟨alt⟩
  let discrTerm :=
    runParserCategory (← getEnv) `term discr |>.toOption.get!
  let discrTerm' : Syntax.Term := ⟨discrTerm⟩
  `(tactic| match $discrTerm':term with $alts':matchAlt*)

def groupCasesAux (cond_pfs: List <| String × Array Syntax.Tactic)
    : TermElabM <| Array Syntax.Tactic := do
    match cond_pfs with
    | [] => return #[← `(tactic| aesop)]
    | (cond, pf) :: tail => do
      let condTerm :=
        runParserCategory (← getEnv) `term cond |>.toOption.get!
      let condTerm' : Syntax.Term := ⟨condTerm⟩
      let tailTacs ← groupCasesAux tail
      let posId := mkIdent `pos
      let negId := mkIdent `neg
      let posId' ← `(caseArg| $posId:ident)
      let negId' ← `(caseArg| $negId:ident)
      return #[← `(tactic| by_cases $condTerm':term), ← `(tactic| case $posId' => $pf*), ← `(tactic| case $negId' => $tailTacs*)]

def groupCases (cond_pfs: List <| String × Array Syntax.Tactic)
    (union_pfs: Array Syntax.Tactic):
    TermElabM <| Array Syntax.Tactic := do
  let conds := cond_pfs.map (·.1)
  let env ← getEnv
  let condTerms := conds.map fun cond =>
    runParserCategory env `term cond |>.toOption.get!
  let orAll : Syntax.Term ←  match condTerms with
    | [] => do
      let falseId := mkIdent `False
      `($falseId:ident)
    | h :: t =>
      let t' : List Syntax.Term := t.map fun term => ⟨term⟩
      t'.foldlM (fun acc cond => `($acc ∨ $cond)) ⟨h⟩
  let casesTacs ← groupCasesAux cond_pfs
  let head ← `(tactic| have : $orAll := by $union_pfs*)
  return #[head] ++ casesTacs


def powerTactics : CoreM <| List <| TSyntax ``tacticSeq := do
  return [← `(tacticSeq| omega), ← `(tacticSeq| ring), ← `(tacticSeq| linarith), ← `(tacticSeq| norm_num), ← `(tacticSeq| positivity), ← `(tacticSeq| gcongr), ←`(tacticSeq| contradiction), ← `(tacticSeq| tauto)]

def powerRules (weight sorryWeight: Nat) : MetaM <| List <| TSyntax `Aesop.rule_expr := do
  let tacs ← powerTactics
  let rules ← tacs.mapM fun tac => AesopSyntax.RuleExpr.ofTactic tac (some weight)
  return rules ++ [← AesopSyntax.RuleExpr.sorryRule sorryWeight]

def suggestionRules (names: List Name) (weight: Nat := 90)
    (rwWeight: Nat := 50) : MetaM <| List <| TSyntax `Aesop.rule_expr := do
  let tacs ← names.mapM fun n => AesopSyntax.RuleExpr.ofName n (some weight)
  let rws ← names.mapM fun n => AesopSyntax.RuleExpr.rewriteName n (some rwWeight)
  let rwsFlip ← names.mapM fun n => AesopSyntax.RuleExpr.rewriteName n (some rwWeight) true
  return tacs ++ rws ++ rwsFlip

def aesopTactic (weight sorryWeight: Nat) (names: List Name) :
    MetaM <| Syntax.Tactic := do
  let rules ← powerRules weight sorryWeight
  let sugRules ← suggestionRules names
  AesopSyntax.fold (rules ++ sugRules).toArray

def haveForAssertion (weight sorryWeight: Nat) (type: Syntax.Term)
  (premises: List Name) :
    MetaM <| Syntax.Tactic := do
  let tac ← aesopTactic weight sorryWeight premises
  `(tactic| have : $type := by $tac:tactic)

elab "dl!" t: term : term => do
let t ← elabType t
  let t' ← dropLocalContext t
  return t'

set_option linter.unusedVariables false in
def eg_drop (n m: Nat)  := dl! (∀ n m: Nat, n = n + 1 → False)

#print eg_drop
#check caseArg
