import Batteries.CodeAction.Misc
import Lean.Meta.Tactic.TryThis

open Lean Std Parser CodeAction Elab Command Server Lsp RequestM Snapshots Tactic

syntax (name := translationComment) "//-" commentBody : command

@[command_elab translationComment]
def translationCommentElab : CommandElab := fun _ ↦ pure ()

def extractTranslationCommentBody : TSyntax ``translationComment → String
  | ⟨.node _ _ #[_, .atom _ doc]⟩ => doc.dropRight 2
  | stx => panic! s!"Ill-formed translation comment syntax: {stx}."

def dummyTranslateStatement (_stmt : String) : TermElabM String :=
  pure "theorem fermat_last : ∀ x y z n : Nat, n > 2 → x^n + y^n = z^n → x*y*z = 0 := by \n  sorry"

@[command_code_action translationComment]
def translationCommentCodeAction : CommandCodeAction := fun _params _snap _ctx _info ↦ do
  let .node (.ofCommandInfo cmdInfo) _ := _info | return #[]
  let doc ← readDoc

  let eager := {
    title := "Auto-formalise to Lean."
    kind? := "quickfix",
    isPreferred? := true }
  return #[{
    eager
    lazy? := some do
      let stx := cmdInfo.stx
      let .some range := stx.getRange? | return eager
      let text := extractTranslationCommentBody ⟨stx⟩
      let res ← EIO.toIO (fun _ ↦ .userError "Translation failed.") <| _snap.runTermElabM doc.meta <|
          dummyTranslateStatement text
      return { eager with
        edit? := some <| .ofTextEdit doc.meta.uri {
          range := doc.meta.text.utf8RangeToLspRange range,
          newText := s!"/-- {text}-/\n{res}"}}
    }]

#check TryThis.addSuggestion

@[command_code_action translationComment]
def translationCommentTryThis : CommandCodeAction := fun _params _snap _ctx _info ↦ do
  let .node (.ofCommandInfo cmdInfo) _ := _info | return #[]
  let doc ← readDoc

  let eager := {
    title := "Suggest a translation to Lean."
    kind? := "quickfix",
    isPreferred? := true }
  return #[{
    eager
    lazy? := some do
      let stx := cmdInfo.stx
      let .some range := stx.getRange? | return eager
      let text := extractTranslationCommentBody ⟨stx⟩
      EIO.toIO (fun _ ↦ .userError "Translation failed.") <|
        _snap.runTermElabM doc.meta <| do
          let res ← dummyTranslateStatement text
          let .ok thm := Parser.runParserCategory (← getEnv) `command res |
            throwError "Failed to parse result."
          TryThis.addSuggestion stx (⟨thm⟩ : TSyntax `command)
      return eager
    }]

//- Hello world -/
