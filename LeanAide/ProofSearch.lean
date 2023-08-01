import LeanAide.AesopSearch
import LeanAide.Aides
import LeanAide.TheoremElab
import Lean
import Mathlib
open Lean Meta Elab

def powerTactics := #["gcongr", "ring", "linarith", "norm_num", "positivity", "polyrith"]

-- should eventually use premises
def proofSearchM (thm: String) : TermElabM <| Bool × Bool := do
  let type? ← elabThm thm 
  IO.println "Trying to prove"
  IO.println thm
  IO.println type?
  IO.println ""
  match type? with
  | Except.ok type => 
    let goal ←mkFreshExprMVar type
    let mvarId := goal.mvarId! 
    try 
      let goals ←
        runAesop 0.5 #[] #[] #[] powerTactics mvarId 
      return (true, goals.isEmpty)
    catch _ =>
      return (true, false)
  | Except.error _ => return (false, false)

def proofSearchCore (thm: String) : CoreM <| Bool × Bool  := 
  (proofSearchM thm).run'.run'

