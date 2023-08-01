import LeanAide.AesopSearch
import LeanAide.Aides
import LeanAide.TheoremElab
import Lean
import Mathlib
open Lean Meta Elab

def powerTactics := #["gcongr", "ring", "linarith", "norm_num", "positivity", "polyrith"]

-- should eventually use premises
def proofSearchM (thm: String) : TermElabM Bool := do
  let type? ← elabThm thm 
  match type? with
  | Except.ok type => 
    let goal ←mkFreshExprMVar type
    let mvarId := goal.mvarId! 
    let goals ←
      runAesop 0.5 #[] #[``Nat.add_comm] #[] powerTactics mvarId 
    return goals.isEmpty
  | Except.error _ => return false

def proofSearchCore (thm: String) : CoreM Bool := 
  (proofSearchM thm).run'.run'

