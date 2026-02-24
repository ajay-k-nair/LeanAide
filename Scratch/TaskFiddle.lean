import Lean
import Mathlib

open Lean Meta Elab Tactic Parser

#eval 3

def slowFibIO : Nat → IO Nat
| 0 => pure 0
| 1 => pure 1
| n + 2 => do return (← slowFibIO (n)) + (←  slowFibIO (n + 1))

-- elab "run_io_task" : tactic => do
--   let _  ← (IO.asTask <|
--     do
--       setFib s!"Computed: {← slowFibIO 34} at {← IO.monoMsNow}"
--     ).toIO
--   return ()

-- example : 4 = 4 := by
--   run_io_task
--   rfl

-- #eval getFib

#check Core.CoreM.run -- {α : Type} → CoreM α → Core.Context → Core.State → EIO Exception (α × Core.State)
#check Meta.MetaM.run /-{α : Type} →
  MetaM α →
    optParam Meta.Context
        {...} →
      optParam Meta.State
          {...} →
        CoreM (α × Meta.State)
-/
#check Elab.runTactic /- MVarId →
  Syntax →
    optParam Term.Context
        {...} →
      optParam Term.State
          { levelNames := [], syntheticMVars := ∅, pendingMVars := ∅, mvarErrorInfos := ∅, letRecsToLift := [] } →
        MetaM (List MVarId × Term.State)-/
#check IO.asTask /- {α : Type} → IO α → optParam Task.Priority Task.Priority.default → BaseIO (Task (Except IO.Error α)) -/
#check evalTactic
#check Elab.runFrontend

def useTactic (type : Expr)
  (tacticCode : TSyntax `Lean.Parser.Tactic.tacticSeq) : TermElabM Expr :=
  Term.withoutErrToSorry do
    let code ← `(by $tacticCode)
    let term ← Elab.Term.elabTerm code (some type)
    Term.synthesizeSyntheticMVarsNoPostponing
    return term

def egProof : TermElabM Expr := do
  let typeStx ← `((1 : Nat) ≤ 2)
  let type ← Elab.Term.elabTerm typeStx none
  let code ← `(by linarith)
  let term  ← Elab.Term.elabTerm code (some type)
  Term.synthesizeSyntheticMVarsNoPostponing
  reduce <| term

example (n: Nat) : n + 1 ≤ n + 2 := by linarith

#eval egProof

elab "eg_proof" : term => do
  reduce <| ← egProof

def eg :  1 ≤ 2 := eg_proof

open Std.Internal.IO Async
def delayedWrite : Async Unit := do
  let now' ← Std.Time.PlainDateTime.now
  Async.sleep 3000
  let now ← Std.Time.PlainDateTime.now
  IO.FS.writeFile "delayed.txt" s!"This was written after a delay: {now} after starting at {now'}"

elab "#delayed_write" : command => do
  AsyncTask.block <| ←
    Async.toIO do
      delayedWrite

#delayed_write

#eval 3
