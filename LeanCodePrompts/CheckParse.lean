import Lean
import Lean.Meta
import Lean.Elab
import Lean.Parser
import Std
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Set
import LeanCodePrompts.Basic
open Lean Meta Std Elab Parser Mathlib Set
 
def s : Set Nat := fun _ => true
#check s ∩ s

def depsPrompt : IO (Array String) := do
  let file := System.mkFilePath ["data/types.txt"]
  IO.FS.lines file

syntax "(" term ")" : term
syntax "λ" ident "," term : term
syntax "λ"  ident ":" term  "," term : term
syntax "λ" "(" ident ":" term ")" "," term : term
syntax "⇑" term : term
macro_rules
| `(λ $x:ident : $type:term , $y:term) => 
  `(fun ($x : $type)  => $y)
| `(λ ( $x:ident : $type:term ) , $y:term) => 
  `(fun ($x : $type)  => $y)


def checkTerm (s : String) : MetaM Bool := do
  let env ← getEnv
  let chk := runParserCategory env `term  s
  match chk with
  | Except.ok _  => pure true
  | Except.error _  => pure false

#eval checkTerm "(fun x : Nat => x + 1)"

syntax term "•" term : term
syntax term "⊆" term : term
syntax term "⊂" term : term
syntax term "∩" term : term


#eval checkTerm "a • s"


#eval checkTerm "λ x : Nat, x + 1"

def checkStatements : MetaM (List (String × Bool)) := do
  let prompts ← depsPrompt
  (prompts.toList.take 50).mapM fun s => 
    do return (s, ← checkTerm s)

#eval checkStatements