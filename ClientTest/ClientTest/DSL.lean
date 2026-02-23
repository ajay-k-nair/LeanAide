import LeanAideCore
import Mathlib

open LeanAide

#leanaide_connect
-- #leanaide_connect "http://10.134.13.103:7654"

set_option trace.leanaide.translate.debug true

#generate TheoremWithCode from "There are infinitely many odd numbers" as testToken

#lookup testToken

#eval LeanAidePipe.response <| json% {"task": "echo"}

def text : TheoremStatementText :=⟨"There are infinitely many odd numbers"⟩

def tokenM := mkQueryM text TheoremWithCode

#eval tokenM

-- #aide_eval getQueryM? TheoremWithCode tokenM

set_option lean_aide.translate.prompt_size 7

def tokenM' := mkQueryM text TheoremWithCode

#eval tokenM'

-- #aide_eval getQueryM? TheoremWithCode tokenM'


def tokenM'' := mkQueryM "There are infinitely many odd numbers" TheoremWithCode

#eval tokenM''
