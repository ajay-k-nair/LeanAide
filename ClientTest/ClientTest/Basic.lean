import LeanAideCore
import Mathlib

open LeanAide

#leanaide_connect -- "http://10.134.13.103:7654"

#eval LeanAidePipe.response <| json% {"task": "echo"}
