import Lean
import LeanAideCore.Aides
import LeanAideCore.ChatClient
import LeanAideCore.Prompts
import LeanAideCore.Kernel

/-!
## DSL and Discussion types

Types for a discussion thread involving chatbots, humans and leanaide. Wrapper types for messages and an indexed inductive type for a discussion thread.

* The main line for the present code is
`TheoremText` → `TheoremCode` → `Document` → `StructuredDocument` → `TheoremCode`
* We may also upload a document or treat a response as a document (if the query is appropriate). But these will be *informal documents*.
-/

namespace LeanAide

open Lean Meta Elab Term

/-- A query message in a discussion thread. -/
structure Query where
  message : String
  queryParams : Json := Json.mkObj []
deriving Inhabited, Repr, ToJson, FromJson

/-- A response message in a discussion thread. -/
structure Response where
  message : String
  responseParams : Json := Json.mkObj []
deriving Inhabited, Repr, ToJson, FromJson

structure TheoremText where
  name? : Option Name
  text : String
deriving Inhabited, Repr, ToJson, FromJson

def thmText (s: String) (name? : Option Name := none) : TheoremText := { text := s , name? := name? }

structure Conjecture where
  text : String
  name: Name
  type : Expr
  statement : Syntax.Command
deriving Inhabited, Repr

structure TheoremCode where
  text : String
  name: Name
  type : String
  statement : String
deriving Inhabited, Repr, ToJson, FromJson

def TheoremCode.ofNameM (name: Name) : TermElabM TheoremCode := do
  let env ← getEnv
  let some text ← findDocString? env name | throwError "No doc string for {name}"
  let info ← getConstInfo name
  let typeStr ← ppExpr info.type
  let typeStx ← PrettyPrinter.delab info.type
  let nameIdent := mkIdent <| name ++ "prop".toName
  let statement ← `(command| def $nameIdent : Prop := $typeStx)
  return { text := text, name := name, type := typeStr.pretty, statement := (← PrettyPrinter.ppCommand statement).pretty }

instance : Proxy Conjecture  where
  β := TheoremCode
  to t := do
    let typeStr ← ppExpr t.type
    let stmtStr ← PrettyPrinter.ppCommand t.statement
    return { text := t.text, name := t.name, type := typeStr.pretty, statement := stmtStr.pretty }
  of t := do
    let .ok typeStx := Parser.runParserCategory (← getEnv) `term t.type | throwError "Failed to parse type"
    let typeExpr ← elabType typeStx
    let .ok stmtCmd := Parser.runParserCategory (← getEnv) `command t.statement | throwError "Failed to parse statement"
    return { text := t.text, name := t.name, type := typeExpr, statement := ⟨stmtCmd⟩ }


instance : InverseProxy TheoremCode  where
  α := Conjecture
  of t := do
    let .ok typeStx := Parser.runParserCategory (← getEnv) `term t.type | throwError "Failed to parse type"
    let typeExpr ← elabType typeStx
    let .ok stmtCmd := Parser.runParserCategory (← getEnv) `command t.statement | throwError "Failed to parse statement"
    return { text := t.text, name := t.name, type := typeExpr, statement := ⟨stmtCmd⟩ }
  to t := do
    let typeStr ← ppExpr t.type
    let stmtStr ← PrettyPrinter.ppCommand t.statement
    return { text := t.text, name := t.name, type := typeStr.pretty, statement := stmtStr.pretty }



structure DefinitionText where
  text : String
deriving Inhabited, Repr, ToJson, FromJson

structure DefinitionCodeM where
  name: Name
  text : String
  statement : Syntax.Command
deriving Inhabited, Repr

structure ProofDocument where
  name : Name
  content : String
deriving Inhabited, Repr, ToJson, FromJson

structure StructuredProof where
  name : Name
  json: Json
deriving Inhabited, Repr, ToJson, FromJson

structure ProofCode where
  name : Name
  code : TSyntax ``commandSeq
deriving Inhabited, Repr

structure Comment where
  message : String
  user : String
deriving Inhabited, Repr, ToJson, FromJson

class Content (α : Type) where
  content : α → String

instance : Content Query where
  content q := q.message

instance : Content Response where
  content r := r.message

instance : Content ProofDocument where
  content d := d.content

instance : Content Comment where
  content c := c.message

inductive ResponseType where
  | start | query | response | document | structuredDocument | code | comment | theoremText | theoremCode | definitionText | definitionCode | documentCode
deriving Repr, Inhabited

def ResponseType.toType : ResponseType → Type
| .start => Unit
| .query => Query
| .response => Response
| .document => ProofDocument
| .structuredDocument => StructuredProof
| .code => ProofCode
| .comment => Comment
| .theoremText => TheoremText
| .theoremCode => TheoremCode
| .definitionText => DefinitionText
| .definitionCode => DefinitionCodeM
| .documentCode => ProofCode

instance (rt: ResponseType) : Repr rt.toType where
  reprPrec := by
    cases rt <;> simp [ResponseType.toType] <;> apply reprPrec



class ResponseType.OfType (α : Type)  where
  rt : ResponseType
  ofType : α → rt.toType := by exact fun x ↦ x
  eqn : rt.toType = α := by rfl

instance unitOfType : ResponseType.OfType Unit where
  rt := .start

instance queryOfType : ResponseType.OfType Query where
  rt := .query

instance responseOfType : ResponseType.OfType Response where
  rt := .response

instance documentOfType : ResponseType.OfType ProofDocument where
  rt := .document

instance structuredDocumentOfType : ResponseType.OfType StructuredProof where
  rt := .structuredDocument

instance codeOfType : ResponseType.OfType ProofCode where
  rt := .code

instance commentOfType : ResponseType.OfType Comment where
  rt := .comment

instance theoremTextOfType : ResponseType.OfType TheoremText where
  rt := .theoremText

instance theoremCodeOfType : ResponseType.OfType TheoremCode where
  rt := .theoremCode

instance definitionTextOfType : ResponseType.OfType DefinitionText where
  rt := .definitionText

instance definitionCodeOfType : ResponseType.OfType DefinitionCodeM where
  rt := .definitionCode

instance documentCodeOfType : ResponseType.OfType ProofCode where
  rt := .documentCode



inductive Discussion : Type → Type where
  | start  (sysPrompt? : Option String)  : Discussion Unit
  | query {rt: ResponseType} (init: Discussion rt.toType) (q : Query) : Discussion Query
  | response (init: Discussion Query) (r : Response) : Discussion Response
  | translateTheoremQuery (init : Discussion Unit) (tt : TheoremText) : Discussion TheoremText
  | theoremTranslation (init : Discussion TheoremText) (tc : TheoremCode) :Discussion TheoremCode
  | translateDefinitionQuery (init : Discussion Unit) (dt : DefinitionText) : Discussion DefinitionText
  | definitionTranslation (init : Discussion DefinitionText) (dc : DefinitionCodeM) : Discussion DefinitionCodeM
  | comment {rt : ResponseType} (init: Discussion rt.toType) (c : Comment) : Discussion Comment
  | proveTheoremQuery (init: Discussion Unit) (tt : TheoremText) : Discussion TheoremText
  | proofDocument (init: Discussion TheoremCode) (doc : ProofDocument) (prompt? : Option String := none) :  Discussion ProofDocument
  | proofStructuredDocument (init: Discussion ProofDocument) (sdoc : StructuredProof) (prompt? : Option String := none) (schema : Option Json := none) :  Discussion StructuredProof
  | proofCode (init: Discussion StructuredProof) (tc : ProofCode) : Discussion ProofCode
  | rewrittenDocument (init: Discussion ProofDocument ) (doc : ProofDocument) (prompt? : Option String := none) :  Discussion ProofDocument
  | edit {rt : ResponseType} (userName? : Option String := none) : Discussion rt.toType  → Discussion rt.toType
deriving Repr

namespace Discussion

def last {α} : Discussion α → α
| start _  => ()
| query _ q => q
| response _ r => r
| translateTheoremQuery _ tt => tt
| theoremTranslation _ tc => tc
| translateDefinitionQuery _ d =>  d
| definitionTranslation _ d =>  d
| comment _ d => d
| proveTheoremQuery _ tt => tt
| proofDocument _ doc _  => doc
| proofStructuredDocument _ sdoc _ _ => sdoc
| proofCode _ tc => tc
| rewrittenDocument _ doc _ => doc
| edit _ d => d.last

def lastM {α} : TermElabM (Discussion α) → TermElabM α
| d => do return (← d).last

def length {α} : Discussion α → Nat
| start _  => 0
| query init _ => init.length + 1
| response init _ => init.length + 1
| translateTheoremQuery init _ => init.length + 1
| theoremTranslation init _ => init.length + 1
| translateDefinitionQuery init _ => init.length + 1
| definitionTranslation init _ => init.length + 1
| comment init _ => init.length + 1
| proveTheoremQuery init _ => init.length + 1
| proofDocument init _ _ => init.length + 1
| proofStructuredDocument init _ _ _ => init.length + 1
| proofCode init _ => init.length + 1
| rewrittenDocument init _ _ => init.length + 1
| edit _ d => d.length

def mkQuery {α} [inst : ResponseType.OfType α ] (prev : Discussion α) (q : Query) : Discussion Query := by
  apply Discussion.query (rt := inst.rt)  _ q
  rw [inst.eqn]
  exact prev

def addQuery {α} [inst : ResponseType.OfType α ] (prev : Discussion α) (s : String) : Discussion Query :=
  prev.mkQuery { message := s }

def mkComment {α} [inst : ResponseType.OfType α ] (prev : Discussion α) (c : Comment) : Discussion Comment := by
  apply Discussion.comment (rt := inst.rt) _ c
  rw [inst.eqn]
  exact prev

class Append (α β : Type) where
  append : Discussion α → β → Discussion β

instance [Append α β] : HAdd (Discussion α) β (Discussion β) where
  hAdd := Append.append

instance appendQuery (α : Type) [inst : ResponseType.OfType α] : Append α Query where
  append d q := d.mkQuery q

instance appendResponse : Append Query Response where
  append d r := Discussion.response d r

instance appendComment (α : Type) [inst : ResponseType.OfType α] : Append α Comment where
  append d c := d.mkComment c

instance appendTheoremText : Append Unit TheoremText where
  append d tt := Discussion.translateTheoremQuery d tt
instance appendTheoremCode : Append TheoremText TheoremCode where
  append d tc := Discussion.theoremTranslation d tc
instance appendDefinitionText : Append Unit DefinitionText where
  append d dt := Discussion.translateDefinitionQuery d dt
instance appendDefinitionCode : Append DefinitionText DefinitionCodeM where
  append d dc := Discussion.definitionTranslation d dc
instance appendProveTheorem : Append Unit TheoremText where
  append d tt := Discussion.proveTheoremQuery d tt
instance appendProofDocument : Append TheoremCode ProofDocument where
  append d doc := Discussion.proofDocument d doc
instance appendProofStructuredDocument : Append ProofDocument StructuredProof where
  append d sdoc := Discussion.proofStructuredDocument d sdoc
instance appendProofCode : Append StructuredProof ProofCode where
  append d tc := Discussion.proofCode d tc
instance appendRewrittenDocument : Append ProofDocument ProofDocument where
  append d doc := Discussion.rewrittenDocument d doc

def append {α β : Type} [r : Append α β] (d : Discussion α) (b : β) : Discussion β :=
  r.append d b

def initQuery (q: Query) (sysPrompt : Option String := none) : Discussion Query :=
  Discussion.start sysPrompt |>.mkQuery q

def initComment (c: Comment) (sysPrompt : Option String := none) : Discussion Comment :=
  Discussion.start sysPrompt |>.mkComment c

end Discussion
class GenerateM (α β : Type) where
  generateM : α →  TermElabM β

def generateM {α}  (β : Type) [r : GenerateM α β] (a : α) : TermElabM β :=
  r.generateM a

set_option synthInstance.checkSynthOrder false in
instance GenerateM.composition (α γ : Type) (β : outParam Type) [r1 : GenerateM α β] [r2 : GenerateM β γ] : GenerateM α γ where
  generateM a := do
    let d ← r1.generateM a
    r2.generateM d

set_option synthInstance.checkSynthOrder false in
def GenerateM.compositionProxyTo (α γ : Type)  [r1 : Proxy α ] [r2 : GenerateM r1.β γ] : GenerateM α γ where
  generateM a := do
    let d ← r1.to a
    r2.generateM d

set_option synthInstance.checkSynthOrder false in
def GenerateM.compositionProxyOf (α : Type) {β : outParam Type}  [ToJson β] [FromJson β] [Repr β] [r2 : InverseProxy β][r1 : GenerateM α β] : GenerateM α r2.α where
  generateM a := do
    let d ← r1.generateM a
    r2.of d

namespace Discussion
class Continuation (α β : Type) where
  continueM : (Discussion α) → TermElabM (Discussion β)

def continueM {α} (β : Type) [r : Continuation α β] (d : Discussion α) : TermElabM (Discussion β) :=
  r.continueM d

set_option synthInstance.checkSynthOrder false in
instance Continuation.composition (α γ : Type) (β : outParam Type) [r1 : Continuation α β] [r2 : Continuation β γ] : Continuation α γ where
  continueM d := do
    let d' ← r1.continueM d
    r2.continueM d'

instance {α β : Type} [inst : GenerateM α β][inst' : Append α β] : Continuation α β where
  continueM d := do
    let x ← inst.generateM d.last
    return d.append x

instance {α β : Type} [inst : GenerateM α β][inst' : Append α β] : GenerateM (Discussion α) (Discussion β) where
  generateM d := do
    let x ← inst.generateM d.last
    return d.append x


class ContinuationCommands (α β : Type) where
  continueCommandsM : (Discussion α) → Syntax.Term → TermElabM (List Syntax.Command × (Discussion β) × Name)

set_option synthInstance.checkSynthOrder false in
instance ContinuationCommands.composition (α γ : Type) (β : outParam Type) [r1 : ContinuationCommands α β] [r2 : ContinuationCommands β γ] : ContinuationCommands α γ where
  continueCommandsM d stx := do
    let (cmds1, b, name1) ← r1.continueCommandsM d stx
    let (cmds2, c, name2) ← r2.continueCommandsM b (mkIdent name1)
    return (cmds1 ++ cmds2, c, name2)

instance {α β : Type} [inst : GenerateM α β][inst' : Append α β] [inst'' : DefinitionCommand β] : ContinuationCommands α β where
  continueCommandsM d stx := do
    let x ← inst.generateM d.last
    let (elemDef, name) ← definitionCommandPair x
    let descName := name ++ "chat".toName
    let appendIdent := mkIdent ``append
    let descId := mkIdent descName
    let nameIdent := mkIdent name
    let cmd ← `(command| def $descId := $appendIdent $stx $nameIdent)
    let d' := d.append x
    return ([elemDef, cmd], d', descName)

/--
The simplified chat history. In case of complex queries with examples etc., a simple query is substituted.
-/
def historyM {α : Type } (d : Discussion α ) :
  MetaM ((List ChatPair) × Option String) := do
  match d with
  | start sysPrompt? => return ([], sysPrompt?)
  | query init q => do
    let (h, sp?) ← init.historyM
    return addQuery h sp? q.message
  | response init r => do
    let (h, sp?) ← init.historyM
    return addResponse h sp? r.message
  | comment init c => do
    let (h, sp?) ← init.historyM
    return addQuery h sp? c.message
  | translateTheoremQuery init tt =>
    let (h, sp?) ← init.historyM
    let q := s!"Translate the following theorem statement into a formal Lean theorem statement and its type:\n{tt.text}\n"
    return addQuery h sp? q
  | theoremTranslation init tc =>
    let (h, sp?) ← init.historyM
    let q := s!"Translate the following theorem statement into a formal Lean theorem statement and its type:\n{tc.text}\n"
    let response := s!"{tc.statement}"
    return addSyntheticPair h sp? q response
  | translateDefinitionQuery init tt =>
    let (h, sp?) ← init.historyM
    let q := s!"Translate the following definition into a formal Lean definition and its type:\n{tt.text}\n"
    return addQuery h sp? q
  | definitionTranslation init tt =>
    let (h, sp?) ← init.historyM
    let q := s!"Translate the following definition into a formal Lean definition and its type:\n{tt.text}\n"
    let response := s!"{tt.statement}"
    return addSyntheticPair h sp? q response
  | proveTheoremQuery init tt =>
    let (h, sp?) ← init.historyM
    let q := s!"Provide a detailed proof of the following theorem:\n{tt.text}\n"
    return addQuery h sp? q
  | proofDocument init doc prompt? =>
    let statement := init.last.text
    let (h, sp?) ← init.historyM
    let q := s!"Provide a detailed proof of the following theorem:\n{statement}\n"
    return addSyntheticPair h sp? q doc.content
  | proofStructuredDocument init sdoc _ _ => do
    let (h, sp?) ← init.historyM
    let q := "Write the proof in the structured JSON format of LeanAide."
    let response := s!"{sdoc.json.pretty}"
    return addSyntheticPair h sp? q response
  | proofCode init c =>
    let (h, sp?) ← init.historyM
    let q := "Write the proof in Lean code."
    let response ← showCommandSeq c.code
    return addSyntheticPair h sp? q response
  | rewrittenDocument init _ _ => init.historyM
  | edit _ d => d.historyM
where
  addQuery (h: List ChatPair) (sp? : Option String) (q: String) : (List ChatPair) × Option String :=
    let sp? := sp?.map (fun s => s.trim ++ "\n")
    let sp := sp?.getD ""
    (h, some (sp ++ q))
  addResponse (h: List ChatPair) (sp? : Option String) (r: String) : (List ChatPair) × Option String :=
    match sp? with
    | some sp =>
      let newPair : ChatPair := {user := sp, assistant := r}
      (h ++ [newPair], none)
    | none =>
      match h.getLast? with
      | some lastPair => (h.dropLast ++ [{lastPair with assistant := lastPair.assistant ++ "\n" ++ r}], none) -- response appended to last
      | none => (h, none) -- response to nothing is discarded
  addSyntheticPair (h: List ChatPair) (sp? : Option String) (q: String) (response : String) : (List ChatPair) × Option String :=
    match sp? with
    | some sp =>
      let newPair : ChatPair := {user := sp, assistant := response}
      (h ++ [newPair], none)
    | none =>
      (h ++ [ {user := q, assistant := response} ], none)
section

local instance queryResponse : GenerateM Query Response where
  generateM q := do
    let res := { message := s!"This is a response to: {q.message}", responseParams := Json.null }
    return res


local instance responseComment : GenerateM Response Comment where
  generateM r := do
    let c := { message := s!"This is a comment on: {r.message}", user := "user" }
    return c

def q : Discussion Query :=
  initQuery { message := "What is 2+2?"}

-- #eval q.continueM Comment


-- #eval generateM Comment  ({ message := "What is 2+2?"} : Query)

-- #eval generateM (Discussion Comment)  q


end

def isDiscussionType (e: Expr) : MetaM Bool := do
  let typeExpr := mkSort (Level.succ Level.zero)
  let mvar ← mkFreshExprMVar typeExpr
  let discType := mkApp (mkConst ``Discussion) mvar
  isDefEq e discType

elab "isDiscussionType%" e:term : term => do
  let e ← elabTerm e none
  if (← isDiscussionType e) then
    mkConst ``true
  else
    mkConst ``false

-- #eval isDiscussionType% (Discussion Query)

end Discussion

end LeanAide
