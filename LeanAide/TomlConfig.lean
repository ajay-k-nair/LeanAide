import Lake.Load.Toml
import LeanAide.PromptBuilder

open Lean Parser Lake
open System (FilePath)

open Toml

namespace LeanAide

def loadTableL (inp : IO String) : LogIO Table := do
  let ictx := mkInputContext (← inp) ("leanaide.toml")
  match ← loadToml ictx |>.toBaseIO with
  | Except.ok table => return table
  | .error log =>
    errorWithLog <| log.forM fun msg => do logError (← msg.toString)

def loadTableIO? (file: System.FilePath := "leanaide.toml") :
    IO <| Option Table := do
  if ← file.pathExists then
    let inp ← IO.FS.readFile file
    loadTableL (pure inp) |>.run?'
  else
    return none

def Translator.configureToml (translator: Translator)
  (file: System.FilePath := "leanaide.toml") : IO Translator := do
    match ← loadTableIO? file with
    | some table =>
      let translator ←
        StateT.run' (s := (#[] : Array DecodeError)) do
          let n ← table.tryDecodeD  `n translator.params.n
          let translator := {translator with params := {translator.params with n := n}}
          let tempFloat ← table.tryDecodeD  `temperature (translator.params.temp.toFloat)
          let temp := match JsonNumber.fromFloat? tempFloat with
          | .inr temp => temp
          | .inl _ => translator.params.temp
          let translator  := {translator with params := {translator.params with temp := temp}}
          let server? : Option Table ←
              table.tryDecode?  `server
          let server ← match server? with
            | none => pure translator.server
            | some server =>
              let model ←  server.tryDecodeD `model
                  translator.server.model
              let url? : Option String ←  server.tryDecode? `url
              let gemini ←
                server.tryDecodeD `gemini (model.startsWith "gemini")
              let azure ←  server.tryDecodeD `azure false
              let sysLess ←  server.tryDecodeD `no_sysprompt false
              if azure then pure <| ChatServer.azure else
              if gemini then pure <| .gemini model else
                  match url? with
                  | some url =>
                    pure <| ChatServer.generic model url none !sysLess
                  | none => pure <| ChatServer.openAI model
              pure translator.server
          let authKey? : Option String ← table.tryDecode? `auth_key
          let chatServer := server.addKeyOpt authKey?
          let translator : Translator := {translator with server := chatServer}
          let reasoning  ←  table.tryDecodeD `reasoning false
          let translator : Translator :=
            if reasoning then translator.reasoning else translator
          let examples? : Option Table  ← table.tryDecode? `examples
          let pb ← match examples? with
          | none => pure translator.pb
          | some table' =>
              let numSim ←  table'.tryDecodeD `docstrings 20
              let numConcise ←  table'.tryDecodeD `concise_descriptions 2
              let numDesc ←  table'.tryDecodeD `descriptions 2
              let embedUrl? ←  table'.tryDecode? `examples_url
              let pb₁ := PromptExampleBuilder.mkEmbedBuilder embedUrl? numSim numConcise numDesc
              let pb₂ := PromptExampleBuilder.searchBuilder 0 0 |>.simplify
              let pb := pb₁ ++ pb₂
              let pb := pb.simplify
              pure pb
          let translator := {translator with pb := pb}
          return translator
      return translator
    | none => return translator

def eg := "hello = 'this world'\nn = 42\n[leanaide]\nname = 'leanaide'"


def loadTable : LogIO <| Table × String × Nat × String := do
  let ictx := mkInputContext eg ("")
  match ← loadToml ictx |>.toBaseIO with
  | Except.ok table =>
    let (hello, n) ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        let hello ← table.tryDecodeD  `hello "decode world"
        let n ← table.tryDecodeD  `n 0
        return (hello, n)
    let t : Table ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        table.tryDecode  `leanaide
    let name ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        t.tryDecodeD `name "missing?"
    return (table, hello, n, name)
  | .error log =>
    errorWithLog <| log.forM fun msg => do logError (← msg.toString)


def loadHello : IO <| String × Nat × String:= do
  let hello? ← loadTable.toBaseIO
  match hello? with
  | some (_, hello, n, name) => return (hello, n, name)
  | none => return ("IO world", 12, "missing name")

-- #eval loadHello
