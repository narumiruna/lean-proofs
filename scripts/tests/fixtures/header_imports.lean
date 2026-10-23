import Lean.Parser.Module

open Lean Lean.Parser

def main (args : List String) : IO Unit := do
  for path in args do
    let source ← IO.FS.readFile path
    let (header, _, messages) ← parseHeader (mkInputContext source path)
    let mut names : Array Json := #[]
    if let `(Module.header| $[module]? $[prelude]? $imports*) := header then
      for stx in imports do
        if let `(Module.import| $[public]? $[meta]? import $[all]? $mod) := stx then
          names := names.push (toJson mod.getId.toString)
    let mut errors : Array Json := #[]
    for message in messages.toList do
      errors := errors.push (toJson (← message.toString))
    IO.println (Json.mkObj [("path", toJson path), ("imports", Json.arr names),
                            ("errors", Json.arr errors)]).compress
