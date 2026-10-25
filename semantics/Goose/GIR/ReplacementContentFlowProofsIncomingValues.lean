import Goose.GIR.Validate

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def edgeIncomingValues (func : Func) (value : ValueId) (target : BlockId)
    (args : List ValueId) : List ValueId :=
  match func.blocks[target]? with
  | none => []
  | some block => (block.params.zip args).filterMap fun pair =>
      if pair.1.1 = value then some pair.2 else none

def allIncomingValues (func : Func) (value : ValueId) : List ValueId :=
  func.blocks.toList.flatMap fun block => block.insts.flatMap fun inst =>
    match inst with
    | .term term => (termEdges term).flatMap fun pair => edgeIncomingValues func value pair.1 pair.2
    | _ => []

end Goose.GIR.ReplacementContentFlow.Model
