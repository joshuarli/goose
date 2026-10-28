import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionGhostEachCore
open Goose.Construct

def eachElement (fuel : Nat) (config : EvalConfig) (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId)
    (byRef : Bool) (view : RuntimeView) (current : Nat) : EvalM (List (Goose.Core.VarId × Value)) := do
  let location : Goose.Core.Loc := ⟨view.location.root, view.location.path ++ [view.start + current]⟩
  let value ← if byRef then pure (Value.ref location) else readLoc fuel config.layout location
  pure ((localVar, value) :: (index.toList.map fun index => (index, Value.int .i64 current)))

def eachBodyResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) : ExecutionStep (List (Goose.Core.VarId × Value)) → ExecutionStep Flow
  | .ok pre state => (do
      match (← loopBody fuel config environment pre body) with
      | .normal _ | .continuing => execEach fuel config environment localVar index byRef body view (current + 1)
      | .breaking value => pure (.normal (value.getD .unit))) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem eachBody_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) (before : ExecutionState) :
    (do
      let location : Goose.Core.Loc := ⟨view.location.root, view.location.path ++ [view.start + current]⟩
      let value ← if byRef then pure (Value.ref location) else readLoc fuel config.layout location
      let pre := (localVar, value) :: (index.toList.map fun index => (index, Value.int .i64 current))
      match (← loopBody fuel config environment pre body) with
      | .normal _ | .continuing => execEach fuel config environment localVar index byRef body view (current + 1)
      | .breaking value => pure (.normal (value.getD .unit))) before =
    eachBodyResult fuel config environment localVar index byRef body view current
      (eachElement fuel config localVar index byRef view current before) := by
  cases byRef <;> simp only [eachElement, eachBodyResult, bind, pure, Bool.false_eq_true, ↓reduceIte]
  cases readLoc fuel config.layout ⟨view.location.root, view.location.path ++ [view.start + current]⟩ before <;> rfl

#print axioms eachBody_source
end Goose.Proofs.ConstructionGhostEachCore
