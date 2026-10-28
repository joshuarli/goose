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

def eachCount (fuel : Nat) (config : EvalConfig) (view : RuntimeView) : EvalM Nat := do
  if view.dynamic then do pure (← arrayLength (← readLoc fuel config.layout view.location)).1 else pure view.count

def eachBody (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) : EvalM Flow := do
  let location : Goose.Core.Loc := ⟨view.location.root, view.location.path ++ [view.start + current]⟩
  let value ← if byRef then pure (Value.ref location) else readLoc fuel config.layout location
  let pre := (localVar, value) :: (index.toList.map fun index => (index, Value.int .i64 current))
  match (← loopBody fuel config environment pre body) with
  | .normal _ | .continuing => execEach fuel config environment localVar index byRef body view (current + 1)
  | .breaking value => pure (.normal (value.getD .unit))

def eachCountResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) : ExecutionStep Nat → ExecutionStep Flow
  | .ok count state => if current < count then
      eachBodyResult fuel config environment localVar index byRef body view current
        (eachElement fuel config localVar index byRef view current state)
    else .ok (.normal .unit) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem eachCount_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) (before : ExecutionState) :
    execEach (fuel + 1) config environment localVar index byRef body view current before =
      eachCountResult fuel config environment localVar index byRef body view current
        (eachCount fuel config view before) := by
  cases dynamic : view.dynamic with
  | false =>
      simp only [execEach, eachCount, dynamic, Bool.false_eq_true, ↓reduceIte, bind, pure, eachCountResult]
      split
      · exact eachBody_source fuel config environment localVar index byRef body view current before
      · rfl
  | true =>
      simp only [execEach, eachCount, dynamic, ↓reduceIte, bind, pure, eachCountResult]
      cases read : readLoc fuel config.layout view.location before with
      | ok value afterRead =>
          simp only [read, bind, pure]
          cases length : arrayLength value afterRead with
          | ok count afterLength =>
              simp only [length, bind, pure]
              split
              · exact eachBody_source fuel config environment localVar index byRef body view current afterLength
              · rfl
          | stop | escape | jump => simp_all [bind, pure]
      | stop | escape | jump => simp_all [bind, pure]

#print axioms eachCount_source

#print axioms eachBody_source
end Goose.Proofs.ConstructionGhostEachCore
