import Goose.Proofs.ConstructionGhostMaterialization

namespace Goose.Proofs.ConstructionGhostNonfixedDeclaration
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostMaterialization

def declarationContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (expression : Expr) (origin : Goose.Core.OriginId)
    (materialized : Option (Array Value)) : EvalM Flow := do
  let destination ← newDestination config.layout environment.act descriptor.ty .value origin none
    (materialized.map Array.size <|> producerCount? ⟨config.module, environment.vars⟩ expression)
  match materialized with
  | some values => copyValue fuel config.layout destination (.fixed values) origin none
  | none => buildExpr fuel config environment destination expression
  let destination ← completedReceivingDestination destination
  publishCarriers origin [.completed destination]
  let stored ← storedDestination destination
  bindRoot root (.stored { stored with ty := descriptor.ty, object := none })
  pure (.normal .unit)

def declarationAfterMaterialization (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (expression : Expr) (origin : Goose.Core.OriginId)
    (result : ExecutionStep (Option (Array Value))) : ExecutionStep Flow :=
  match result with
  | .ok materialized state => declarationContinuation fuel config environment descriptor root expression origin materialized state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem nonfixedDeclaration_execution (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr)
    (origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (found : environment.vars[localVar]? = some descriptor)
    (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root ready)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = none) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationAfterMaterialization fuel config environment descriptor root expression origin
        (materializeProducer fuel ⟨config.module, environment.vars⟩ expression
          (evalValue fuel config environment expression) ready) := by
  simp only [execStmt, found, bind, rootResult, nonfixed, ↓reduceIte, implementationFound, notNamed,
    pure, Option.isNone_none, Option.isSome_none, declarationAfterMaterialization, declarationContinuation]
  cases materializeProducer fuel ⟨config.module, environment.vars⟩ expression
      (evalValue fuel config environment expression) ready with
  | ok value state => cases value <;> rfl
  | stop | escape | jump => rfl

theorem nonfixedDeclaration_direct (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr)
    (origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root ready)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = none)
    (noMaterialization : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = none) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationContinuation fuel config environment descriptor root expression origin none ready := by
  rw [nonfixedDeclaration_execution fuel config environment localVar expression origin before ready
    descriptor root implementation found nonfixed rootResult implementationFound notNamed]
  rw [materializeProducer_none fuel ⟨config.module, environment.vars⟩ expression
    (evalValue fuel config environment expression) ready noMaterialization]
  rfl

theorem nonfixedDeclaration_materialized (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (path : List Nat) (localVar : Goose.Core.VarId) (expression : Expr)
    (origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl) (count : Nat)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root ready)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = none)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
    EvaluationTree config environment fuel (path ++ [0]) expression ready
      (evalValue fuel config environment expression ready) ∧
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationAfterMaterialization fuel config environment descriptor root expression origin
        (materializationContinuation (evalValue fuel config environment expression ready)) := by
  obtain ⟨tree, execution⟩ := materializeProducer_source_ghost fuel config environment path expression ready count materialized
  refine ⟨tree, ?_⟩
  rw [nonfixedDeclaration_execution fuel config environment localVar expression origin before ready
    descriptor root implementation found nonfixed rootResult implementationFound notNamed, execution]

private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"entry", #[], #[], #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩],
    .mk 0 [] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4,
  #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩], [(0, 1)], []⟩
private def sideEffectSource : Expr := .blockE
  (.mk 1 [.print [.text "once"] 0] (some (.lit .i64 7))) 0
private def directExpression : Expr :=
  .arrLit (.varr (.int .i64)) [sideEffectSource, .lit .i64 8] 0
private def materializedExpression : Expr := .blockE
  (.mk 1 [.print [.text "once"] 0]
    (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem directDeclarationWitness :
    ordinaryProducerCount? 39 ⟨witnessConfig.module, witnessEnvironment.vars⟩ directExpression = none ∧
    ∃ state, execStmt 40 witnessConfig witnessEnvironment (.letS 0 directExpression 0) .initial =
      .ok (.normal .unit) state ∧ state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  constructor
  · unfold witnessConfig witnessEnvironment directExpression sideEffectSource; cbv
  · refine ⟨stepState (execStmt 40 witnessConfig witnessEnvironment (.letS 0 directExpression 0) .initial), ?_, ?_⟩ <;>
      unfold witnessConfig witnessEnvironment directExpression sideEffectSource stepState <;> cbv

theorem materializedDeclarationWitness :
    ordinaryProducerCount? 39 ⟨witnessConfig.module, witnessEnvironment.vars⟩ materializedExpression = some 2 ∧
    ∃ state, execStmt 40 witnessConfig witnessEnvironment (.letS 0 materializedExpression 0) .initial =
      .ok (.normal .unit) state ∧ state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  constructor
  · unfold witnessConfig witnessEnvironment materializedExpression; cbv
  · refine ⟨stepState (execStmt 40 witnessConfig witnessEnvironment (.letS 0 materializedExpression 0) .initial), ?_, ?_⟩ <;>
      unfold witnessConfig witnessEnvironment materializedExpression stepState <;> cbv

#print axioms directDeclarationWitness
#print axioms materializedDeclarationWitness
#print axioms nonfixedDeclaration_direct
#print axioms nonfixedDeclaration_materialized
#print axioms nonfixedDeclaration_execution
end Goose.Proofs.ConstructionGhostNonfixedDeclaration
