import Goose.Proofs.ConstructionGhostInvocation

namespace Goose.Proofs.ConstructionGhostMaterialization
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation

def materializationContinuation (source : ExecutionStep Value) : ExecutionStep (Option (Array Value)) :=
  match source with
  | .ok (.fixed values) state => .ok (some values) state
  | .ok _ state => .stop (.fault .shape) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem materializeProducer_none (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (before : ExecutionState)
    (unknown : ordinaryProducerCount? fuel declarations expression = none) :
    materializeProducer fuel declarations expression evaluate before = .ok none before := by
  simp [materializeProducer, unknown, pure]

theorem materializeProducer_source_ghost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (path : List Nat) (expression : Expr) (before : ExecutionState)
    (count : Nat)
    (known : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
    EvaluationTree config environment fuel (path ++ [0]) expression before
      (evalValue fuel config environment expression before) ∧
    materializeProducer fuel ⟨config.module, environment.vars⟩ expression
      (evalValue fuel config environment expression) before =
      materializationContinuation (evalValue fuel config environment expression before) := by
  refine ⟨evaluationTree_exists fuel config environment _ _ _, ?_⟩
  simp only [materializeProducer, known, bind, materializationContinuation]
  cases evalValue fuel config environment expression before with
  | ok value state => cases value <;> rfl
  | stop | escape | jump => rfl

theorem nonfixedDeclaration_materialized_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr)
    (origin : Goose.Core.OriginId) (before ready stopped : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl) (count : Nat)
    (reason : Goose.Core.Stop)
    (found : environment.vars[localVar]? = some descriptor)
    (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root ready)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = none)
    (known : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count)
    (source : evalValue fuel config environment expression ready = .stop reason stopped) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      .stop reason stopped := by
  simp only [execStmt, found, bind, rootResult, nonfixed, ↓reduceIte, implementationFound, notNamed,
    Option.isNone_none, materializeProducer, known, source, pure]

#print axioms nonfixedDeclaration_materialized_stop
private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessExpression : Expr := .blockE
  (.mk 0 [.print [.text "once"] 0]
    (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0
private def witnessRun : EvalM (Option (Array Value)) :=
  materializeProducer 40 ⟨witnessConfig.module, witnessEnvironment.vars⟩ witnessExpression
    (evalValue 40 witnessConfig witnessEnvironment witnessExpression)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem materializationWitness_sideEffect :
    ordinaryProducerCount? 40 ⟨witnessConfig.module, witnessEnvironment.vars⟩ witnessExpression = some 2 ∧
    ∃ state, witnessRun .initial = .ok (some #[.int .i64 7, .int .i64 8]) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  constructor
  · unfold witnessConfig witnessEnvironment witnessExpression; cbv
  · refine ⟨stepState (witnessRun .initial), ?_, ?_⟩ <;>
      unfold witnessRun witnessConfig witnessEnvironment witnessExpression stepState <;> cbv

private def declarationConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"entry", #[], #[], #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩],
    .mk 0 [] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def declarationEnvironment : RuntimeActivation := ⟨0, 4,
  #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩], [(0, 1)], []⟩
private def stoppedExpression : Expr := .blockE
  (.mk 1 [.print [.text "before"] 0, .abort "stop" 0]
    (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0

theorem nonfixedDeclaration_stopWitness :
    ordinaryProducerCount? 39 ⟨declarationConfig.module, declarationEnvironment.vars⟩ stoppedExpression = some 2 ∧
    ∃ state, execStmt 40 declarationConfig declarationEnvironment (.letS 0 stoppedExpression 0) .initial =
      .stop (.abort .userAbort 0) state ∧
      state.construction.stdout.data.toList = [98, 101, 102, 111, 114, 101, 10] := by
  constructor
  · unfold declarationConfig declarationEnvironment stoppedExpression; cbv
  · refine ⟨stepState (execStmt 40 declarationConfig declarationEnvironment
        (.letS 0 stoppedExpression 0) .initial), ?_, ?_⟩ <;>
      unfold stepState declarationConfig declarationEnvironment stoppedExpression <;> cbv

#print axioms nonfixedDeclaration_stopWitness
#print axioms materializationWitness_sideEffect
#print axioms materializeProducer_none
#print axioms materializeProducer_source_ghost
end Goose.Proofs.ConstructionGhostMaterialization
