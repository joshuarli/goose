import Goose.Proofs.ExitExecutionInvocationStatementsDefinitions

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem bind_step (action : EvalM α) (next : α → EvalM β) (state : ExecutionState) :
    (action >>= next) state = match action state with
      | .ok value after => next value after
      | .stop reason after => .stop reason after
      | .escape address carriers after => .escape address carriers after
      | .jump target kind after => .jump target kind after := rfl

private theorem bind_pure (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

theorem statementLetBuild_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (initial prepared : ExecutionState) (destination : Nat)
    (setup : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared)
    (address : ExitAddress) (carriers : List Carrier) (before : ExecutionState)
    (escaped : buildExpr fuel config environment destination expression prepared = .escape address carriers before) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) initial = .escape address carriers before := by
  cases setup with
  | actual selected materialized allocated prepared descriptor root named destination namedPrefix materialization allocation preparation =>
      cases namedPrefix with
      | absent selected descriptor root implementation lookup nonfixed rootSelected implementationLookup candidate =>
          simp only [Option.isNone, ↓reduceIte] at materialization
          simp only [execStmt, lookup]
          rw [bind_step, rootSelected]
          dsimp only []
          simp only [nonfixed, implementationLookup, candidate]
          simp only [ite_true, bind_pure, Option.isSome, Option.isNone, Bool.false_eq_true, ite_false]
          rw [bind_step, materialization]
          dsimp only []
          simp only [Option.map_none]
          change newDestination config.layout environment.act descriptor.ty .value origin none
            (producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated at allocation
          have nativeAllocation : newDestination config.layout environment.act descriptor.ty .value origin none
              (none <|> producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated := allocation
          rw [bind_step, nativeAllocation]
          dsimp only []
          have same : allocated = prepared := by simpa only [Option.isSome, Bool.false_eq_true, ite_false, pure, ExecutionStep.ok.injEq, true_and] using preparation
          subst allocated
          rw [bind_step, escaped]
      | receiving rooted renewed selected descriptor root implementation result index incoming renewedDestination receiving lookup nonfixed rootSelected implementationLookup candidate channel renewal selection request =>
          simp only [execStmt, lookup]
          rw [bind_step, rootSelected]
          dsimp only []
          simp only [nonfixed, implementationLookup, candidate, channel, ite_true]
          rw [bind_step, renewal]
          dsimp only []
          rw [bind_step, selection]
          dsimp only []
          simp only [request, ite_true, bind_pure, Option.isSome, Option.isNone, Bool.false_eq_true, ite_false]
          have sameMaterialized : selected = materialized := by
            simpa only [Option.isNone, Bool.false_eq_true, ite_false, pure, ExecutionStep.ok.injEq, true_and] using materialization
          subst materialized
          simp only [channel] at allocation ⊢
          rw [bind_step, allocation]
          dsimp only []
          simp only [Option.isSome, ite_true] at preparation
          rw [bind_step, preparation]
          dsimp only []
          rw [bind_step, escaped]
      | other rooted renewed selected descriptor root implementation result index incoming renewedDestination receiving lookup nonfixed rootSelected implementationLookup candidate channel renewal selection request =>
          simp only [Option.isNone, ↓reduceIte] at materialization
          simp only [execStmt, lookup]
          rw [bind_step, rootSelected]
          dsimp only []
          simp only [nonfixed, implementationLookup, candidate, channel, ite_true]
          rw [bind_step, renewal]
          dsimp only []
          rw [bind_step, selection]
          dsimp only []
          simp only [request, ite_true, bind_pure, Option.isSome, Option.isNone, Bool.false_eq_true, ite_false]
          rw [bind_step, materialization]
          dsimp only []
          simp only [Option.map_none]
          change newDestination config.layout environment.act descriptor.ty .value origin none
            (producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated at allocation
          have nativeAllocation : newDestination config.layout environment.act descriptor.ty .value origin none
              (none <|> producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated := allocation
          rw [bind_step, nativeAllocation]
          dsimp only []
          have same : allocated = prepared := by simpa only [Option.isSome, Bool.false_eq_true, ite_false, pure, ExecutionStep.ok.injEq, true_and] using preparation
          subst allocated
          rw [bind_step, escaped]

end Goose.Proofs.ExitExecution
