import Goose.Lower.DemandWhileIterationStop
import Goose.Lower.DemandBranchBlockStopped
import Goose.Lower.DemandStoppedExpressionFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_while_body_stopped_outcome {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {count : Nat} {state current middle : St}
    (iterations : WhileIterations cfg env condition body count state current)
    {conditionFuel : Nat} (conditionDone : evalExpr conditionFuel cfg env condition current = .ok (.bool true) middle)
    (branch : BlockSource cfg env [] body middle) {cx : FnCtx} {results : List Ty}
    {before : LS} {loop : Option LoopCtx} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {taken : Nat} {reached : DemandRuntimePoint} {stop : Stop} {after : St}
    (progress : StoppedLoopBranchBlockPrefix branch map required cx results before loop initial start taken reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    (∃ total, execStmt total cfg env (.while condition body origin) state = .stop stop after) ∨
    ∃ (fuel consumed remaining : Nat) (boundary : DemandRuntimePoint) (flow : Flow),
      consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed ⟨start, initial, middle⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧ execBlock fuel cfg env [] body middle = .ok flow boundary.state ∧
      GeneratedBranchBlockEnd branch map required cx results before loop initial flow boundary := by
  cases progress with
  | aborted fuel done => exact Or.inl (while_iterations_body_stop iterations conditionDone done nonTimeout)
  | complete count executed residual evaluated post => exact Or.inr ⟨_, _, _, _, _, count, executed, residual, evaluated, post⟩

theorem accepted_generated_while_condition_stopped_outcome {cfg : Cfg} {env : Env} {condition : Expr} {body : Core.Block}
    {origin : OriginId} {count : Nat} {state current : St}
    (iterations : WhileIterations cfg env condition body count state current)
    (child : ExprSource cfg env condition current) {cx : FnCtx} {results : List Ty}
    {before : LS} {initial : GIR.Frame} {start : Pt} {map : RetainedSsaMap}
    {taken : Nat} {reached : DemandRuntimePoint} {stop : Stop} {after : St}
    (progress : StoppedExpressionPrefix child map cx results before initial start taken reached stop after)
    (nonTimeout : stop ≠ .timeout) :
    (∃ total, execStmt total cfg env (.while condition body origin) state = .stop stop after) ∨
    ∃ (fuel consumed remaining : Nat) (boundary : DemandRuntimePoint) (value : Val),
      consumed + remaining = taken ∧ DemandRuntimePrefix cx consumed ⟨start, initial, current⟩ boundary ∧
      DemandRuntimePrefix cx remaining boundary reached ∧ evalExpr fuel cfg env condition current = .ok value boundary.state ∧
      GeneratedExpressionPrefixEnd child map cx before initial
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).2
        (lowerExpr condition (lowerEnv cfg.mod env.vars results) before).1 value boundary := by
  cases progress with
  | aborted fuel done => exact Or.inl (while_iterations_condition_stop iterations done nonTimeout)
  | complete count executed residual evaluated post => exact Or.inr ⟨_, _, _, _, _, count, executed, residual, evaluated, post⟩

#print axioms accepted_generated_while_body_stopped_outcome
#print axioms accepted_generated_while_condition_stopped_outcome
end Goose.Lower
