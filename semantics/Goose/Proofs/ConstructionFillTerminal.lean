import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionFillTerminal
open Goose.Construct
open Goose.Core (DestinationId OriginId Stop)

theorem fixedElementFill_source_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (incoming destination : DestinationId)
    (element : Ty) (count : Nat) (operand : Expr) (origin : OriginId)
    (before ready stopped : ExecutionState) (reason : Stop)
    (fixed : element.nonfixed = false)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready)
    (source : evalValue fuel config environment operand ready = .stop reason stopped) :
    buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) before =
      .stop reason stopped := by
  simp only [buildExpr, expressionOrigin, bind, renewed, protectDestination, fixed, Bool.false_eq_true,
    ↓reduceIte, source]

theorem nonfixedElementFill_source_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (incoming destination sourceId : DestinationId)
    (element : Ty) (count : Nat) (operand : Expr) (origin : OriginId)
    (before ready sourceReady stopped : ExecutionState) (reason : Stop)
    (nonfixed : element.nonfixed = true)
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok destination ready)
    (allocated : newDestination config.layout environment.act element .value origin none none ready = .ok sourceId sourceReady)
    (source : buildExpr fuel config environment sourceId operand sourceReady = .stop reason stopped) :
    buildExpr (fuel + 1) config environment incoming (.fill (.arr element count) operand origin) before =
      .stop reason stopped := by
  simp only [buildExpr, expressionOrigin, bind, renewed, protectDestination, nonfixed, ↓reduceIte,
    allocated, source]

private def interruptedFill : EvalM Unit := do
  let config : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
  let destination ← newDestination config.layout 0 (.arr (.int .u8) 2) .value 0
  buildExpr 1 config ⟨0, 0, #[], [], []⟩ destination
    (.fill (.arr (.int .u8) 2) (.lit .u8 7) 0)

theorem interruptedFill_realizable :
    ∃ state, interruptedFill .initial = .stop .timeout state ∧
      state.construction.events = [.begin 0] := by
  refine ⟨(match interruptedFill .initial with | .ok _ s | .stop _ s | .escape _ _ s | .jump _ _ s => s), ?_, ?_⟩ <;>
    unfold interruptedFill <;> cbv

#print axioms interruptedFill_realizable
#print axioms fixedElementFill_source_stop
#print axioms nonfixedElementFill_source_stop
end Goose.Proofs.ConstructionFillTerminal
