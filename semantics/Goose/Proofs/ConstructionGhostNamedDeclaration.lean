import Goose.Proofs.ConstructionGhostNonfixedDeclaration

namespace Goose.Proofs.ConstructionGhostNamedDeclaration
open Goose.Construct

def namedDeclarationAfterBuild (descriptor : LocalVar) (root : Goose.Core.RootInst)
    (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId)
    (built : ExecutionStep Unit) : ExecutionStep Flow :=
  match built with
  | .ok () state => (do
      let destination ← completedReceivingDestination destination
      let stored ← storedDestination destination
      let object ← liftConstruction origin reserveStorage
      bindRoot root (.stored { stored with ty := descriptor.ty, object := some object })
      pure (Flow.normal .unit)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem namedDeclaration_execution (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr)
    (origin : Goose.Core.OriginId) (before rootReady selectedReady destinationReady renewedReady buildReady : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected destination : Goose.Core.DestinationId)
    (pending : PendingDestination)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (pendingResult : getDestination selected selectedReady = .ok pending destinationReady)
    (valueRequest : pending.capability.request = .value)
    (renewedResult : liftConstruction origin (renewReceivingDestination incoming) destinationReady = .ok destination renewedReady)
    (prepared : liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady = .ok () buildReady) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      namedDeclarationAfterBuild descriptor root origin destination
        (buildExpr fuel config environment destination expression buildReady) := by
  simp only [execStmt, found, bind, rootResult, nonfixed, ↓reduceIte, implementationFound, named, channelFound,
    selectedResult, pendingResult, valueRequest, BEq.rfl, ↓reduceIte, pure, Option.isNone_some, Bool.false_eq_true,
    Option.isSome_some, renewedResult, prepared, namedDeclarationAfterBuild]
  cases buildExpr fuel config environment destination expression buildReady <;> rfl

private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"entry", #[], #[⟨.varr (.int .i64), .value, some 0⟩],
    #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩], .mk 0 [] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def witnessAction : EvalM Flow := do
  let destination ← newDestination witnessConfig.layout 4 (.varr (.int .i64)) .value 0
  let environment : RuntimeActivation := ⟨0, 4,
    #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩], [(0, 1)], [.construct destination]⟩
  execStmt 50 witnessConfig environment (.letS 0 (.arrLit (.varr (.int .i64))
    [.blockE (.mk 1 [.print [.text "once"] 0] (some (.lit .i64 7))) 0, .lit .i64 8] 0) 0)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem namedDeclarationWitness :
    ∃ state, witnessAction .initial = .ok (.normal .unit) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨stepState (witnessAction .initial), ?_, ?_⟩ <;>
    unfold witnessAction witnessConfig stepState <;> cbv

#print axioms namedDeclarationWitness
#print axioms namedDeclaration_execution
end Goose.Proofs.ConstructionGhostNamedDeclaration
