import Goose.Proofs.ConstructionGhostSourceFuel

namespace Goose.Proofs.ConstructionGhostDeclarationOnce
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel

theorem fallback_excludes_named {environment : RuntimeActivation} {implementation : Impl}
    {localVar : Goose.Core.VarId} {origin : Goose.Core.OriginId} {before fallbackReady selectedReady ready : ExecutionState}
    (fallback : DeclarationFallback environment implementation localVar origin before fallbackReady)
    (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId) (pending : PendingDestination)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = some (result, index))
    (channel : environment.channels[index]? = some (.construct incoming))
    (renewed : liftConstruction origin (renewReceivingDestination incoming) before = .ok selected selectedReady)
    (queried : getDestination selected selectedReady = .ok pending ready)
    (valueRequest : pending.capability.request = .value) : False := by
  cases fallback <;> simp_all

inductive DeclarationOccurrence (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    Option Goose.Core.DestinationId → ExecutionState → Prop
  | fixed (descriptor : LocalVar) (root : Goose.Core.RootInst) (ready : ExecutionState)
      (found : environment.vars[localVar]? = some descriptor) (fixed : descriptor.ty.nonfixed = false)
      (rootResult : rootOf environment localVar before = .ok root ready) :
      DeclarationOccurrence fuel config environment localVar expression origin before none ready
  | materialized (descriptor : LocalVar) (root : Goose.Core.RootInst) (rootReady : ExecutionState)
      (implementation : Impl) (ready : ExecutionState) (count : Nat)
      (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
      (rootResult : rootOf environment localVar before = .ok root rootReady)
      (implemented : config.module.impls[environment.implementation]? = some implementation)
      (fallback : DeclarationFallback environment implementation localVar origin rootReady ready)
      (counted : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
      DeclarationOccurrence fuel config environment localVar expression origin before none ready
  | direct (descriptor : LocalVar) (root : Goose.Core.RootInst) (rootReady : ExecutionState)
      (implementation : Impl) (ready : ExecutionState) (destination : Goose.Core.DestinationId) (buildReady : ExecutionState)
      (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
      (rootResult : rootOf environment localVar before = .ok root rootReady)
      (implemented : config.module.impls[environment.implementation]? = some implementation)
      (fallback : DeclarationFallback environment implementation localVar origin rootReady ready)
      (counted : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = none)
      (allocated : newDestination config.layout environment.act descriptor.ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ expression) ready = .ok destination buildReady) :
      DeclarationOccurrence fuel config environment localVar expression origin before (some destination) buildReady
  | named (descriptor : LocalVar) (root : Goose.Core.RootInst) (rootReady : ExecutionState) (implementation : Impl)
      (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId)
      (selectedReady : ExecutionState) (pending : PendingDestination) (ready : ExecutionState)
      (destination : Goose.Core.DestinationId) (renewedReady buildReady : ExecutionState)
      (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
      (rootResult : rootOf environment localVar before = .ok root rootReady)
      (implemented : config.module.impls[environment.implementation]? = some implementation)
      (named : (implementation.results.toList.zipIdx.find? fun (result, _) =>
        result.namedLocal == some localVar) = some (result, index))
      (channel : environment.channels[index]? = some (.construct incoming))
      (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
      (queried : getDestination selected selectedReady = .ok pending ready) (valueRequest : pending.capability.request = .value)
      (renewed : liftConstruction origin (renewReceivingDestination incoming) ready = .ok destination renewedReady)
      (prepared : liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady = .ok () buildReady) :
      DeclarationOccurrence fuel config environment localVar expression origin before (some destination) buildReady

theorem DeclarationOccurrence.unique {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {localVar : Goose.Core.VarId} {expression : Expr} {origin : Goose.Core.OriginId} {before firstReady secondReady : ExecutionState}
    {first second : Option Goose.Core.DestinationId}
    (left : DeclarationOccurrence fuel config environment localVar expression origin before first firstReady)
    (right : DeclarationOccurrence fuel config environment localVar expression origin before second secondReady) :
    first = second ∧ firstReady = secondReady := by
  cases left <;> cases right <;> simp_all
  all_goals first
    | exact DeclarationFallback.unique (by assumption) (by assumption)
    | exfalso; exact fallback_excludes_named (by assumption) _ _ _ _ _ (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption)
    | skip
  case direct.direct =>
    rename_i firstFallback _ _ _ _ secondFallback _ _
    have same := DeclarationFallback.unique firstFallback secondFallback
    cases same
    simp_all


theorem DeclarationOccurrence.history {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {localVar : Goose.Core.VarId} {expression : Expr} {origin : Goose.Core.OriginId} {before ready : ExecutionState}
    {destination : Option Goose.Core.DestinationId} (path : List Nat)
    (occurrence : DeclarationOccurrence fuel config environment localVar expression origin before destination ready)
    (value : FuelSupport config fuel (.value environment expression))
    (builder : ∀ destination, FuelSupport config fuel (.builder environment destination expression)) :
    match destination with
    | none => SourceHistory config fuel (path ++ [0]) (.value environment expression) ready
        (evalValue fuel config environment expression ready)
    | some destination => SourceHistory config fuel (path ++ [0]) (.builder environment destination expression) ready
        (buildExpr fuel config environment destination expression ready) := by
  cases occurrence with
  | fixed | materialized => exact fuelHistory_exists fuel config _ _ ready value
  | direct _ _ _ _ _ destination _ | named _ _ _ _ _ _ _ _ _ _ _ destination _ _ =>
      exact fuelHistory_exists fuel config _ _ ready (builder destination)

private def witnessDescriptor : LocalVar := ⟨"number", .int .i64, .immutable, 0, 0⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4, #[witnessDescriptor], [(0, 1)], []⟩
private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩

theorem fixedOccurrence_witness (fuel : Nat) :
    DeclarationOccurrence fuel witnessConfig witnessEnvironment 0 (.lit .i64 7) 0 .initial none .initial ∧
    execStmt (fuel + 1) witnessConfig witnessEnvironment (.letS 0 (.lit .i64 7) 0) .initial =
      (do let value ← evalValue fuel witnessConfig witnessEnvironment (.lit .i64 7)
          bindRoot (.local 4 1 0) value
          pure (Flow.normal .unit)) .initial := by
  constructor
  · apply DeclarationOccurrence.fixed witnessDescriptor (.local 4 1 0) .initial <;>
      simp [witnessEnvironment, witnessDescriptor, rootOf, Ty.nonfixed, bind, pure]
  · simp [execStmt, witnessEnvironment, witnessDescriptor, rootOf, Ty.nonfixed, bind, pure]

#print axioms fixedOccurrence_witness
#print axioms DeclarationOccurrence.history
#print axioms DeclarationOccurrence.unique
#print axioms fallback_excludes_named
end Goose.Proofs.ConstructionGhostDeclarationOnce
