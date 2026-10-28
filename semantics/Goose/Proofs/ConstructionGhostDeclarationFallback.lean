import Goose.Proofs.ConstructionGhostNonfixedDeclaration

namespace Goose.Proofs.ConstructionGhostDeclarationFallback
open Goose.Construct Goose.Proofs.ConstructionGhostNonfixedDeclaration

theorem nonfixedDeclaration_nonvalueFallback (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady selectedReady destinationReady : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId) (pending : PendingDestination)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) =>
      result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (pendingResult : getDestination selected selectedReady = .ok pending destinationReady)
    (nonvalueRequest : pending.capability.request ≠ .value) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationAfterMaterialization fuel config environment descriptor root expression origin
        (materializeProducer fuel ⟨config.module, environment.vars⟩ expression
          (evalValue fuel config environment expression) destinationReady) := by
  simp only [execStmt, found, bind, rootResult, nonfixed, ↓reduceIte, implementationFound, named, channelFound,
    selectedResult, pendingResult]
  simp only [nonvalueRequest, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, pure, bind,
    Option.isNone_none, Option.isSome_none, declarationAfterMaterialization, declarationContinuation]
  cases materializeProducer fuel ⟨config.module, environment.vars⟩ expression
      (evalValue fuel config environment expression) destinationReady with
  | ok value state => cases value <;> rfl
  | stop | escape | jump => rfl

theorem nonfixedDeclaration_nonvalueFallback_direct (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady selectedReady destinationReady : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId) (pending : PendingDestination)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (pendingResult : getDestination selected selectedReady = .ok pending destinationReady)
    (nonvalueRequest : pending.capability.request ≠ .value)
    (direct : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = none) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationContinuation fuel config environment descriptor root expression origin none destinationReady := by
  rw [nonfixedDeclaration_nonvalueFallback fuel config environment localVar expression origin before rootReady selectedReady destinationReady
    descriptor root implementation result index incoming selected pending found nonfixed rootResult implementationFound named channelFound
    selectedResult pendingResult nonvalueRequest]
  rw [Goose.Proofs.ConstructionGhostMaterialization.materializeProducer_none fuel ⟨config.module, environment.vars⟩ expression
    (evalValue fuel config environment expression) destinationReady direct]
  rfl

theorem nonfixedDeclaration_nonvalueFallback_materialized (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady selectedReady destinationReady : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId) (pending : PendingDestination) (count : Nat)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (pendingResult : getDestination selected selectedReady = .ok pending destinationReady)
    (nonvalueRequest : pending.capability.request ≠ .value)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ expression = some count) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationAfterMaterialization fuel config environment descriptor root expression origin
        (Goose.Proofs.ConstructionGhostMaterialization.materializationContinuation
          (evalValue fuel config environment expression destinationReady)) := by
  rw [nonfixedDeclaration_nonvalueFallback fuel config environment localVar expression origin before rootReady selectedReady destinationReady
    descriptor root implementation result index incoming selected pending found nonfixed rootResult implementationFound named channelFound
    selectedResult pendingResult nonvalueRequest]
  obtain ⟨tree, execution⟩ := Goose.Proofs.ConstructionGhostMaterialization.materializeProducer_source_ghost
    fuel config environment [] expression destinationReady count materialized
  rw [execution]

#print axioms nonfixedDeclaration_nonvalueFallback_direct
#print axioms nonfixedDeclaration_nonvalueFallback_materialized
inductive DeclarationTerminal where
  | stopped (reason : Goose.Core.Stop) (state : ExecutionState)
  | escaped (address : ExitAddress) (carriers : List Carrier) (state : ExecutionState)
  | jumped (target : Nat) (kind : JumpKind) (state : ExecutionState)

def DeclarationTerminal.step : DeclarationTerminal → ExecutionStep α
  | .stopped reason state => .stop reason state
  | .escaped address carriers state => .escape address carriers state
  | .jumped target kind state => .jump target kind state

theorem nonfixedDeclaration_renewalTerminal (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming : Goose.Core.DestinationId) (terminal : DeclarationTerminal)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (renewal : liftConstruction origin (renewReceivingDestination incoming) rootReady = terminal.step) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step := by
  cases terminal <;> simp only [DeclarationTerminal.step] at renewal ⊢ <;>
    simp only [execStmt, found, bind, rootResult, nonfixed, ↓reduceIte, implementationFound, named, channelFound, renewal]

theorem nonfixedDeclaration_lookupTerminal (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady selectedReady : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected : Goose.Core.DestinationId) (terminal : DeclarationTerminal)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (renewal : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (lookup : getDestination selected selectedReady = terminal.step) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before = terminal.step := by
  cases terminal <;> simp only [DeclarationTerminal.step] at lookup ⊢ <;>
    simp only [execStmt, found, bind, rootResult, nonfixed, ↓reduceIte, implementationFound, named, channelFound, renewal, lookup]

theorem nonfixedDeclaration_badNamedChannel (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (notConstruct : ∀ incoming, environment.channels[index]? ≠ some (.construct incoming)) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before = .stop (.fault .flow) rootReady := by
  cases channel : environment.channels[index]? with
  | none => simp [execStmt, found, bind, rootResult, nonfixed, implementationFound, named, channel, fault, EvalM.stop]
  | some value =>
      cases value with
      | construct incoming => exact False.elim (notConstruct incoming channel)
      | register | completion => simp [execStmt, found, bind, rootResult, nonfixed, implementationFound, named, channel, fault, EvalM.stop]

#print axioms nonfixedDeclaration_renewalTerminal
#print axioms nonfixedDeclaration_lookupTerminal
#print axioms nonfixedDeclaration_badNamedChannel
#print axioms nonfixedDeclaration_nonvalueFallback
end Goose.Proofs.ConstructionGhostDeclarationFallback
