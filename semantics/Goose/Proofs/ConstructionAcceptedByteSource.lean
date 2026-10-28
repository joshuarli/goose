import Goose.Proofs.ConstructionAcceptedBytePublication

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionStorage

theorem bytes_writeLoop_sourceState (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    OwnershipSourceState after.construction := by
  induction bytes generalizing before row count with
  | nil =>
    simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    exact valid
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement id ⟨#[byte]⟩ before.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      have extension := writeElement_ownership_source id ⟨#[byte]⟩ before.construction valid.structural.1.1.1
      have nextValid := constructionPrimitive_sourceState_of_sourceExtension (writeElement id ⟨#[byte]⟩)
        (.writeElement id ⟨#[byte]⟩) before.construction valid extension
      rw [written] at nextValid
      have row' := writeElement_success_destination id ⟨#[byte]⟩ before.construction final row count present opened written
      have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ before.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final id = .ok id := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ before.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      exact ih { before with construction := final }
        { row with progress := .open (count + 1), writeEnd := row.writeEnd + (⟨#[byte]⟩ : ByteArray).size } (count + 1)
        nextValid current' row'.1 rfl executed

theorem buildExpr_bytes_sourceState (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : buildExpr (fuel + 1) config environment id (.bytes ty bytes origin) before = .ok () after) :
    OwnershipSourceState after.construction := by
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  simp only [buildExpr, liftConstruction, renewal, bind] at executed
  have action := protectDestination_success origin id _ before after () executed
  cases loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before with
  | stop reason state => simp only [bind] at loop; rw [loop] at action; cases action
  | escape target carriers state => simp only [bind] at loop; rw [loop] at action; cases action
  | jump target kind state => simp only [bind] at loop; rw [loop] at action; cases action
  | ok value middle =>
    cases value
    have nextValid := bytes_writeLoop_sourceState bytes origin id before middle row count valid current present opened loop
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle row count valid.structural.1.1.1 current present opened loop
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, present', opened']
    have loop' := loop
    simp only [bind] at loop'
    rw [loop'] at action
    simp only [receivingAction, liftConstruction, renewal', bind] at action
    cases finished : finishDestination id middle.construction with
    | fault reason final => simp only [finished] at action; cases action
    | ok value final =>
      cases value
      simp only [finished, ExecutionStep.ok.injEq, true_and] at action
      subst after
      have extension := finishDestination_ownership_source middle.construction id lifecycle
      have preserved := constructionPrimitive_sourceState_of_sourceExtension (finishDestination id)
        (.finishDestination id) middle.construction nextValid extension
      simpa only [finished, ConstructionResult.finalState] using preserved

theorem publishCompleted_sourceState (origin : Goose.Core.OriginId) (id : Nat) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (executed : publishCarriers origin [.completed id] before = .ok () after) :
    OwnershipSourceState after.construction := by
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, List.filterMap_cons,
    List.filterMap_nil, _root_.id, liftConstruction] at executed
  cases result : publishOperation [id] before.construction with
  | fault reason final => simp only [result] at executed; cases executed
  | ok value final =>
    cases value
    simp only [result, ExecutionStep.ok.injEq, true_and] at executed
    subst after
    have extension := publishOperation_ownership_source [id] before.construction valid.structural.1.1.1
    have preserved := constructionPrimitive_sourceState_of_sourceExtension (publishOperation [id])
      (.publishOperation [id]) before.construction valid extension
    simpa only [result, ConstructionResult.finalState] using preserved

theorem allocated_published_byteOwner_sourceState (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before allocated built final : ExecutionState) (id : Nat) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (created : newDestination config.layout environment.act (.varr (.int .u8)) .value origin none (some bytes.length) before =
      .ok id allocated)
    (constructed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) allocated =
      .ok () built)
    (published : publishCarriers origin [.completed id] built = .ok () final) :
    OwnershipSourceState final.construction := by
  have allocatedWorld := newDestination_acceptedWorld config environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) initialized before allocated id ambient types live regions pending world created
  obtain ⟨ready⟩ := newDestination_initial_backing config.layout environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id (.int .u8) rfl created
  have current := newDestination_current_self config initialized environment.act (.varr (.int .u8)) .value origin
    (some bytes.length) before allocated id ambient types live regions pending world created
  have builtSource := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin
    allocated built ready.destination 0 allocatedWorld.ownership.source current ready.present ready.opened constructed
  exact publishCompleted_sourceState origin id built final builtSource published

#print axioms bytes_writeLoop_sourceState
#print axioms buildExpr_bytes_sourceState
#print axioms publishCompleted_sourceState
#print axioms allocated_published_byteOwner_sourceState

end Goose.Proofs.ConstructionAcceptedExecution
