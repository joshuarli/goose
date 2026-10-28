import Goose.Proofs.ConstructionFreshByteGlobalSequenceEvents
import Goose.Proofs.ConstructionByteStatementOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_acceptedByteOwner_fresh_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (bytes : List UInt8) (origin bytesOrigin : Goose.Core.OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (phase : frame.phase = .implementation context)
    (byteOwner : (frame.typing.variables[id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some id)) = none) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState (execStmt fuel config frame.interpretation.environment
        (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before)).construction.events =
          before.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ByteOwnerTraceEvent before.construction.destinations.size event := by
  cases declared : frame.typing.variables[id]? with
  | none => simp [declared] at byteOwner
  | some descriptor =>
    have descriptorType : descriptor.ty = .varr (.int .u8) := by simpa [declared] using byteOwner
    have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
      rw [source.compatible.variables]
      exact declared
    have originFact := source.compatible.origin
    unfold SourceOrigin at originFact
    rw [phase] at originFact
    obtain ⟨original, calls, contextFound, implementationFound, implementationId, restOrigin⟩ := originFact
    have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
      rw [implementationId]
      exact implementationFound
    exact execStmt_byteOwner_fresh_events fuel config frame.initialized frame.interpretation.environment id descriptor frame.source.impl
      before bytes origin bytesOrigin ambient types live regions pending world runtimeDeclared descriptorType implementation unnamed

theorem execStmts_byteOwners_fresh_events (declarations : List ByteOwnerDeclaration) :
    ∀ (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      declarations.length ≤ checkFuel → frame.typingFuel = checkFuel + 1 →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement)) →
      (∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ declaration ∈ declarations,
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      ∃ suffix,
        (Goose.Proofs.Exit.stepState (execStmts runFuel config frame.interpretation.environment
          (declarations.map ByteOwnerDeclaration.statement) before)).construction.events =
            before.construction.events ++ suffix ∧ ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
  intro runFuel checkFuel config accepted frame context before ambient types live regions pending
  induction declarations generalizing runFuel checkFuel frame before types live regions with
  | nil =>
    intro enough nesting world source phase position owners unnamed
    refine ⟨[], ?_, by simp⟩
    cases runFuel <;> simp [List.map_nil, execStmts, timeout, EvalM.stop, pure, Goose.Proofs.Exit.stepState]
  | cons declaration declarations ih =>
    intro enough nesting world source phase position owners unnamed
    cases runFuel with
    | zero =>
      refine ⟨[], ?_, by simp⟩
      simp [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    | succ runFuel =>
      cases checkFuel with
      | zero => simp at enough
      | succ checkFuel =>
        have owner := owners declaration (by simp)
        have unnamedHead := unnamed declaration (by simp)
        have positionHead : SourcePosition accepted frame (.statements
            (declaration.statement :: declarations.map ByteOwnerDeclaration.statement)) := by
          simpa only [List.map_cons] using position
        obtain ⟨first, firstTrace, firstValid⟩ := execStmt_acceptedByteOwner_fresh_events runFuel config accepted frame context
          declaration.id declaration.bytes declaration.origin declaration.bytesOrigin before ambient types live regions pending
          world source phase owner unnamedHead
        have outcome := execStmt_acceptedByteOwner_outcome runFuel (checkFuel + 1) config accepted frame context
          declaration.id declaration.bytes declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement)
          before ambient types live regions pending world source phase positionHead (by omega) owner unnamedHead
        simp only [List.map_cons, execStmts]
        cases head : execStmt runFuel config frame.interpretation.environment declaration.statement before with
        | stop reason after =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head', Goose.Proofs.Exit.stepState] at firstTrace
          refine ⟨first, ?_, ?_⟩
          · simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
          · intro event member
            exact ⟨before.construction.destinations.size, firstValid event member⟩
        | escape target carriers after =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head', Goose.Proofs.Exit.stepState] at firstTrace
          refine ⟨first, ?_, ?_⟩
          · simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
          · intro event member
            exact ⟨before.construction.destinations.size, firstValid event member⟩
        | jump target kind after =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head', Goose.Proofs.Exit.stepState] at firstTrace
          refine ⟨first, ?_, ?_⟩
          · simpa only [bind, head, Goose.Proofs.Exit.stepState] using firstTrace
          · intro event member
            exact ⟨before.construction.destinations.size, firstValid event member⟩
        | ok flow middle =>
          have head' := head
          simp only [ByteOwnerDeclaration.statement] at head'
          simp only [head'] at outcome
          obtain ⟨flowEq, scopeInst, stored, published, extended, middleWorld, middleSource, middlePosition⟩ := outcome
          subst flow
          let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst declaration.id
          let nextTypes := registerRootType types root (.varr (.int .u8))
          let nextFrame := advanceLocalFrame { frame with typingFuel := checkFuel + 1 } declaration.id
          let nextLive := fun other => other = root ∨ live other
          let nextRegions := regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))
          have remainingOwners : ∀ item ∈ declarations, (nextFrame.typing.variables[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
            intro item member
            exact owners item (List.mem_cons_of_mem declaration member)
          have remainingUnnamed : ∀ item ∈ declarations,
              (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
            intro item member
            exact unnamed item (List.mem_cons_of_mem declaration member)
          obtain ⟨tail, tailTrace, tailValid⟩ := ih runFuel checkFuel nextFrame middle nextTypes nextLive nextRegions (by simp only [List.length_cons] at enough; omega) rfl middleWorld middleSource
            (by simpa only [nextFrame, advanceLocalFrame] using phase) middlePosition remainingOwners remainingUnnamed
          simp only [head', Goose.Proofs.Exit.stepState] at firstTrace
          refine ⟨first ++ tail, ?_, ?_⟩
          · simp only [bind, head, pure]
            change (Goose.Proofs.Exit.stepState (execStmts runFuel config nextFrame.interpretation.environment
              (declarations.map ByteOwnerDeclaration.statement) middle)).construction.events = _
            rw [tailTrace, firstTrace]
            simp [List.append_assoc]
          · intro event member
            simp only [List.mem_append] at member
            rcases member with member | member
            · exact ⟨before.construction.destinations.size, firstValid event member⟩
            · exact tailValid event member

#print axioms execStmts_byteOwners_fresh_events
#print axioms execStmt_acceptedByteOwner_fresh_events

end Goose.Proofs.ConstructionAcceptedExecution
