import Goose.Proofs.ConstructionByteBatchTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmts_byteOwners_terminal_timeout (declarations : List ByteOwnerDeclaration) :
    ∀ (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before after : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      declarations.length ≤ checkFuel → frame.typingFuel = checkFuel + 1 →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement)) →
      (∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ declaration ∈ declarations,
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      execStmts runFuel config frame.interpretation.environment (declarations.map ByteOwnerDeclaration.statement) before = .stop .timeout after →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
        (nextRegions : List ReceivingRegion), next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config next.initialized after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted next after nextTypes := by
  intro runFuel checkFuel config accepted frame context before after ambient types live regions pending
  induction declarations generalizing runFuel checkFuel frame before types live regions with
  | nil =>
    intro enough nesting world source phase position owners unnamed executed
    cases runFuel with
    | zero =>
      simp only [List.map_nil, execStmts, timeout, EvalM.stop, ExecutionStep.stop.injEq, true_and] at executed
      subst after
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source⟩
    | succ fuel =>
      simp only [List.map_nil, execStmts, pure, reduceCtorEq] at executed
  | cons declaration declarations ih =>
    intro enough nesting world source phase position owners unnamed executed
    cases checkFuel with
    | zero => simp at enough
    | succ checkFuel =>
      have headOwner := owners declaration (by simp)
      have headUnnamed := unnamed declaration (by simp)
      have headPosition : SourcePosition accepted frame (.statements
          (declaration.statement :: declarations.map ByteOwnerDeclaration.statement)) := by
        simpa only [List.map_cons, ByteOwnerDeclaration.statement] using position
      have headExecuted : execStmts runFuel config frame.interpretation.environment
          (declaration.statement :: declarations.map ByteOwnerDeclaration.statement) before = .stop .timeout after := by
        simpa only [List.map_cons] using executed
      have split := execStmts_acceptedByteOwner_timeout_split runFuel (checkFuel + 1) config accepted frame context declaration.id
        declaration.bytes declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement) before after
        ambient types live regions pending world source phase headPosition (by omega) headOwner headUnnamed headExecuted
      rcases split with ⟨same, finalWorld, finalSource⟩ | ⟨destination, finalWorld, finalSource⟩ |
          ⟨middle, scopeInst, stored, published, tailFuel, tail, extended, middleWorld, middleSource, middlePosition⟩
      · exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), finalWorld, finalSource⟩
      · exact ⟨frame, types, live, freshReceivingRegion before destination :: regions, rfl,
          (fun _ _ found => found), finalWorld, finalSource⟩
      · let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst declaration.id
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
        obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource⟩ :=
          ih tailFuel checkFuel nextFrame middle nextTypes nextLive nextRegions
            (by simp only [List.length_cons] at enough; omega) rfl middleWorld middleSource
            (by simpa only [nextFrame, advanceLocalFrame] using phase) middlePosition remainingOwners remainingUnnamed tail
        refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, ?_, finalWorld, finalSource⟩
        intro oldRoot ty found
        exact finalExtended oldRoot ty (extended oldRoot ty found)

#print axioms execStmts_byteOwners_terminal_timeout

end Goose.Proofs.ConstructionAcceptedExecution
