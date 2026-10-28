import Goose.Proofs.ConstructionAcceptedByteBatch
import Goose.Proofs.ConstructionAcceptedByteAbnormalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmts_byteOwners_prefix (declarations : List ByteOwnerDeclaration) :
    ∀ (runFuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (rest : List Stmt)
      (before : ExecutionState) (result : ExecutionStep Flow) (ambient : OwnershipAmbient) (types : RootTypes)
      (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      declarations.length + 2 ≤ runFuel → declarations.length ≤ checkFuel → frame.typingFuel = checkFuel + 1 →
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements (declarations.map ByteOwnerDeclaration.statement ++ rest)) →
      (∀ declaration ∈ declarations, (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ declaration ∈ declarations,
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      execStmts runFuel config frame.interpretation.environment (declarations.map ByteOwnerDeclaration.statement ++ rest)
        before = result →
      ∃ (completed remaining : List ByteOwnerDeclaration) (remainingFuel : Nat) (next : ConstructionSourceFrame)
        (middle : ExecutionState) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
        (nextRegions : List ReceivingRegion),
        declarations = completed ++ remaining ∧ remainingFuel + completed.length = runFuel ∧
        next.interpretation = frame.interpretation ∧ next.initialized = frame.initialized ∧
        RootTypesExtend types nextTypes ∧ AcceptedWorld config next.initialized middle ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted next middle nextTypes ∧
        SourcePosition accepted next (.statements (remaining.map ByteOwnerDeclaration.statement ++ rest)) ∧
        ((remaining = [] ∧ execStmts remainingFuel config next.interpretation.environment rest middle = result) ∨
         (∃ declaration tail, remaining = declaration :: tail ∧
           execStmt (remainingFuel - 1) config next.interpretation.environment declaration.statement middle = result)) := by
  intro runFuel checkFuel config accepted frame context rest before result ambient types live regions pending
  induction declarations generalizing runFuel checkFuel frame before types live regions with
  | nil =>
    intro enoughRun enoughCheck nesting world source phase position owners unnamed executed
    exact ⟨[], [], runFuel, frame, before, types, live, regions, rfl, by simp, rfl, rfl,
      (fun root ty found => found), world, source, position, Or.inl ⟨rfl, executed⟩⟩
  | cons declaration declarations ih =>
    intro enoughRun enoughCheck nesting world source phase position owners unnamed executed
    cases runFuel with
    | zero => simp at enoughRun
    | succ runFuel =>
     cases runFuel with
     | zero => simp at enoughRun
     | succ runFuel =>
      cases runFuel with
      | zero => simp at enoughRun
      | succ runFuel =>
       cases checkFuel with
       | zero => simp at enoughCheck
       | succ checkFuel =>
        have headOwner := owners declaration (by simp)
        have headUnnamed := unnamed declaration (by simp)
        have headPosition : SourcePosition accepted frame (.statements
            (declaration.statement :: (declarations.map ByteOwnerDeclaration.statement ++ rest))) := by
          simpa only [List.map_cons, List.cons_append] using position
        have headExecuted : execStmts (runFuel + 3) config frame.interpretation.environment
            (declaration.statement :: (declarations.map ByteOwnerDeclaration.statement ++ rest)) before = result := by
          simpa only [List.map_cons, List.cons_append] using executed
        have split := execStmts_byteOwner_split runFuel (checkFuel + 1) config accepted frame context declaration.id declaration.bytes
          declaration.origin declaration.bytesOrigin (declarations.map ByteOwnerDeclaration.statement ++ rest)
          before result ambient types live regions pending world source phase headPosition (by omega) headOwner headUnnamed headExecuted
        rcases split with stopped | ⟨middle, scopeInst, stored, published, tail, extended, middleWorld, middleSource, middlePosition⟩
        · refine ⟨[], declaration :: declarations, runFuel + 3, frame, before, types, live, regions,
            rfl, by simp, rfl, rfl, (fun root ty found => found), world, source, position, Or.inr ?_⟩
          have fuelStep : runFuel + 3 - 1 = runFuel + 2 := by omega
          exact ⟨declaration, declarations, rfl, by simpa only [ByteOwnerDeclaration.statement, fuelStep] using stopped⟩
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
          obtain ⟨completed, remaining, remainingFuel, finalFrame, finalState, finalTypes, finalLive, finalRegions,
            decomposition, fuelEq, interpretationEq, initializedEq, typesExtended, finalWorld, finalSource, finalPosition, outcome⟩ :=
            ih (runFuel + 2) checkFuel nextFrame middle nextTypes nextLive nextRegions
              (by simp only [List.length_cons] at enoughRun; omega) (by simp only [List.length_cons] at enoughCheck; omega) rfl
              middleWorld middleSource (by simpa only [nextFrame, advanceLocalFrame] using phase) middlePosition remainingOwners remainingUnnamed tail
          refine ⟨declaration :: completed, remaining, remainingFuel, finalFrame, finalState, finalTypes, finalLive, finalRegions,
            ?_, ?_, interpretationEq, initializedEq, ?_, finalWorld, finalSource, finalPosition, outcome⟩
          · simp only [List.cons_append, decomposition]
          · simp only [List.length_cons] at *; omega
          · intro oldRoot ty found
            exact typesExtended oldRoot ty (extended oldRoot ty found)

#print axioms execStmts_byteOwners_prefix

end Goose.Proofs.ConstructionAcceptedExecution
