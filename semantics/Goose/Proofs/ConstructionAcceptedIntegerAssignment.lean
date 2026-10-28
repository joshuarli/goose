import Goose.Proofs.ConstructionAcceptedScalarWriteRuntime
import Goose.Proofs.ConstructionAcceptedTerminalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem checkedIntegerLiteral {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (intTy : Goose.Core.IntTy) (number : Int)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size) :
    CheckedValue (ordinaryOperandFrame frame 1) (.lit intTy number) (.int intTy) []
      frame.typingCounter frame.rootCursor := by
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized frame.rootCursor.eff := by
    rw [initialized, ← source.compatible.globalCount]
    exact (globalEffectsAvailable_iff_bounded frame.interpretation frame.rootCursor.eff).2
      (by simpa only [source.compatible.globalCount] using bounded)
  refine ⟨?_, ?_, available⟩
  · simp [ordinaryOperandFrame, typeExpr, pure, StateT.pure, Except.pure]
  · simp [ordinaryOperandFrame, rpExpr, pure, StateT.pure, Except.pure]
    rfl

theorem execStmt_assignVisibleInteger_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (intTy : Goose.Core.IntTy) (number : Int) (origin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (localType : ∀ descriptor, frame.typing.variables[id]? = some descriptor → descriptor.ty = .int intTy) :
    ∃ nextLive,
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState
        (execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state)) ambient types nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState
        (execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state)) types ∧
      (match execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state with
      | .ok flow _ => flow = .normal .unit | .stop .. => True | _ => False) := by
  obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := source.locals id visible
  have typingDeclared : frame.typing.variables[id]? = some descriptor := by
    rw [← source.compatible.variables]; exact declared
  have same := localType descriptor typingDeclared
  have checked : CheckedValue (ordinaryOperandFrame frame 1) (.lit intTy number) descriptor.ty []
      frame.typingCounter frame.rootCursor := by
    simpa [same] using checkedIntegerLiteral source intTy number initialized bounded
  have result := execStmt_checkedScalarAssignLocal_registered fuel 1 config accepted frame state ambient types live regions pending
    id (.lit intTy number) origin descriptor (.numeric (.scalar (.scalar (.integer intTy number)))) world source initialized
    visible typingDeclared (Or.inl ⟨intTy, same⟩) [] frame.typingCounter frame.rootCursor checked
  cases outcome : execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state <;>
    simpa only [outcome] using result

theorem execStmt_assignVisibleInteger_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (intTy : Goose.Core.IntTy) (number : Int) (origin : Goose.Core.OriginId)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (visible : id ∈ frame.typing.visible)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (localType : ∀ descriptor, frame.typing.variables[id]? = some descriptor → descriptor.ty = .int intTy) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state) := by
  have result := execStmt_assignVisibleInteger_complete fuel config accepted frame state ambient types live regions pending
    id intTy number origin world source visible initialized bounded localType
  cases outcome : execStmt fuel config frame.interpretation.environment (.assign (.var id) (.lit intTy number) origin) state with
  | escape target carriers after | jump target kind after =>
    simp only [outcome] at result
    obtain ⟨_, _, _, impossible⟩ := result
    exact impossible.elim
  | stop reason after =>
    simp only [outcome, Goose.Proofs.Exit.stepState] at result
    obtain ⟨nextLive, nextWorld, nextSource, flow⟩ := result
    simp only [StatementWorldOutcome, outcome]
    exact ⟨ambient, types, nextLive, regions, nextWorld⟩
  | ok flow after =>
    simp only [outcome, Goose.Proofs.Exit.stepState] at result
    obtain ⟨nextLive, nextWorld, nextSource, normal⟩ := result
    simp only [StatementWorldOutcome, outcome]
    exact ⟨normal, frame, types, nextLive, regions, rfl, nextWorld, nextSource⟩

theorem execStmt_assignGlobalInteger_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (intTy : Goose.Core.IntTy) (number : Int) (origin : Goose.Core.OriginId) (descriptor : Global)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (declared : config.module.globals[id]? = some descriptor) (localType : descriptor.ty = .int intTy) :
    AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState
      (execStmt fuel config frame.interpretation.environment (.assign (.global id) (.lit intTy number) origin) state)) ambient types live regions pending ∧
    AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState
      (execStmt fuel config frame.interpretation.environment (.assign (.global id) (.lit intTy number) origin) state)) types ∧
    (match execStmt fuel config frame.interpretation.environment (.assign (.global id) (.lit intTy number) origin) state with
    | .ok flow _ => flow = .normal .unit | .stop .. => True | _ => False) := by
  have checked : CheckedValue (ordinaryOperandFrame frame 1) (.lit intTy number) descriptor.ty []
      frame.typingCounter frame.rootCursor := by
    simpa [localType] using checkedIntegerLiteral source intTy number initialized bounded
  have result := execStmt_checkedScalarAssignGlobal_complete fuel 1 config accepted frame state ambient types live regions pending
    id (.lit intTy number) origin descriptor (.numeric (.scalar (.scalar (.integer intTy number)))) world source initialized
    declared (Or.inl ⟨intTy, localType⟩) [] frame.typingCounter frame.rootCursor checked
  cases outcome : execStmt fuel config frame.interpretation.environment (.assign (.global id) (.lit intTy number) origin) state <;>
    simpa only [outcome] using result

theorem execStmt_assignGlobalInteger_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id : Nat) (intTy : Goose.Core.IntTy) (number : Int) (origin : Goose.Core.OriginId) (descriptor : Global)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (declared : config.module.globals[id]? = some descriptor) (localType : descriptor.ty = .int intTy) :
    StatementWorldOutcome config accepted frame.initialized ambient pending
      (execStmt fuel config frame.interpretation.environment (.assign (.global id) (.lit intTy number) origin) state) := by
  have result := execStmt_assignGlobalInteger_complete fuel config accepted frame state ambient types live regions pending
    id intTy number origin descriptor world source initialized bounded declared localType
  cases outcome : execStmt fuel config frame.interpretation.environment (.assign (.global id) (.lit intTy number) origin) state with
  | escape target carriers after | jump target kind after =>
    simp only [outcome] at result
    exact result.2.2.elim
  | stop reason after =>
    simp only [outcome, Goose.Proofs.Exit.stepState] at result
    simp only [StatementWorldOutcome, outcome]
    exact ⟨ambient, types, live, regions, result.1⟩
  | ok flow after =>
    simp only [outcome, Goose.Proofs.Exit.stepState] at result
    simp only [StatementWorldOutcome, outcome]
    exact ⟨result.2.2, frame, types, live, regions, rfl, result.1, result.2.1⟩

#print axioms checkedIntegerLiteral
#print axioms execStmt_assignGlobalInteger_complete
#print axioms execStmt_assignGlobalInteger_world
#print axioms execStmt_assignVisibleInteger_complete
#print axioms execStmt_assignVisibleInteger_world
end Goose.Proofs.ConstructionAcceptedExecution
