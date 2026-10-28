import Goose.Proofs.ConstructionAcceptedCalleeBodySequence
import Goose.Proofs.ConstructionAcceptedCalleeBody
import Goose.Proofs.ConstructionAcceptedRegisterTail
import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_scalarLocal_prefix_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier scope : Nat) (statements : List Stmt) (expression : Expr) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, statements, some expression⟩)
    (frontierBound : frontier ≤ frame.interpretation.environment.act)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (form : ScalarLocalStatements statements) (tailForm : AcceptedBinaryExpression expression)
    (scalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (bodyType : ∃ declared, typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
      .ok ([ty], declared))
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, statements, some expression⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) :
    ∃ nextTypes nextLive,
      let outcome := execActivationBody fuel config frame.interpretation.environment [] ⟨scope, statements, some expression⟩ state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  obtain ⟨nextTypes, nextLive, nextAmbient, sameAmbient, extend, acts, scopeClocks, finalWorld, clear, observed, result⟩ :=
    execActivationBody_checkedSequence_earlier fuel config accepted frame context state ambient types live regions pending
      frontier scope statements expression ty world source phase parameters scopes cursor bodyFrame body frontierBound channels position
      tailForm bodyType available (fun candidate => candidate = ambient) rfl (by
        intro n _ child before seqWorld seqSource seqPhase seqPosition seqAvailable
        have bodyScope : frame.source.impl.body.scope = scope := by simp [body, Block.scope]
        have childInterpretation : child.interpretation = frame.interpretation.enterScope scope state.nextScope := by
          simp [child, entryStatementsFrame, bodyScope]
        have childSource : child.source = { frame.source with scopes := scope :: frame.source.scopes } := by
          simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
        have childScalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
            child.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
          intro id expression origin member descriptor declared
          apply scalar id expression origin member descriptor
          simpa [childSource] using declared
        have bound : frontier ≤ child.interpretation.environment.act := by
          simpa [childInterpretation, RootInterpretation.enterScope] using frontierBound
        obtain ⟨next, nextTypes, nextLive, initialized, extend, acts, scopeClocks, world, source, observed, result⟩ :=
          execStmts_scalarLocal_prefix_observed form frontier n config accepted child context
            before ambient types live regions pending
            bound seqWorld seqSource seqPhase seqPosition seqAvailable childScalar
        refine ⟨next, nextTypes, nextLive, ambient, initialized, rfl, extend, ?_, ?_, world, source, observed, ?_⟩
        · exact Nat.le_of_eq acts.symm
        · exact Nat.le_of_eq scopeClocks.symm
        · cases run : execStmts n config child.interpretation.environment statements before with
          | ok flow after => simp only [run] at result ⊢; exact ⟨trivial, result⟩
          | stop reason after => simp only [run] at result ⊢
          | escape address carriers after | jump target kind after => simp only [run] at result)
  subst nextAmbient
  refine ⟨nextTypes, nextLive, extend, acts, scopeClocks, finalWorld, clear, observed, ?_⟩
  cases execution : execActivationBody fuel config frame.interpretation.environment [] ⟨scope, statements, some expression⟩ state with
  | ok carriers after => simp only [execution] at result ⊢; exact result.2
  | stop reason after => simp only [execution] at result ⊢
  | escape address carriers after | jump target kind after => simpa only [execution] using result

theorem execActivationBody_scalarLocal_prefix (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (scope : Nat) (statements : List Stmt) (expression : Expr) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, statements, some expression⟩)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (form : ScalarLocalStatements statements) (tailForm : AcceptedBinaryExpression expression)
    (scalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (bodyType : ∃ declared, typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
      .ok ([ty], declared))
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, statements, some expression⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) :
    ∃ nextTypes nextLive,
      let outcome := execActivationBody fuel config frame.interpretation.environment [] ⟨scope, statements, some expression⟩ state
      RootTypesExtend types nextTypes ∧
      state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  obtain ⟨nextTypes, nextLive, extend, acts, scopes, finalWorld, clear, observed, result⟩ :=
    execActivationBody_scalarLocal_prefix_earlier fuel config accepted frame context state ambient types live regions pending 0 scope
      statements expression ty world source phase parameters scopes cursor bodyFrame body (Nat.zero_le _) channels position form tailForm
      scalar bodyType available
  exact ⟨nextTypes, nextLive, extend, acts, scopes, finalWorld, clear, result⟩

#print axioms execActivationBody_scalarLocal_prefix_earlier
#print axioms execActivationBody_scalarLocal_prefix
end Goose.Proofs.ConstructionAcceptedExecution
