import Goose.Proofs.ConstructionAcceptedNestedScalarGlobalsInvoke
import Goose.Proofs.ConstructionAcceptedNestedArgumentAnyUse
import Goose.Proofs.ConstructionAcceptedSingleGlobalRegisterInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem nestedArgumentList_singleGlobalRegisterCall_world {config : EvalConfig} (accepted : AcceptedModule config)
    (fuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (forms : NestedEffectfulArguments expressions)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (tail : callee.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (globalId globalOrigin : Nat) (assigned : Expr) (assignedForm : AcceptedBinaryExpression assigned)
    (statements : callee.body.stmts = [.assign (.global globalId) assigned globalOrigin])
    (globalScalar : ∀ descriptor, config.module.globals[globalId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, NestedArgumentSafe config frame expression)
    (position : SourcePosition accepted frame (.expression (.call contextId (expressions.map Arg.byVal) origin))) :
    match invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted frame after nextTypes
    | _ => False := by
  apply nestedArgumentList_scalarGlobalsRegisterCall_world accepted fuel frame state ambient types live regions pending contextId origin context callee expressions parameterTypes resultTy resultExpression contextAt calleeAt descriptors forms results resultScalar tail resultForm
  · rw [statements]
    exact .cons globalId assigned globalOrigin [] assignedForm .nil
  · intro id expression origin member descriptor declared
    simp [statements] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    exact globalScalar descriptor declared
  · exact world
  · exact source
  · exact initialized
  · exact bounded
  · exact blocks
  · exact position

#print axioms nestedArgumentList_singleGlobalRegisterCall_world
end Goose.Proofs.ConstructionAcceptedExecution
