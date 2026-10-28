import Goose.Proofs.ConstructionAcceptedCallLocalInitializer
import Goose.Proofs.ConstructionAcceptedEarlierRecursiveValue

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execStmt_recursiveRegisterCall_initializer (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id statementOrigin target callOrigin : Nat) (context : Context) (callee : Impl) (ty : Ty) (scope scopeInst : Nat)
    (outerScopes : List (Nat × Nat)) (graph : RegisterCallGraphWithLocals config ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 1)
    (position : SourcePosition accepted frame (.statement (.letS id (.call target [] callOrigin) statementOrigin)))
    (available : ∀ rootsAfter, rpStmt frame.source (.letS id (.call target [] callOrigin) statementOrigin) frame.rootCursor =
      .ok ((), rootsAfter) → GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes) :
    match execStmt fuel config frame.interpretation.environment (.letS id (.call target [] callOrigin) statementOrigin) state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive,
        RootTypesExtend types nextTypes ∧ AcceptedWorld config frame.initialized after nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted frame after nextTypes
    | .ok flow after => flow = .normal .unit ∧ ∃ nextTypes nextLive,
        RootTypesExtend types nextTypes ∧
        AcceptedWorld config frame.initialized after ambient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted (advanceLocalFrame frame id) after nextTypes
    | .escape .. | .jump .. => False := by
  obtain ⟨descriptor, roots, typingAfter, rootsAfter, declared, typingOrder, rootOrder, sameTy, initialSource, checked⟩ :=
    checked_recursiveRegisterCall_initializer frame state types id statementOrigin target callOrigin checkFuel context callee ty
      source contextAt calleeAt results scalarTy localScalar nesting position available
  apply execStmt_recursiveRegisterCall_initializer_fromInvocation fuel checkFuel config accepted frame state ambient types live regions pending
    id statementOrigin target callOrigin context callee ty scope scopeInst outerScopes world source contextAt calleeAt results
    scalarTy localScalar nesting position available scopes
  intro evalFuel callFuel _ _
  exact invokeCall_recursive_register_earlier_frame callFuel config accepted ty scalarTy graph
    (letInitializerFrame frame id (checkFuel + 1)) state ambient types live regions pending target context callee callOrigin
    world initialSource contextAt calleeAt parameters results roots typingAfter rootsAfter checked

#print axioms execStmt_recursiveRegisterCall_initializer
end Goose.Proofs.ConstructionAcceptedExecution
