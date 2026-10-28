import Goose.Proofs.ConstructionAcceptedParameterizedCallTailEffects
import Goose.Proofs.ConstructionAcceptedArithmeticCallEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedSingleByValueBoundRegisterBinaryCallTail (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (value : Value) (ty : Ty) (summary : Summary) (integer : Goose.Core.IntTy)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (declared : implementation.vars[0]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value)
    (known : implementation.summary = .known summary)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (tailTarget tailOrigin operandOrigin : Nat) (operation : Goose.Core.BinOp) (left right : Expr) (tailContext : Context) (tailCallee : Impl) (tailParameter : Param) (tailSummary : Summary)
    (body : implementation.body = ⟨implementation.body.scope, [], some (.call tailTarget [.byVal (.bin operation left right operandOrigin)] tailOrigin)⟩)
    (tailContextAt : config.module.contexts[tailTarget]? = some tailContext)
    (tailCalleeAt : config.module.impls[tailContext.impl]? = some tailCallee)
    (tailForm : RegisterArithmeticExpression config integer (.bin operation left right operandOrigin))
    (tailParameters : tailCallee.params = #[tailParameter]) (tailKnown : tailCallee.summary = .known tailSummary)
    (tailResults : tailCallee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (outerTy : Ty) (outerRoots : List RootRef) (outerTypingAfter : Nat) (outerRootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal argument] origin) outerTy outerRoots outerTypingAfter outerRootsAfter) :
    ∃ frame activation after roots typingAfter rootsAfter,
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := ownershipResultScopeState activation implementation.body.scope activated
      let root := Goose.Core.RootInst.local activation.act state.nextScope 0
      frame.source.impl = implementation ∧ frame.initialized = caller.initialized ∧ frame.interpretation.environment = activation ∧
      activation.act = state.nextAct ∧ activation.scopes = [] ∧ activation.channels = [.register ty] ∧
      activation.implementation = context.impl ∧ activation.vars = implementation.vars ∧
      bindAll activation.act state.nextScope [(parameter.var, value)] scopeState = .ok () after ∧
      RootTypesExtend types (registerRootType types root descriptor.ty) ∧
      AcceptedWorld config caller.initialized after (.callChannels activation [] :: ambient)
        (registerRootType types root descriptor.ty) (fun other => other = root ∨ live other) regions pending ∧
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope) after (registerRootType types root descriptor.ty) ∧
      CheckedValue (entryStatementsFrame config frame state.nextScope) (.call tailTarget [.byVal (.bin operation left right operandOrigin)] tailOrigin) ty roots typingAfter rootsAfter := by
  refine acceptedSingleByValueBoundCallTail_noParameterBody config accepted caller state ambient types live regions pending
    target origin context implementation parameter descriptor argument value ty summary contextAt implementationAt parameters declared
    scalar represented pointers known ?_ results tailTarget tailOrigin tailContext tailCallee [.byVal (.bin operation left right operandOrigin)]
    body tailContextAt tailCalleeAt tailResults scalarTy world source outerTy outerRoots outerTypingAfter outerRootsAfter checked
  intro bodySource before after result sourceModule sourceImpl clear rooted
  rw [body] at rooted
  exact
    arithmeticBinaryCallTail_noParameter config integer bodySource implementation.body.scope tailTarget tailOrigin operandOrigin operation left right tailContext tailCallee
      tailParameter tailSummary before after result tailForm sourceModule (by simpa [sourceModule] using tailContextAt)
      (by simpa [sourceModule] using tailCalleeAt) tailParameters tailKnown clear rooted

#print axioms acceptedSingleByValueBoundRegisterBinaryCallTail
end Goose.Proofs.ConstructionAcceptedExecution
