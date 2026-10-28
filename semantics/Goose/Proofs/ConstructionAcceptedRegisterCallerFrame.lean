import Goose.Proofs.ConstructionAcceptedCallerContents

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocalRegisterParameter_call_callerFrame {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller expression descriptor.ty roots typingAfter rootsAfter)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient)
    (carriers : List Carrier) (after : ExecutionState)
    (executed : invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state =
      .ok carriers after) :
    ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧ ValueRepresentation resultTy value ∧
      RootTypesExtend types nextTypes ∧
      AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
      AcceptedFrame config accepted caller after nextTypes := by
  have outcome := mixedLocalRegisterParameter_call_observedWorld shape fuel config accepted caller state ambient types live regions pending
    contextId origin context helper parameter descriptor resultTy resultExpression contextAt helperAt parameters results resultScalar declared
    scalar callerInitialized world callerSource roots typingAfter rootsAfter checked form tail resultShape owners scalarOwners depth outer
  simp only [executed] at outcome
  obtain ⟨value, nextTypes, nextLive, nextRegions, same, represented, extended, protectedTypes, finalWorld, counters, objects⟩ := outcome
  have frame := callerSource.afterFreshActivation counters.1 counters.2
    (fun root outside => (objects root outside).1) (fun root outside => (objects root outside).2) protectedTypes
  exact ⟨value, nextTypes, nextLive, nextRegions, same, represented, extended, finalWorld, frame⟩

#print axioms mixedLocalRegisterParameter_call_callerFrame
end Goose.Proofs.ConstructionAcceptedExecution
