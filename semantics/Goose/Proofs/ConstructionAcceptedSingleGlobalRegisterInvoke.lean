import Goose.Proofs.ConstructionAcceptedScalarGlobalsRegisterInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem singleGlobalScalarParameterList_call_worldWithCallerFrame (specifications : List (Expr × Ty)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameterTypes : List Ty) (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (specificationTypes : specifications.map Prod.snd = parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (tail : callee.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (globalId globalOrigin : Nat) (assigned : Expr) (assignedForm : AcceptedBinaryExpression assigned)
    (statements : callee.body.stmts = [.assign (.global globalId) assigned globalOrigin])
    (globalScalar : ∀ descriptor, config.module.globals[globalId]? = some descriptor →
      (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (initialized : caller.initialized = config.module.globals.size)
    (safe : ∀ specification ∈ specifications, ∀ runtimeFuel current,
      AcceptedWorld config caller.initialized current ambient types live regions pending →
      AcceptedFrame config accepted caller current types →
      FirstArgumentOutcome config accepted caller ambient types live regions pending specification.2 []
        (evalValue runtimeFuel config caller.interpretation.environment specification.1 current)) :
    match invokeCall fuel config caller.interpretation.environment contextId
      (specifications.map fun specification => .byVal specification.1) [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted caller after nextTypes
    | _ => False := by
  apply scalarGlobalsParameterList_call_worldWithCallerFrame specifications fuel config accepted caller state ambient types live regions pending
    contextId origin context callee resultTy resultExpression contextAt calleeAt parameterTypes descriptors specificationTypes results resultScalar tail resultForm
  · rw [statements]
    exact .cons globalId assigned globalOrigin [] assignedForm .nil
  · intro id expression origin member descriptor declared
    simp [statements] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    exact globalScalar descriptor declared
  · exact world
  · exact source
  · exact initialized
  · exact safe

#print axioms singleGlobalScalarParameterList_call_worldWithCallerFrame
end Goose.Proofs.ConstructionAcceptedExecution
