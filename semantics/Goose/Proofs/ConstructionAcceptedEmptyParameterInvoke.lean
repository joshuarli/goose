import Goose.Proofs.ConstructionAcceptedEmptyParameterListBody
import Goose.Proofs.ConstructionAcceptedParameterBody
import Goose.Proofs.ConstructionAcceptedMixedLocalAsAssign
import Goose.Proofs.ConstructionAcceptedEmptyMixedAssignInvoke
import Goose.Proofs.ConstructionAcceptedFreshActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem emptyScalarParameterList_call_world (specifications : List (Expr × Ty)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameterTypes : List Ty) (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (specificationTypes : specifications.map Prod.snd = parameterTypes)
    (results : callee.results = #[])
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = none)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value statementOrigin, .letS id value statementOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ descriptor, callee.vars[id]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (initialized : caller.initialized = config.module.globals.size)
    (safe : ∀ specification ∈ specifications, ∀ runtimeFuel current,
      AcceptedWorld config caller.initialized current ambient types live regions pending →
      AcceptedFrame config accepted caller current types →
      FirstArgumentOutcome config accepted caller ambient types live regions pending specification.2 []
        (evalValue runtimeFuel config caller.interpretation.environment specification.1 current)) :
    match invokeCall fuel config caller.interpretation.environment contextId
      (specifications.map fun specification => .byVal specification.1) [] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  have localTargets : ∀ id expression statementOrigin, .assign (.var id) expression statementOrigin ∈ callee.body.stmts →
      ∀ descriptor, callee.vars[id]? = some descriptor → (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (bodyForm.noAssignment (.var id) expression statementOrigin member).elim
  have globalTargets : ∀ id expression statementOrigin, .assign (.global id) expression statementOrigin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool := by
    intro id expression statementOrigin member descriptor declared
    exact (bodyForm.noAssignment (.global id) expression statementOrigin member).elim
  have result := emptyMixedAssignParameterList_call_world specifications fuel config accepted caller state ambient types live regions pending
    contextId origin context callee contextAt calleeAt parameterTypes descriptors specificationTypes results bodyForm.asAssign tail
    owners scalarOwners localTargets globalTargets world source initialized safe
  cases step : invokeCall fuel config caller.interpretation.environment contextId
      (specifications.map fun specification => .byVal specification.1) [] origin state <;> simpa [step] using result

#print axioms emptyScalarParameterList_call_world
end Goose.Proofs.ConstructionAcceptedExecution
