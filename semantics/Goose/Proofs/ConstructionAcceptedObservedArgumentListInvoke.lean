import Goose.Proofs.ConstructionAcceptedStatefulArgumentListInvoke
import Goose.Proofs.ConstructionAcceptedObservedParameterListInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem statefulArgumentList_call_worldWithCallerFrame {config : EvalConfig} (accepted : AcceptedModule config)
    (fuel checkFuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (first : Param) (remaining : List Param)
    (firstDescriptor : LocalVar) (parameterTypes : List Ty)
    (scope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (rest : List Expr)
    (resultTy : Ty) (resultExpression : Expr)
    (form : AcceptedBinaryExpression expression) (restForms : ScalarArgumentExpressions rest)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params.toList = first :: remaining)
    (firstAt : callee.params[0]? = some first) (firstMode : first.mode = .byValue)
    (firstDeclaredIndex : callee.vars[0]? = some firstDescriptor)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (tailDescriptors : ScalarParameterDescriptors callee 1 remaining parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ localId value statementOrigin, .letS localId value statementOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ descriptor, callee.vars[localId]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (ordinary : frame.typing.use = .ordinary) (request : frame.typing.request = .value)
    (requests : frame.typing.resultRequests = [])
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      (.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal) callOrigin)))
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    match invokeCall fuel config frame.interpretation.environment contextId
      (.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal)
      [.register resultTy] callOrigin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted frame after nextTypes
    | _ => False := by
  obtain ⟨specifications, expressions, specificationTypes, safe⟩ := checkedStatefulArgumentList_safety frame state types ambient live regions pending
    checkFuel contextId callOrigin context callee first remaining firstDescriptor parameterTypes scope id origin blockOrigin expression intTy literal rest
    form restForms source contextAt calleeAt parameters firstMode firstDeclared firstScalar tailDescriptors initialized ordinary request requests
    fresh absent nesting position globalScalar
  have descriptors : ScalarParameterDescriptors callee 0 callee.params.toList (firstDescriptor.ty :: parameterTypes) := by
    rw [parameters]
    exact .cons firstAt firstDescriptor firstDeclaredIndex firstMode firstScalar tailDescriptors
  have outcome := statefulScalarParameterList_call_worldWithCallerFrame specifications fuel config accepted frame state ambient types live regions pending
    contextId callOrigin context callee resultTy resultExpression contextAt calleeAt (firstDescriptor.ty :: parameterTypes)
    descriptors specificationTypes results resultScalar bodyForm tail resultForm owners scalarOwners world source initialized safe
  have mapped : specifications.map (fun specification => Arg.byVal specification.1) =
      .byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Arg.byVal) expressions
  rw [mapped] at outcome
  cases step : invokeCall fuel config frame.interpretation.environment contextId
      (.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal)
      [.register resultTy] callOrigin state <;> simpa [step] using outcome


#print axioms statefulArgumentList_call_worldWithCallerFrame
end Goose.Proofs.ConstructionAcceptedExecution
