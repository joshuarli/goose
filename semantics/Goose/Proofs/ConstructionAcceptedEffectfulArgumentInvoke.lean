import Goose.Proofs.ConstructionAcceptedEffectfulArgumentList
import Goose.Proofs.ConstructionAcceptedObservedParameterListInvoke

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem effectfulArgumentList_call_worldWithCallerFrame {config : EvalConfig} (accepted : AcceptedModule config)
    (fuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (forms : EffectfulScalarArguments expressions)
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
    (ordinary : frame.typing.use = .ordinary) (request : frame.typing.request = .value) (requests : frame.typing.resultRequests = [])
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (blocks : ∀ expression ∈ expressions, ArgumentBlockSafe config frame expression)
    (position : SourcePosition accepted frame (.expression (.call contextId (expressions.map Arg.byVal) origin))) :
    match invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted frame after nextTypes
    | _ => False := by
  cases nesting : frame.typingFuel with
  | zero =>
    obtain ⟨resultTypes, after, roots, rootAfter, typed, rooted⟩ := position.checked accepted frame _
    rw [nesting] at typed
    change Except.error _ = Except.ok _ at typed
    cases typed
  | succ checkFuel =>
    let argsFrame := { frame with typingFuel := checkFuel }
    have argsPosition := position.call_arguments accepted frame contextId origin checkFuel context callee (expressions.map Arg.byVal)
      source.compatible contextAt calleeAt nesting
    have argsSource := source.withTypingFuel checkFuel
    have argsBlocks : ∀ expression ∈ expressions, ArgumentBlockSafe config argsFrame expression := by
      intro expression member
      simpa [ArgumentBlockSafe, argsFrame] using blocks expression member
    obtain ⟨specifications, sameExpressions, sameTypes, safe⟩ := checkedEffectfulArgumentList_safety config accepted context.impl callee calleeAt
      descriptors expressions forms argsFrame state types ambient live regions pending argsSource initialized ordinary request requests bounded argsBlocks argsPosition
    have callerSafe : ∀ specification ∈ specifications, ∀ runtimeFuel current,
        AcceptedWorld config frame.initialized current ambient types live regions pending →
        AcceptedFrame config accepted frame current types →
        FirstArgumentOutcome config accepted frame ambient types live regions pending specification.2 []
          (evalValue runtimeFuel config frame.interpretation.environment specification.1 current) := by
      intro specification member runtimeFuel current currentWorld currentSource
      have currentArgs := currentSource.withTypingFuel checkFuel
      have actual := safe specification member runtimeFuel current currentWorld currentArgs
      exact FirstArgumentOutcome.retargetCursor checkFuel frame.rootCursor rfl specification.2 _ actual
    have outcome := statefulScalarParameterList_call_worldWithCallerFrame specifications fuel config accepted frame state ambient types live regions pending
      contextId origin context callee resultTy resultExpression contextAt calleeAt parameterTypes descriptors sameTypes results resultScalar
      bodyForm tail resultForm owners scalarOwners world source initialized callerSafe
    have mapped : specifications.map (fun specification => Arg.byVal specification.1) = expressions.map Arg.byVal := by
      simpa [List.map_map, Function.comp_def] using congrArg (List.map Arg.byVal) sameExpressions
    rw [mapped] at outcome
    cases step : invokeCall fuel config frame.interpretation.environment contextId (expressions.map Arg.byVal) [.register resultTy] origin state <;>
      simpa [step] using outcome

#print axioms effectfulArgumentList_call_worldWithCallerFrame
end Goose.Proofs.ConstructionAcceptedExecution
