import Goose.Proofs.ConstructionAcceptedStatefulArgumentListChecks
import Goose.Proofs.ConstructionAcceptedGlobalAssignResultBlock

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem checkedStatefulArgumentList_safety {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (ambient : OwnershipAmbient)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (checkFuel contextId callOrigin : Nat) (context : Context) (callee : Impl) (first : Param) (remaining : List Param)
    (firstDescriptor : LocalVar) (parameterTypes : List Ty)
    (scope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (rest : List Expr)
    (form : AcceptedBinaryExpression expression) (restForms : ScalarArgumentExpressions rest)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params.toList = first :: remaining)
    (firstMode : first.mode = .byValue) (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (tailDescriptors : ScalarParameterDescriptors callee 1 remaining parameterTypes)
    (initialized : frame.initialized = config.module.globals.size)
    (ordinary : frame.typing.use = .ordinary) (request : frame.typing.request = .value)
    (requests : frame.typing.resultRequests = [])
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      (.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal) callOrigin)))
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    ∃ specifications : List (Expr × Ty),
      specifications.map Prod.fst = (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest ∧
      specifications.map Prod.snd = firstDescriptor.ty :: parameterTypes ∧
      ∀ specification ∈ specifications, ∀ runtimeFuel current,
        AcceptedWorld config frame.initialized current ambient types live regions pending →
        AcceptedFrame config accepted frame current types →
        FirstArgumentOutcome config accepted frame ambient types live regions pending specification.2 []
          (evalValue runtimeFuel config frame.interpretation.environment specification.1 current) := by
  obtain ⟨middle, leftAfter, tailAfter, tailRoots, firstType, sameRoot, firstPosition, tailTyped, tailRooted⟩ :=
    checkedStatefulArgumentList_cursors frame state types checkFuel contextId callOrigin context callee first remaining firstDescriptor
      scope id origin blockOrigin expression intTy literal rest form source contextAt calleeAt parameters firstMode firstDeclared firstScalar
      initialized fresh absent nesting position
  let cursor := { leftAfter with eff := {} }
  let tailFrame := { frame with typingFuel := checkFuel + 4, rootCursor := cursor }
  have tailSource : AcceptedFrame config accepted tailFrame state types := by
    have result := (source.withTypingFuel (checkFuel + 4)).withRootCursor cursor (by simpa [cursor] using sameRoot)
    simpa [tailFrame] using result
  have bounded : GlobalEffectTargetsBounded tailFrame.rootCursor.eff config.module.globals.size := by
    simp [tailFrame, cursor, GlobalEffectTargetsBounded, Eff.accessTargets]
  obtain ⟨tailSpecs, tailExpressions, tailTypes, tailSafe⟩ := checkedScalarArgumentList_safety config accepted context.impl callee calleeAt
    tailDescriptors rest restForms tailFrame state types ambient live regions pending middle tailRoots tailAfter tailSource
    initialized ordinary request requests bounded (by simpa [tailFrame] using tailTyped) (by simpa [tailFrame, cursor] using tailRooted)
  refine ⟨(.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin, firstDescriptor.ty) :: tailSpecs, ?_, ?_, ?_⟩
  · simp [tailExpressions]
  · simp [tailTypes]
  · intro specification member runtimeFuel current currentWorld currentSource
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst specification
      have firstSource := ordinaryOperandFrame_accepted accepted frame (checkFuel + 4) current types currentSource
      have result := evalValue_globalAssign_integerTail_world runtimeFuel checkFuel config accepted
        (ordinaryOperandFrame frame (checkFuel + 4)) current ambient types live regions pending scope id expression origin blockOrigin
        intTy literal form currentWorld firstSource initialized fresh absent firstPosition rfl globalScalar
      have sameTyping : { frame.typing with use := .ordinary, request := .value, resultRequests := [] } = frame.typing := by
        cases typing : frame.typing
        simp_all
      have converted : FirstArgumentOutcome config accepted { frame with typingFuel := checkFuel + 4 }
          ambient types live regions pending (.int intTy) []
          (evalValue runtimeFuel config frame.interpretation.environment (.blockE
            ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) current) := by
        simpa [ordinaryOperandFrame, sameTyping] using result
      have retargeted := FirstArgumentOutcome.retargetCursor (checkFuel + 4) frame.rootCursor rfl (.int intTy) _ converted
      simpa [firstType] using retargeted
    · have currentTail : AcceptedFrame config accepted tailFrame current types := by
        have result := (currentSource.withTypingFuel (checkFuel + 4)).withRootCursor cursor (by simpa [cursor] using sameRoot)
        simpa [tailFrame] using result
      have result := tailSafe specification member runtimeFuel current currentWorld currentTail
      exact FirstArgumentOutcome.retargetCursor (checkFuel + 4) cursor (by simpa [cursor] using sameRoot) specification.2 _ result

#print axioms checkedStatefulArgumentList_safety
end Goose.Proofs.ConstructionAcceptedExecution
