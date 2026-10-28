import Goose.Proofs.ConstructionAcceptedNestedArgument

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

inductive NestedEffectfulArguments : List Expr → Prop
  | nil : NestedEffectfulArguments []
  | cons {expression : Expr} {rest : List Expr} (form : NestedEffectfulArgument expression)
      (tail : NestedEffectfulArguments rest) : NestedEffectfulArguments (expression :: rest)

theorem checkedNestedArgumentList_safety (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    {index : Nat} {parameters : List Param} {parameterTypes : List Ty}
    (descriptors : ScalarParameterDescriptors implementation index parameters parameterTypes) :
    ∀ (expressions : List Expr), NestedEffectfulArguments expressions →
      ∀ (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
        (ambient : OwnershipAmbient) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
        AcceptedFrame config accepted frame state types → frame.initialized = config.module.globals.size →
        frame.typing.use = .ordinary → frame.typing.request = .value → frame.typing.resultRequests = [] →
        GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
        (∀ expression ∈ expressions, NestedArgumentSafe config frame expression) →
        SourcePosition accepted frame (.arguments implementation parameters (expressions.map Arg.byVal)) →
        ∃ specifications : List (Expr × Ty), specifications.map Prod.fst = expressions ∧ specifications.map Prod.snd = parameterTypes ∧
          ∀ specification ∈ specifications, ∀ runtimeFuel current,
            AcceptedWorld config frame.initialized current ambient types live regions pending →
            AcceptedFrame config accepted frame current types →
            FirstArgumentOutcome config accepted frame ambient types live regions pending specification.2 []
              (evalValue runtimeFuel config frame.interpretation.environment specification.1 current) := by
  induction descriptors with
  | nil index =>
    intro expressions forms frame state types ambient live regions pending source initialized ordinary request requests bounded blocks position
    cases expressions with
    | nil =>
      refine ⟨[], rfl, rfl, ?_⟩
      intro specification member
      cases member
    | cons expression rest => cases forms with
      | cons form tail =>
        obtain ⟨typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
        cases fuel : frame.typingFuel with
        | zero => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ fuel => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
  | @cons index parameter parameters parameterTypes parameterAt descriptor declared mode scalar tail ih =>
    intro expressions forms frame state types ambient live regions pending source initialized ordinary request requests bounded blocks position
    cases expressions with
    | nil =>
      obtain ⟨typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
      cases fuel : frame.typingFuel with
      | zero => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ fuel => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | cons expression rest =>
      cases forms with
      | cons form restForms =>
        cases fuelEq : frame.typingFuel with
        | zero =>
          obtain ⟨typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
          rw [fuelEq] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ fuel =>
          have parameterId := validated_parameter_variable config.module implementationId implementation index parameter accepted.accepted implementationAt parameterAt
          have actualDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
          obtain ⟨middle, headRoots, headAfter, headPosition, tailPosition, headTyped, headRooted⟩ :=
            position.arguments_byValue accepted frame implementation parameter descriptor parameters expression (rest.map Arg.byVal) fuel fuelEq mode actualDeclared scalar
          let headFrame := ordinaryOperandFrame frame fuel
          have headSource := ordinaryOperandFrame_accepted accepted frame fuel state types source
          have headBlock : NestedArgumentSafe config headFrame expression := by simpa [NestedArgumentSafe, ArgumentBlockSafe, headFrame, ordinaryOperandFrame] using blocks expression (by simp)
          have headBound : GlobalEffectTargetsBounded headFrame.rootCursor.eff config.module.globals.size := by simpa [headFrame, ordinaryOperandFrame] using bounded
          have head := checkedNestedEffectfulArgument config accepted headFrame state types ambient live regions pending expression descriptor.ty
            headRoots middle headAfter form headBlock headSource initialized headBound headTyped headRooted scalar headPosition
          have sameCounter : middle = frame.typingCounter := by simpa [headFrame, ordinaryOperandFrame] using head.1
          have sameRoot : headAfter.nextVar = frame.rootCursor.nextVar := by simpa [headFrame, ordinaryOperandFrame] using head.2.1
          let tailCursor := { headAfter with eff := {} }
          let tailFrame := { frame with typingFuel := fuel, rootCursor := tailCursor }
          have tailSource : AcceptedFrame config accepted tailFrame state types := by
            have source' := (source.withTypingFuel fuel).withRootCursor tailCursor (by simpa [tailCursor] using sameRoot)
            simpa [tailFrame] using source'
          have tailBound : GlobalEffectTargetsBounded tailFrame.rootCursor.eff config.module.globals.size := by
            simp [tailFrame, tailCursor, GlobalEffectTargetsBounded, Eff.accessTargets]
          have tailBlocks : ∀ item ∈ rest, NestedArgumentSafe config tailFrame item := by
            intro item member
            simpa [NestedArgumentSafe, ArgumentBlockSafe, tailFrame] using blocks item (by simp [member])
          have tailPosition' : SourcePosition accepted tailFrame (.arguments implementation parameters (rest.map Arg.byVal)) := by
            simpa [tailFrame, tailCursor, sameCounter] using tailPosition
          obtain ⟨tailSpecs, tailExpressions, tailTypes, tailSafe⟩ := ih rest restForms tailFrame state types ambient live regions pending
            tailSource initialized ordinary request requests tailBound tailBlocks tailPosition'
          refine ⟨(expression, descriptor.ty) :: tailSpecs, ?_, ?_, ?_⟩
          · simp [tailExpressions]
          · simp [tailTypes]
          · intro specification member runtimeFuel current currentWorld currentSource
            simp only [List.mem_cons] at member
            rcases member with equal | member
            · subst specification
              have actualHead := ordinaryOperandFrame_accepted accepted frame fuel current types currentSource
              have sameTyping : { frame.typing with use := .ordinary, request := .value, resultRequests := [] } = frame.typing := by
                cases typing : frame.typing
                simp_all
              have outcome := head.2.2 runtimeFuel current currentWorld actualHead
              have converted : FirstArgumentOutcome config accepted { frame with typingFuel := fuel } ambient types live regions pending descriptor.ty []
                  (evalValue runtimeFuel config frame.interpretation.environment expression current) := by
                simpa [headFrame, ordinaryOperandFrame, sameTyping] using outcome
              exact FirstArgumentOutcome.retargetCursor fuel frame.rootCursor rfl descriptor.ty _ converted
            · have currentTail : AcceptedFrame config accepted tailFrame current types := by
                have source' := (currentSource.withTypingFuel fuel).withRootCursor tailCursor (by simpa [tailCursor] using sameRoot)
                simpa [tailFrame] using source'
              have actual := tailSafe specification member runtimeFuel current currentWorld currentTail
              exact FirstArgumentOutcome.retargetCursor fuel tailCursor (by simpa [tailCursor] using sameRoot) specification.2 _ actual

#print axioms checkedNestedArgumentList_safety
end Goose.Proofs.ConstructionAcceptedExecution
