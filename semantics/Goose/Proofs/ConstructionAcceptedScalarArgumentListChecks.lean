import Goose.Proofs.ConstructionAcceptedScalarArgumentOutcome
import Goose.Proofs.ConstructionAcceptedArgumentListRoots
import Goose.Proofs.ConstructionAcceptedScalarArgumentListTyping
import Goose.Proofs.ConstructionAcceptedParameterListDescriptors
import Goose.Proofs.ConstructionAcceptedScalarEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

inductive ScalarArgumentExpressions : List Expr → Prop
  | nil : ScalarArgumentExpressions []
  | cons {expression : Expr} {rest : List Expr} (form : AcceptedBinaryExpression expression)
      (tail : ScalarArgumentExpressions rest) : ScalarArgumentExpressions (expression :: rest)

theorem FirstArgumentOutcome.retargetCursor {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {types : RootTypes} {ambient : OwnershipAmbient}
    {live : Goose.Core.RootInst → Prop} {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (fuel : Nat) (cursor : RState) (same : cursor.nextVar = frame.rootCursor.nextVar)
    (ty : Ty) (step : ExecutionStep Value)
    (outcome : FirstArgumentOutcome config accepted { frame with typingFuel := fuel, rootCursor := cursor }
      ambient types live regions pending ty [] step) :
    FirstArgumentOutcome config accepted frame ambient types live regions pending ty [] step := by
  cases step with
  | escape address carriers after | jump target kind after => simp [FirstArgumentOutcome] at outcome
  | stop reason after =>
    have source := outcome.2.1.withRootCursor frame.rootCursor same.symm
    have source := source.withTypingFuel frame.typingFuel
    simpa [FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using And.intro outcome.1 (And.intro source True.intro)
  | ok value after =>
    have source := outcome.2.1.withRootCursor frame.rootCursor same.symm
    have source := source.withTypingFuel frame.typingFuel
    simpa [FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using And.intro outcome.1 (And.intro source outcome.2.2)

theorem checkedScalarArgumentList_safety (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    {index : Nat} {parameters : List Param} {parameterTypes : List Ty}
    (descriptors : ScalarParameterDescriptors implementation index parameters parameterTypes) :
    ∀ (expressions : List Expr), ScalarArgumentExpressions expressions →
      ∀ (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
        (ambient : OwnershipAmbient) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
        (typingAfter : Nat) (allRoots : List (List RootRef)) (rootsAfter : RState),
        AcceptedFrame config accepted frame state types → frame.initialized = config.module.globals.size →
        frame.typing.use = .ordinary → frame.typing.request = .value → frame.typing.resultRequests = [] →
        GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
        typeArguments frame.typingFuel frame.typing implementation parameters (expressions.map Arg.byVal) frame.typingCounter = .ok ((), typingAfter) →
        rpArgs frame.source (expressions.map Arg.byVal) frame.rootCursor = .ok (allRoots, rootsAfter) →
        ∃ specifications : List (Expr × Ty), specifications.map Prod.fst = expressions ∧ specifications.map Prod.snd = parameterTypes ∧
          ∀ specification ∈ specifications, ∀ runtimeFuel current,
            AcceptedWorld config frame.initialized current ambient types live regions pending →
            AcceptedFrame config accepted frame current types →
            FirstArgumentOutcome config accepted frame ambient types live regions pending specification.2 []
              (evalValue runtimeFuel config frame.interpretation.environment specification.1 current) := by
  induction descriptors with
  | nil index =>
    intro expressions forms frame state types ambient live regions pending typingAfter allRoots rootsAfter source initialized ordinary request requests bounded typed rooted
    cases expressions with
    | nil =>
      refine ⟨[], rfl, rfl, ?_⟩
      intro specification member
      cases member
    | cons expression rest =>
      cases fuel : frame.typingFuel with
      | zero => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ fuel => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
  | @cons index parameter parameters parameterTypes parameterAt descriptor declared mode scalar tail ih =>
    intro expressions forms frame state types ambient live regions pending typingAfter allRoots rootsAfter source initialized ordinary request requests bounded typed rooted
    cases expressions with
    | nil =>
      cases fuel : frame.typingFuel with
      | zero => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ fuel => rw [fuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | cons expression rest =>
      cases forms with
      | cons form restForms =>
        cases fuelEq : frame.typingFuel with
        | zero => rw [fuelEq] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ fuel =>
          have parameterId := validated_parameter_variable config.module implementationId implementation index parameter accepted.accepted implementationAt parameterAt
          have actualDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
          have typed' : typeArguments (fuel + 1) frame.typing implementation (parameter :: parameters)
              (.byVal expression :: rest.map Arg.byVal) frame.typingCounter = .ok ((), typingAfter) := by simpa [fuelEq] using typed
          obtain ⟨middle, headTyped, tailTyped⟩ := typeArguments_scalarByValue_cons fuel frame.typing implementation parameter descriptor
            parameters expression (rest.map Arg.byVal) frame.typingCounter typingAfter mode actualDeclared scalar typed'
          obtain ⟨headRoots, headAfter, tailRoots, tailAfter, headRooted, tailRooted⟩ :=
            rpArgs_byValue_cons frame.source expression (rest.map Arg.byVal) frame.rootCursor rootsAfter allRoots (by simpa using rooted)
          let headFrame := ordinaryOperandFrame frame fuel
          have headSource := ordinaryOperandFrame_accepted accepted frame fuel state types source
          have headBounded := recursiveScalar_effects_bounded form fuel headFrame.typing frame.source config.module.globals.size
            frame.typingCounter middle frame.rootCursor headAfter [descriptor.ty] headRoots source.compatible.globals bounded headTyped headRooted
          have headAvailable : GlobalEffectsAvailable headFrame.interpretation headFrame.initialized headAfter.eff := by
            change GlobalEffectsAvailable frame.interpretation frame.initialized headAfter.eff
            rw [initialized, ← source.compatible.globalCount]
            exact (globalEffectsAvailable_iff_bounded frame.interpretation headAfter.eff).2
              (by simpa only [source.compatible.globalCount] using headBounded)
          have headChecked : CheckedValue headFrame expression descriptor.ty headRoots middle headAfter := ⟨headTyped, headRooted, headAvailable⟩
          have cursors := checked_binary_recursive_cursor form headFrame descriptor.ty headRoots middle headAfter headChecked
          have sameCounter : middle = frame.typingCounter := by simpa [headFrame, ordinaryOperandFrame] using cursors.1
          have sameRoot : headAfter.nextVar = frame.rootCursor.nextVar := by simpa [headFrame, ordinaryOperandFrame] using cursors.2
          let tailCursor := { headAfter with eff := {} }
          let tailFrame := { frame with typingFuel := fuel, rootCursor := tailCursor }
          have tailSource : AcceptedFrame config accepted tailFrame state types := by
            have source' := (source.withTypingFuel fuel).withRootCursor tailCursor (by simpa [tailCursor] using sameRoot)
            simpa [tailFrame] using source'
          have tailBound : GlobalEffectTargetsBounded tailFrame.rootCursor.eff config.module.globals.size := by
            simp [tailFrame, tailCursor, GlobalEffectTargetsBounded, Eff.accessTargets]
          have tailTyped' : typeArguments tailFrame.typingFuel tailFrame.typing implementation parameters (rest.map Arg.byVal) tailFrame.typingCounter = .ok ((), typingAfter) := by
            simpa [tailFrame, sameCounter] using tailTyped
          have tailRooted' : rpArgs tailFrame.source (rest.map Arg.byVal) tailFrame.rootCursor = .ok (tailRoots, tailAfter) := by
            simpa [tailFrame, tailCursor] using tailRooted
          obtain ⟨tailSpecs, tailExpressions, tailTypes, tailSafe⟩ := ih rest restForms tailFrame state types ambient live regions pending
            typingAfter tailRoots tailAfter tailSource initialized ordinary request requests tailBound tailTyped' tailRooted'
          refine ⟨(expression, descriptor.ty) :: tailSpecs, ?_, ?_, ?_⟩
          · simp [tailExpressions]
          · simp [tailTypes]
          · intro specification member runtimeFuel current currentWorld currentSource
            simp only [List.mem_cons] at member
            rcases member with equal | member
            · subst specification
              have actualHeadSource := ordinaryOperandFrame_accepted accepted frame fuel current types currentSource
              exact evalValue_checkedScalar_argumentOutcomeAtFrame form runtimeFuel config accepted frame headFrame current ambient types live regions pending
                rfl rfl currentWorld currentSource actualHeadSource descriptor.ty headRoots middle headAfter headChecked scalar
            · have currentTailSource : AcceptedFrame config accepted tailFrame current types := by
                have source' := (currentSource.withTypingFuel fuel).withRootCursor tailCursor (by simpa [tailCursor] using sameRoot)
                simpa [tailFrame] using source'
              have currentTailWorld : AcceptedWorld config tailFrame.initialized current ambient types live regions pending := currentWorld
              have actual := tailSafe specification member runtimeFuel current currentTailWorld currentTailSource
              exact FirstArgumentOutcome.retargetCursor fuel tailCursor (by simpa [tailCursor] using sameRoot)
                specification.2 _ actual

#print axioms checkedScalarArgumentList_safety
#print axioms FirstArgumentOutcome.retargetCursor
end Goose.Proofs.ConstructionAcceptedExecution
