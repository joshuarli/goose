import Goose.Proofs.ExitExecutionPathProducerUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem producerForEach_stop (action : α → EvalM Unit) (before after : List α) (item : α)
    (initial ready final : ExecutionState) (reason : Goose.Core.Stop)
    (preceding : ((do for previous in before do action previous) : EvalM Unit) initial = .ok () ready)
    (stopped : action item ready = .stop reason final) :
    ((do for previous in before ++ item :: after do action previous) : EvalM Unit) initial =
      .stop reason final := by
  rw [producerForEach_append]
  change ((do for previous in before do action previous) >>= fun _ =>
    (do for previous in item :: after do action previous)) initial = .stop reason final
  simp only [bind] at preceding
  simp only [bind]
  erw [preceding]
  simp only [List.forIn_cons, bind, stopped]

private theorem producerForEach_raw_stop (action : α → EvalM Unit) (items : List α)
    (initial final : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : ((do for item in items do action item) : EvalM Unit) initial = .stop reason final) :
    (forIn items PUnit.unit (fun item _ => (do action item; pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial =
      .stop reason final := by
  cases evaluated : (forIn items PUnit.unit (fun item _ => (do action item; pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial with
  | ok value after | escape target payload after | jump target kind after =>
      simp only [bind, pure] at stopped
      erw [evaluated] at stopped
      cases stopped
  | stop target after =>
      simp only [bind, pure] at stopped
      erw [evaluated] at stopped
      cases stopped
      rfl

theorem BuilderBodyChild.stop_build {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {incoming destination : Nat} {expression : Expr}
    {initial prepared ready before : ExecutionState} {β : Type} {child : ExitInvocation β}
    {reason : Goose.Core.Stop}
    (renewed : liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) initial =
      .ok destination prepared)
    (body : BuilderBodyChild fuel config environment destination expression prepared child ready)
    (stopped : child.action config ready = .stop reason before) :
    buildExpr (fuel + 1) config environment incoming expression initial =
      protectDestination (expressionOrigin expression) destination
        (fun _ => .stop reason (producerBodyEscapedState expression prepared before)) prepared := by
  simp only [buildExpr, bind, renewed]
  cases body
  all_goals simp only [ExitInvocation.action] at stopped
  all_goals simp only [producerBodyEscapedState]
  all_goals simp only [protectDestination]
  case call | condition | values | copy =>
    simp only [stopped]
  case fillValue =>
    rename_i fixed
    simp only [fixed, Bool.false_eq_true, ↓reduceIte, stopped]
  case conditionalResult =>
    rename_i evaluated boolean
    simp only [evaluated, boolean, stopped]
  case blockResult =>
    simp only [producerBreakState] at stopped
    simp only [withBreakTarget, stopped, mapStepState]
  case value =>
    rename_i fallback
    cases expression <;> simp only [builderValueExpression] at fallback <;> try cases fallback
    all_goals try simp only [stopped]
    all_goals split at fallback <;> simp_all [bind]
  case array =>
    rename_i ty beforeList afterList operand origin pending element lookupElem lookupDest preceding
    have loopStop := producerForEach_stop _ beforeList afterList operand _ _ _ reason preceding stopped
    simp only [lookupDest, lookupElem]
    have rawStop := producerForEach_raw_stop _ _ _ _ _ loopStop
    erw [rawStop]
  case fillBuild =>
    rename_i dynamic created
    simp only [dynamic, ↓reduceIte, created, stopped]
  case stringArgument =>
    rename_i ty beforeList afterList argument origin preceding
    have argumentStop : ((do
      let bytes ← evalPrintArg fuel config environment argument
      for byte in bytes.data do receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)) : EvalM Unit) ready =
        .stop reason before := by simp only [bind, stopped]
    have loopStop := producerForEach_stop (fun previous => do
      let bytes ← evalPrintArg fuel config environment previous
      for byte in bytes.data do
        receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩))
      beforeList afterList argument prepared ready before reason
      (by simpa only [bind_assoc, pure_bind] using preceding) argumentStop
    have rawStop := producerForEach_raw_stop _ _ _ _ _ loopStop
    simp only [bind_assoc, pure_bind] at rawStop
    erw [rawStop]

theorem ProducerBodyChild.stop_produce {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {incoming planned channels : List Channel} {expression : Expr}
    {initial prepared ready before : ExecutionState} {β : Type} {child : ExitInvocation β}
    {reason : Goose.Core.Stop}
    (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
    (body : ProducerBodyChild fuel config environment planned channels expression prepared child ready)
    (stopped : child.action config ready = .stop reason before) :
    evalProduce (fuel + 1) config environment incoming expression initial =
      .stop reason (producerBodyEscapedState expression prepared before) := by
  simp only [evalProduce]
  refine (producerReceiving_continue receiving _).trans ?_
  cases body
  all_goals simp only [ExitInvocation.action] at stopped
  all_goals simp only [producerBodyEscapedState]
  case value =>
    rename_i receivingShape single
    cases receivingShape with
    | inl empty =>
        subst channels
        cases expression <;> simp only [producerSingleExpression] at single <;> try cases single
        all_goals simp only [bind, stopped]
    | inr register =>
        obtain ⟨ty, rfl⟩ := register
        cases expression <;> simp only [producerSingleExpression] at single <;> try cases single
        all_goals simp only [bind, stopped]
  case build =>
    rename_i destination single unnamed
    cases expression <;> simp only [producerSingleExpression] at single <;> try cases single
    all_goals first | exact False.elim (unnamed _ _ rfl) | simp only [bind, stopped]
  case resultLocalBuild =>
    rename_i destination localVar origin stored namedPrefix
    simp only [bind] at namedPrefix
    simp only [bind]
    cases root : rootOf environment localVar prepared with
    | ok location after =>
        cases read : readLoc fuel config.layout ⟨location, []⟩ after with
        | ok value afterRead =>
            cases value <;> simp only [root, read, fault, EvalM.stop, pure] at namedPrefix ⊢
            all_goals try cases namedPrefix
            rename_i stored
            split at namedPrefix
            all_goals
              simp_all only [bind]
              split at namedPrefix
              all_goals simp_all [pure]
        | stop reason state | escape target payload state | jump target kind state =>
            simp only [root, read] at namedPrefix
            cases namedPrefix
    | stop reason state | escape target payload state | jump target kind state =>
        simp only [root] at namedPrefix
        cases namedPrefix
  case operands | call | condition => simp only [bind, stopped]
  case conditionalResult =>
    rename_i evaluated boolean
    simp only [bind, evaluated, boolean, stopped]
  case blockResult =>
    simp only [producerBreakState] at stopped
    simp only [withBreakTarget, bind, stopped, mapStepState]

theorem ProducerInvocationChild.stop_after_child {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {reason : Goose.Core.Stop}
    (edge : ProducerInvocationChild config parent initial child prepared)
    (stopped : child.action config prepared = .stop reason before) :
    ∃ final, parent.action config initial = .stop reason final ∧
      final.construction = before.construction ∧ final.objects = before.objects := by
  cases edge with
  | produce receiving body =>
      have actual := ProducerBodyChild.stop_produce receiving body stopped
      refine ⟨_, actual, ?_, ?_⟩
      all_goals simp only [producerBodyEscapedState]; split <;> rfl
  | build renewed body =>
      have actual := BuilderBodyChild.stop_build renewed body stopped
      simp only [protectDestination] at actual
      refine ⟨_, actual, ?_, ?_⟩
      all_goals simp only [producerBodyEscapedState]; split <;> rfl
  | elementBuild fuel environment parent element operand initial ready destination dynamic opened =>
      have actual : buildElement (fuel + 1) config environment parent element operand initial = .stop reason before := by
        simp only [ExitInvocation.action] at stopped
        simp only [buildElement, dynamic, ↓reduceIte]
        simp only [bind] at opened ⊢
        cases layoutResult : receivingLayout config.layout element initial with
        | ok layout afterLayout =>
            simp only [layoutResult] at opened ⊢
            erw [opened]
            simp only [stopped]
        | stop reason state | escape target payload state | jump target kind state =>
            simp only [layoutResult] at opened
            cases opened
      exact ⟨before, actual, rfl, rfl⟩
  | elementValue fuel environment parent element operand initial fixed =>
      refine ⟨before, ?_, rfl, rfl⟩
      simp only [ExitInvocation.action] at stopped ⊢
      simp only [buildElement, fixed, Bool.false_eq_true, ↓reduceIte, bind, stopped]

#print axioms ProducerInvocationChild.stop_after_child

#print axioms ProducerBodyChild.stop_produce

#print axioms BuilderBodyChild.stop_build

end Goose.Proofs.ExitExecution
