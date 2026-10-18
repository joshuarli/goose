import Goose.Proofs.ExitExecutionPathProducerFrames
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsOwners

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem BuilderBodyChild.escape_build {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {incoming destination : Nat} {expression : Expr}
    {initial prepared ready before : ExecutionState} {β : Type} {child : ExitInvocation β}
    {address : ExitAddress} {carriers : List Carrier}
    (renewed : liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) initial =
      .ok destination prepared)
    (body : BuilderBodyChild fuel config environment destination expression prepared child ready)
    (escaped : child.action config ready = .escape address carriers before) :
    buildExpr (fuel + 1) config environment incoming expression initial =
      protectDestination (expressionOrigin expression) destination
        (fun _ => .escape address carriers (producerBodyEscapedState expression prepared before)) prepared := by
  simp only [buildExpr, bind, renewed]
  cases body
  all_goals simp only [ExitInvocation.action] at escaped
  all_goals simp only [producerBodyEscapedState]
  all_goals simp only [protectDestination]
  case call | condition | values | copy =>
    simp only [escaped]
  case fillValue =>
    rename_i fixed
    simp only [fixed, Bool.false_eq_true, ↓reduceIte, escaped]
  case conditionalResult =>
    rename_i evaluated boolean
    simp only [evaluated, boolean, escaped]
  case blockResult =>
    simp only [producerBreakState] at escaped
    simp only [withBreakTarget, escaped, mapStepState]
  case value =>
    rename_i fallback
    cases expression <;> simp only [builderValueExpression] at fallback <;> try cases fallback
    all_goals try simp only [escaped]
    all_goals split at fallback <;> simp_all [bind]
  case array =>
    rename_i ty beforeList afterList operand origin pending element lookupElem lookupDest preceding
    have loopEscape := producerForEach_escape _ beforeList afterList operand _ _ _ address carriers preceding escaped
    simp only [lookupDest, lookupElem]
    have rawEscape := producerForEach_raw_escape _ _ _ _ _ _ loopEscape
    erw [rawEscape]
  case fillBuild =>
    rename_i dynamic created
    simp only [dynamic, ↓reduceIte, created, escaped]
  case stringArgument =>
    rename_i ty beforeList afterList argument origin preceding
    have argumentEscape : ((do
      let bytes ← evalPrintArg fuel config environment argument
      for byte in bytes.data do receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)) : EvalM Unit) ready =
        .escape address carriers before := by simp only [bind, escaped]
    have loopEscape := producerForEach_escape (fun previous => do
      let bytes ← evalPrintArg fuel config environment previous
      for byte in bytes.data do
        receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩))
      beforeList afterList argument prepared ready before address carriers
      (by simpa only [bind_assoc, pure_bind] using preceding) argumentEscape
    have rawEscape := producerForEach_raw_escape _ _ _ _ _ _ loopEscape
    simp only [bind_assoc, pure_bind] at rawEscape
    erw [rawEscape]

theorem BuilderBodyChild.escape_or_stop_build {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {incoming destination : Nat} {expression : Expr}
    {initial prepared ready before : ExecutionState} {β : Type} {child : ExitInvocation β}
    {address : ExitAddress} {carriers : List Carrier}
    (renewed : liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) initial =
      .ok destination prepared)
    (body : BuilderBodyChild fuel config environment destination expression prepared child ready)
    (escaped : child.action config ready = .escape address carriers before) :
    (∃ final, buildExpr (fuel + 1) config environment incoming expression initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ reason final, buildExpr (fuel + 1) config environment incoming expression initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) := by
  have actual := BuilderBodyChild.escape_build renewed body escaped
  have frame := cleanupReceivingDestination_frame (expressionOrigin expression) destination carriers
    (producerBodyEscapedState expression prepared before)
  cases cleaned : cleanupReceivingDestination (expressionOrigin expression) destination carriers
      (producerBodyEscapedState expression prepared before) with
  | ok value final =>
      cases value
      simp only [protectDestination, cleaned] at actual
      rw [cleaned] at frame
      have same : (producerBodyEscapedState expression prepared before).construction.stdout = before.construction.stdout ∧
          (producerBodyEscapedState expression prepared before).objects = before.objects := by
        cases expression <;> exact ⟨rfl, rfl⟩
      exact Or.inl ⟨final, actual, frame.1.trans same.1, frame.2.trans same.2⟩
  | stop reason final =>
      simp only [protectDestination, cleaned] at actual
      rw [cleaned] at frame
      have same : (producerBodyEscapedState expression prepared before).construction.stdout = before.construction.stdout ∧
          (producerBodyEscapedState expression prepared before).objects = before.objects := by
        cases expression <;> exact ⟨rfl, rfl⟩
      exact Or.inr ⟨reason, final, actual, frame.1.trans same.1, frame.2.trans same.2⟩
  | escape target payload final =>
      exact False.elim (producerNeverEscapes_cleanupReceivingDestination _ _ _ _ _ _ _ cleaned)
  | jump target kind final =>
      exact False.elim (Goose.Proofs.ConstructionDelivery.neverJumps_cleanupReceivingDestination _ _ _ _ _ _ _ cleaned)

theorem ProducerInvocationChild.escape_after_child {config : EvalConfig} {α β : Type}
    {parent : ExitInvocation α} {child : ExitInvocation β}
    {initial prepared before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (edge : ProducerInvocationChild config parent initial child prepared)
    (escaped : child.action config prepared = .escape address carriers before) :
    (∃ final, parent.action config initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) ∨
    (∃ reason final, parent.action config initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects) := by
  cases edge with
  | produce receiving body =>
      have result := ProducerEscapeResult.produce (before := before) receiving body carriers rfl
      exact Or.inl ⟨_, result.propagates escaped, result.frame⟩
  | build renewed body =>
      exact BuilderBodyChild.escape_or_stop_build renewed body escaped
  | elementBuild fuel environment parent element operand initial ready destination dynamic opened =>
      have result := ProducerEscapeResult.elementBuild fuel environment parent element operand initial prepared before destination dynamic opened carriers
      exact Or.inl ⟨_, result.propagates escaped, result.frame⟩
  | elementValue fuel environment parent element operand initial fixed =>
      have result := ProducerEscapeResult.elementValue (config := config) fuel environment parent element operand initial before fixed carriers
      exact Or.inl ⟨_, result.propagates escaped, result.frame⟩

#print axioms ProducerInvocationChild.escape_after_child

#print axioms BuilderBodyChild.escape_or_stop_build

#print axioms BuilderBodyChild.escape_build

end Goose.Proofs.ExitExecution
