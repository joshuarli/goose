import Goose.Proofs.ExitExecutionInvocationProducers
import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def producerBodyEscapedState (expression : Expr) (initial escaped : ExecutionState) : ExecutionState :=
  match expression with
  | .blockE .. => { escaped with breaks := escaped.breaks.filter (fun entry => entry.id != initial.nextScope) }
  | _ => escaped

inductive ProducerEscapeResult (config : EvalConfig) :
    {α β : Type} → ExitInvocation α → ExecutionState → ExitInvocation β → ExecutionState →
      List Carrier → ExecutionState → ExecutionState → Prop
  | produce {fuel : Nat} {environment : RuntimeActivation} {incoming planned channels : List Channel}
      {expression : Expr} {initial prepared ready before final : ExecutionState} {β : Type} {child : ExitInvocation β}
      (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
      (body : ProducerBodyChild fuel config environment planned channels expression prepared child ready)
      (carriers : List Carrier) (landed : final = producerBodyEscapedState expression prepared before) :
      ProducerEscapeResult config (.produce (fuel + 1) environment incoming expression) initial child ready carriers before final
  | build {fuel : Nat} {environment : RuntimeActivation} {incoming destination : Nat}
      {expression : Expr} {initial prepared ready before final : ExecutionState} {β : Type} {child : ExitInvocation β}
      (renewed : liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) initial = .ok destination prepared)
      (body : BuilderBodyChild fuel config environment destination expression prepared child ready)
      (carriers : List Carrier)
      (cleaned : cleanupReceivingDestination (expressionOrigin expression) destination carriers
        (producerBodyEscapedState expression prepared before) = .ok () final) :
      ProducerEscapeResult config (.build (fuel + 1) environment incoming expression) initial child ready carriers before final
  | elementBuild (fuel : Nat) (environment : RuntimeActivation) (parent : Nat) (element : Ty) (operand : Expr)
      (initial ready before : ExecutionState) (child : Nat) (dynamic : element.nonfixed = true)
      (opened : ((do
        let layout ← receivingLayout config.layout element
        receivingAction (expressionOrigin operand) parent (fun parent => openChild parent element layout)) : EvalM Nat)
          initial = .ok child ready) (carriers : List Carrier) :
      ProducerEscapeResult config (.element (fuel + 1) environment parent element operand) initial
        (.build fuel environment child operand) ready carriers before before
  | elementValue (fuel : Nat) (environment : RuntimeActivation) (parent : Nat) (element : Ty) (operand : Expr)
      (initial before : ExecutionState) (fixed : element.nonfixed = false) (carriers : List Carrier) :
      ProducerEscapeResult config (.element (fuel + 1) environment parent element operand) initial
        (.value fuel environment operand) initial carriers before before

private theorem producerForEach_append (action : α → EvalM Unit) (before after : List α) :
    ((do for item in before ++ after do action item) : EvalM Unit) =
      (do (do for item in before do action item); for item in after do action item) := by
  induction before with
  | nil => simp only [List.nil_append, List.forIn_nil, pure_bind]
  | cons item rest ih =>
      simp only [List.cons_append, List.forIn_cons, bind_assoc, pure_bind]
      funext state
      cases result : action item state <;> simp only [bind, result, pure]
      case ok value final =>
        cases value
        have actual := congrFun ih final
        cases restResult : (forIn rest PUnit.unit (fun item _ => do
          action item
          pure (ForInStep.yield PUnit.unit))) final with
        | ok value after => cases value; simp only [bind, pure] at actual; erw [restResult] at actual; exact actual
        | stop reason after | escape target payload after | jump target kind after =>
            simp only [bind, pure] at actual; erw [restResult] at actual; exact actual

private theorem producerForEach_escape (action : α → EvalM Unit) (before after : List α) (item : α)
    (initial ready final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (preceding : ((do for previous in before do action previous) : EvalM Unit) initial = .ok () ready)
    (escaped : action item ready = .escape address carriers final) :
    ((do for previous in before ++ item :: after do action previous) : EvalM Unit) initial =
      .escape address carriers final := by
  rw [producerForEach_append]
  change ((do for previous in before do action previous) >>= fun _ =>
    (do for previous in item :: after do action previous)) initial = .escape address carriers final
  simp only [bind] at preceding
  simp only [bind]
  erw [preceding]
  simp only [List.forIn_cons, bind, escaped]

private theorem producerForEach_raw_escape (action : α → EvalM Unit) (items : List α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do for item in items do action item) : EvalM Unit) initial = .escape address carriers final) :
    (forIn items PUnit.unit (fun item _ => (do action item; pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial =
      .escape address carriers final := by
  cases evaluated : (forIn items PUnit.unit (fun item _ => (do action item; pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial with
  | ok value after | stop reason after | jump target kind after =>
      simp only [bind, pure] at escaped
      erw [evaluated] at escaped
      cases escaped
  | escape target payload after =>
      simp only [bind, pure] at escaped
      erw [evaluated] at escaped
      cases escaped
      rfl

private theorem producerReceiving_continue {environment : RuntimeActivation} {incoming planned channels : List Channel}
    {expression : Expr} {initial prepared : ExecutionState}
    (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
    (next : List Channel → List Channel → EvalM α) :
    ((do
      let renewed ← incoming.mapM fun channel => match channel with
        | .register ty => pure (Channel.register ty)
        | .construct id => do pure (.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
        | .completion token => pure (.completion token)
      let selected ← match expression with
        | .values _ | .ifE .. | .blockE .. => pure renewed
        | _ => renewed.mapM (selectCompletionChannel environment expression)
      next renewed selected) : EvalM α) initial = next planned channels prepared := by
  cases receiving with
  | actual renewedState prepared planned channels renewed selected =>
      simp only [bind] at renewed selected
      simp only [bind]
      erw [renewed]
      cases expression <;> simp only [bind, pure] at selected ⊢ <;> first | (cases selected; rfl) | (erw [selected])

theorem ProducerEscapeResult.propagates {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial ready before final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (landed : ProducerEscapeResult config caller initial child ready carriers before final)
    (escaped : child.action config ready = .escape address carriers before) :
    caller.action config initial = .escape address carriers final := by
  cases landed with
  | produce receiving body carriers landed =>
      subst final
      simp only [ExitInvocation.action, evalProduce]
      refine (producerReceiving_continue receiving _).trans ?_
      cases body
      all_goals simp only [ExitInvocation.action] at escaped
      all_goals simp only [producerBodyEscapedState]
      case value =>
        rename_i fuel environment incoming planned channels expression receivingShape single
        cases receivingShape with
        | inl empty =>
            subst channels
            cases expression <;> simp only [producerSingleExpression] at single <;> try cases single
            all_goals simp only [bind, escaped]
        | inr register =>
            obtain ⟨ty, rfl⟩ := register
            cases expression <;> simp only [producerSingleExpression] at single <;> try cases single
            all_goals simp only [bind, escaped]
      case build =>
        rename_i fuel environment incoming planned expression destination single unnamed
        cases expression <;> simp only [producerSingleExpression] at single <;> try cases single
        all_goals first | exact False.elim (unnamed _ _ rfl) | simp only [bind, escaped]
      case resultLocalBuild =>
        rename_i fuel environment incoming planned preparedState destination localVar origin stored prepared
        simp only [bind] at prepared
        simp only [bind]
        cases root : rootOf environment localVar preparedState with
        | ok location after =>
            cases read : readLoc fuel config.layout ⟨location, []⟩ after with
            | ok value afterRead =>
                cases value <;> simp only [root, read, bind, fault, EvalM.stop, pure] at prepared ⊢
                all_goals try cases prepared
                rename_i stored
                split at prepared
                all_goals
                  simp_all only [bind, pure]
                  split at prepared
                  all_goals simp_all [pure, bind, escaped]
            | stop reason state | escape target payload state | jump target kind state =>
                simp only [root, read] at prepared
                cases prepared
        | stop reason state | escape target payload state | jump target kind state =>
            simp only [root] at prepared
            cases prepared
      case operands | call | condition => simp only [bind, escaped]
      case conditionalResult =>
        rename_i evaluated boolean
        simp only [bind, evaluated, boolean, escaped]
      case blockResult =>
        simp only [producerBreakState] at escaped
        simp only [withBreakTarget, bind, escaped, mapStepState]
  | build renewed body carriers cleaned =>
      simp only [ExitInvocation.action, buildExpr, bind, renewed]
      cases body
      all_goals simp only [ExitInvocation.action] at escaped
      all_goals simp only [producerBodyEscapedState] at cleaned
      all_goals simp only [protectDestination]
      case call | condition | values | copy =>
        simp only [bind, escaped, cleaned]
      case fillValue =>
        rename_i fixed
        simp only [fixed, Bool.false_eq_true, ↓reduceIte, bind, escaped, cleaned]
      case conditionalResult =>
        rename_i evaluated boolean
        simp only [bind, evaluated, boolean, escaped, cleaned]
      case blockResult =>
        simp only [producerBreakState] at escaped
        simp only [withBreakTarget, bind, escaped, mapStepState, cleaned]
      case value =>
        rename_i fuel environment incoming destination expression fallback
        cases expression <;> simp only [builderValueExpression] at fallback <;> try cases fallback
        all_goals try simp only [bind, escaped, cleaned]
        all_goals split at fallback <;> simp_all [bind, escaped, cleaned]
      case array =>
        rename_i fuel environment incoming destination preparedState ty beforeList afterList operand origin pending element lookupElem lookupDest preceding
        have loopEscape := producerForEach_escape _ beforeList afterList operand _ _ _ address carriers preceding escaped
        simp only [bind, lookupDest, lookupElem]
        have rawEscape := producerForEach_raw_escape _ _ _ _ _ _ loopEscape
        erw [rawEscape]
        simp only [cleaned]
      case fillBuild =>
        rename_i dynamic created
        simp only [dynamic, ↓reduceIte, bind, created, escaped, cleaned]
      case stringArgument =>
        rename_i fuel environment incoming destination preparedState ty beforeList afterList argument origin preceding
        have argumentEscape : ((do
          let bytes ← evalPrintArg fuel config environment argument
          for byte in bytes.data do receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)) : EvalM Unit) ready =
            .escape address carriers before := by simp only [bind, escaped]
        have loopEscape := producerForEach_escape (fun previous => do
          let bytes ← evalPrintArg fuel config environment previous
          for byte in bytes.data do
            receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩))
          beforeList afterList argument preparedState ready before address carriers
          (by simpa only [bind_assoc, pure_bind] using preceding) argumentEscape
        have rawEscape := producerForEach_raw_escape _ _ _ _ _ _ loopEscape
        simp only [bind_assoc, pure_bind] at rawEscape
        erw [rawEscape]
        simp only [cleaned]
  | elementBuild fuel environment parent element operand initial ready before child dynamic opened carriers =>
      simp only [ExitInvocation.action] at escaped ⊢
      simp only [buildElement, dynamic, ↓reduceIte]
      simp only [bind] at opened ⊢
      cases layoutResult : receivingLayout config.layout element initial with
      | ok layout afterLayout =>
          simp only [layoutResult] at opened ⊢
          erw [opened]
          simp only [escaped]
      | stop reason state | escape target payload state | jump target kind state =>
          simp only [layoutResult] at opened
          cases opened
  | elementValue fuel environment parent element operand initial before fixed carriers =>
      simp only [ExitInvocation.action] at escaped ⊢
      simp only [buildElement, fixed, Bool.false_eq_true, ↓reduceIte, bind, escaped]

end Goose.Proofs.ExitExecution
