import Goose.Proofs.ExitExecutionInvocationProducersCausality
import Lean.Elab.Tactic

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def ProducerInvocationCause (config : EvalConfig) (caller : ExitInvocation α) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState) : Prop :=
  ∃ (β : Type) (child : ExitInvocation β) (ready before : ExecutionState),
    ProducerEscapeResult config caller initial child ready carriers before final ∧
    child.action config ready = .escape address carriers before

private theorem producerCause_child {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (child : ExitInvocation β) (ready before : ExecutionState)
    (escaped : child.action config ready = .escape address carriers before)
    (landed : ProducerEscapeResult config caller initial child ready carriers before final) :
    ProducerInvocationCause config caller initial address carriers final :=
  ⟨β, child, ready, before, landed, escaped⟩

theorem ProducerEscapeResult.site {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial ready before final : ExecutionState}
    {carriers : List Carrier}
    (landed : ProducerEscapeResult config caller initial child ready carriers before final) :
    ProducerInvocationChild config caller initial child ready := by
  cases landed with
  | produce receiving body => exact .produce receiving body
  | build renewed body => exact .build renewed body
  | elementBuild => exact .elementBuild _ _ _ _ _ _ _ _ (by assumption) (by assumption)
  | elementValue => exact .elementValue _ _ _ _ _ _ (by assumption)

private theorem producerForEach_escape_inv (action : α → EvalM Unit) (items : List α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do for item in items do action item) : EvalM Unit) initial = .escape address carriers final) :
    ∃ before item after ready, items = before ++ item :: after ∧
      ((do for previous in before do action previous) : EvalM Unit) initial = .ok () ready ∧
      action item ready = .escape address carriers final := by
  induction items generalizing initial with
  | nil => simp only [List.forIn_nil, bind, pure] at escaped; cases escaped
  | cons item rest ih =>
      simp only [List.forIn_cons, bind, pure] at escaped
      cases evaluated : action item initial with
      | ok value ready =>
          cases value
          simp only [evaluated] at escaped
          obtain ⟨before, current, after, prepared, decomposition, preceding, escaped⟩ := ih ready escaped
          refine ⟨item :: before, current, after, prepared, ?_, ?_, escaped⟩
          · rw [decomposition]; rfl
          · simp only [List.forIn_cons, bind, pure, evaluated]
            exact preceding
      | stop reason after | jump target kind after =>
          simp only [evaluated] at escaped
          cases escaped
      | escape target payload after =>
          simp only [evaluated] at escaped
          cases escaped
          exact ⟨[], item, rest, initial, rfl, rfl, evaluated⟩

private theorem producerBind_escape_right_never (action : EvalM α) (next : α → EvalM β)
    (remaining : ∀ value, ProducerNeverEscapes (next value))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    action initial = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value ready =>
      simp only [bind, evaluated] at escaped
      exact False.elim (remaining value ready address carriers final escaped)
  | stop reason after | jump target kind after =>
      simp only [bind, evaluated] at escaped
      cases escaped
  | escape target payload after =>
      simp only [bind, evaluated] at escaped
      cases escaped
      rfl

private theorem producerBind_escape_first_never (action : EvalM α) (next : α → EvalM β)
    (first : ProducerNeverEscapes action)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= next) initial = .escape address carriers final) :
    ∃ value ready, action initial = .ok value ready ∧ next value ready = .escape address carriers final := by
  cases evaluated : action initial with
  | ok value ready =>
      simp only [bind, evaluated] at escaped
      exact ⟨value, ready, rfl, escaped⟩
  | stop reason after | jump target kind after =>
      simp only [bind, evaluated] at escaped
      cases escaped
  | escape target payload after => exact False.elim (first initial target payload after evaluated)

private theorem producerRawForEach_escape_inv (action : α → EvalM Unit) (items : List α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (forIn items PUnit.unit (fun item _ =>
      (do action item; pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial =
        .escape address carriers final) :
    ∃ before item after ready, items = before ++ item :: after ∧
      ((do for previous in before do action previous) : EvalM Unit) initial = .ok () ready ∧
      action item ready = .escape address carriers final := by
  apply producerForEach_escape_inv action items initial final address carriers
  simp only [bind]
  erw [escaped]

private theorem producerStringItem_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (destination : Nat) (origin : Goose.Core.OriginId) (argument : PrintArg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do
      let bytes ← evalPrintArg fuel config environment argument
      for byte in bytes.data do
        receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)) : EvalM Unit)
          initial = .escape address carriers final) :
    evalPrintArg fuel config environment argument initial = .escape address carriers final := by
  apply producerBind_escape_right_never _ _ _ initial final address carriers escaped
  intro bytes
  producer_never_escapes_runtime

private theorem producerStringForEach_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (destination : Nat) (origin : Goose.Core.OriginId) (arguments : List PrintArg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (forIn arguments PUnit.unit (fun argument _ => (do
      let bytes ← evalPrintArg fuel config environment argument
      for byte in bytes.data do
        receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial =
        .escape address carriers final) :
    ∃ before argument after ready, arguments = before ++ argument :: after ∧
      ((do for previous in before do
        let bytes ← evalPrintArg fuel config environment previous
        for byte in bytes.data do
          receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)) : EvalM Unit)
            initial = .ok () ready ∧
      evalPrintArg fuel config environment argument ready = .escape address carriers final := by
  have rawEscape : (forIn arguments PUnit.unit (fun argument _ => (do
      (do
        let bytes ← evalPrintArg fuel config environment argument
        for byte in bytes.data do
          receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩))
      pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) initial =
        .escape address carriers final := by
    simpa only [bind_assoc, pure_bind] using escaped
  obtain ⟨before, argument, after, ready, decomposition, preceding, childEscape⟩ :=
    producerRawForEach_escape_inv _ _ _ _ _ _ rawEscape
  refine ⟨before, argument, after, ready, decomposition, ?_, ?_⟩
  · simpa only [bind_assoc, pure_bind] using preceding
  · exact producerStringItem_escape_inv fuel config environment destination origin argument ready final address carriers childEscape

private theorem producerNeverEscapes_renewChannels (incoming : List Channel) (expression : Expr) :
    ProducerNeverEscapes ((incoming.mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct id => do pure (.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
      | .completion token => pure (.completion token)) : EvalM (List Channel)) := by
  apply producerNeverEscapes_listMapM
  intro channel
  cases channel <;> producer_never_escapes_runtime

private theorem producerNeverEscapes_selectChannels (environment : RuntimeActivation) (channels : List Channel) (expression : Expr) :
    ProducerNeverEscapes (channels.mapM (selectCompletionChannel environment expression)) :=
  producerNeverEscapes_listMapM _ _ (producerNeverEscapes_selectCompletionChannel _ _)

private theorem producerReceiving_escape_prefix (environment : RuntimeActivation) (incoming : List Channel)
    (expression : Expr) (next : List Channel → List Channel → EvalM α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do
      let renewed ← incoming.mapM fun channel => match channel with
        | .register ty => pure (Channel.register ty)
        | .construct id => do pure (.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
        | .completion token => pure (.completion token)
      let selected ← match expression with
        | .values _ | .ifE .. | .blockE .. => pure renewed
        | _ => renewed.mapM (selectCompletionChannel environment expression)
      next renewed selected) : EvalM α) initial = .escape address carriers final) :
    ∃ planned channels prepared,
      ProducerReceivingPrefix environment incoming expression initial planned channels prepared ∧
      next planned channels prepared = .escape address carriers final := by
  obtain ⟨planned, renewedState, renewed, selectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_renewChannels incoming expression)
      initial final address carriers escaped
  cases expression
  all_goals first
    | exact ⟨planned, planned, renewedState,
        .actual initial renewedState renewedState planned planned renewed rfl, selectedEscape⟩
    | (obtain ⟨channels, prepared, selected, rest⟩ :=
        producerBind_escape_first_never _ _ (producerNeverEscapes_selectChannels _ _ _)
          renewedState final address carriers selectedEscape
       exact ⟨planned, channels, prepared,
         .actual initial renewedState prepared planned channels renewed selected, rest⟩)

private theorem producerNeverEscapes_landCarriersInto (origin : Goose.Core.OriginId)
    (channels : List Channel) (carriers : List Carrier) : ProducerNeverEscapes (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  repeat' first
    | exact producerNeverEscapes_carrierValue _
    | producer_never_escapes_runtime_step

private theorem producerProtect_escape_inv (origin : Goose.Core.OriginId) (destination : Nat) (action : EvalM α)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : protectDestination origin destination action initial = .escape address carriers final) :
    ∃ before, action initial = .escape address carriers before ∧
      cleanupReceivingDestination origin destination carriers before = .ok () final := by
  cases evaluated : action initial with
  | ok value after | stop reason after =>
      simp only [protectDestination, evaluated] at escaped
      cases escaped
  | escape target payload before =>
      cases cleaned : cleanupReceivingDestination origin destination payload before with
      | ok ignored after =>
          cases ignored
          simp only [protectDestination, evaluated, cleaned] at escaped
          cases escaped
          exact ⟨before, rfl, cleaned⟩
      | stop reason after | jump target kind after =>
          simp only [protectDestination, evaluated, cleaned] at escaped
          cases escaped
      | escape target values after =>
          exact False.elim (producerNeverEscapes_cleanupReceivingDestination origin destination payload before target values after cleaned)
  | jump target kind before =>
      simp only [protectDestination, evaluated] at escaped
      split at escaped
      all_goals first
        | (solve | simp_all only [producerNeverEscapes_cleanupReceivingDestination])
        | cases escaped

private theorem producerNeverEscapes_listBytes (origin : Goose.Core.OriginId) (destination : Nat) (bytes : List UInt8) :
    ProducerNeverEscapes (forIn bytes PUnit.unit (fun byte _ =>
      (do
        receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)
        pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) := by
  producer_never_escapes_runtime

private theorem producerNeverEscapes_arrayBytes (origin : Goose.Core.OriginId) (destination : Nat) (bytes : Array UInt8) :
    ProducerNeverEscapes (forIn bytes PUnit.unit (fun byte _ =>
      (do
        receivingAction origin destination (fun destination => writeElement destination ⟨#[byte]⟩)
        pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) := by
  producer_never_escapes_runtime

private theorem producerNeverEscapes_writeRange (origin : Goose.Core.OriginId) (destination : Nat)
    (bytes : ByteArray) (count : Nat) :
    ProducerNeverEscapes (forIn [0:count] PUnit.unit (fun _ _ =>
      (do
        receivingAction origin destination (fun destination => writeElement destination bytes)
        pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) := by
  producer_never_escapes_runtime

private theorem producerNeverEscapes_repeatRange (fuel : Nat) (layout : LayoutEnv) (destination : Nat)
    (element : Ty) (source : Nat) (origin : Goose.Core.OriginId) (count : Nat) :
    ProducerNeverEscapes (forIn [0:count] PUnit.unit (fun _ _ =>
      (do
        repeatElement fuel layout destination element source origin
        pure (ForInStep.yield PUnit.unit) : EvalM (ForInStep PUnit))) : EvalM PUnit) := by
  repeat' first | exact producerNeverEscapes_repeatElement _ _ _ _ _ _ | producer_never_escapes_runtime_step

private theorem producerNeverEscapes_expectBool (value : Value) : ProducerNeverEscapes (expectBool value) := by
  cases value <;> simp only [expectBool]
  all_goals first | exact producerNeverEscapes_pure _ | exact producerNeverEscapes_fault _

private theorem producerNeverEscapes_resultFlow (result : Flow × List Carrier) :
    ProducerNeverEscapes ((match result.fst with
      | .normal _ => pure result.snd
      | _ => fault .flow) : EvalM (List Carrier)) := by
  rcases result with ⟨flow, values⟩
  cases flow
  all_goals first | exact producerNeverEscapes_pure _ | exact producerNeverEscapes_fault _

private theorem producerNeverEscapes_unitFlow (result : Flow × List Carrier) :
    ProducerNeverEscapes ((match result.fst with
      | .normal _ => pure ()
      | _ => fault .flow) : EvalM Unit) := by
  rcases result with ⟨flow, values⟩
  cases flow
  all_goals first | exact producerNeverEscapes_pure _ | exact producerNeverEscapes_fault _

private theorem producerResultLocal_prefix {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {destination localVar : Nat} {origin : Goose.Core.OriginId} {planned : List Channel}
    {initial afterRoot afterRead ready : ExecutionState} {root : Goose.Core.RootInst} {stored : StoredValue}
    (rootDone : rootOf environment localVar initial = .ok root afterRoot)
    (readDone : readLoc fuel config.layout ⟨root, []⟩ afterRoot = .ok (.stored stored) afterRead)
    (namedDone : ((match planned with
      | [.completion token] => prepareNamedCarrierAt origin token destination stored
      | _ => prepareNamedCarrier origin destination stored) : EvalM (Option Carrier)) afterRead = .ok none ready) :
    ((do
      let .stored actual ← readLoc fuel config.layout ⟨← rootOf environment localVar, []⟩ | fault .shape
      let named ← match planned with
        | [.completion token] => prepareNamedCarrierAt origin token destination actual
        | _ => prepareNamedCarrier origin destination actual
      pure (actual, named)) : EvalM (StoredValue × Option Carrier)) initial = .ok (stored, none) ready := by
  simp only [bind, rootDone, readDone]
  cases planned with
  | nil => simp only [bind, namedDone, pure]
  | cons channel rest =>
      cases rest with
      | cons next rest => cases channel <;> simp only [bind] at namedDone ⊢ <;> simpa only [namedDone, pure]
      | nil => cases channel <;> simp only [bind] at namedDone ⊢ <;> simpa only [namedDone, pure]

private theorem producerResultLocal_cause {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {incoming planned : List Channel} {destination localVar : Nat} {origin : Goose.Core.OriginId}
    {initial prepared afterRoot afterRead ready final : ExecutionState} {root : Goose.Core.RootInst}
    {stored : StoredValue} {address : ExitAddress} {carriers : List Carrier}
    (rootDone : rootOf environment localVar prepared = .ok root afterRoot)
    (readDone : readLoc fuel config.layout ⟨root, []⟩ afterRoot = .ok (.stored stored) afterRead)
    (namedDone : ((match planned with
      | [.completion token] => prepareNamedCarrierAt origin token destination stored
      | _ => prepareNamedCarrier origin destination stored) : EvalM (Option Carrier)) afterRead = .ok none ready)
    (receiving : ProducerReceivingPrefix environment incoming (.resultLocal localVar origin) initial planned [.construct destination] prepared)
    (escaped : buildExpr fuel config environment destination (.resultLocal localVar origin) ready = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment incoming (.resultLocal localVar origin)) initial address carriers final := by
  exact ⟨_, .build fuel environment destination (.resultLocal localVar origin), ready, final,
    .produce receiving (.resultLocalBuild destination localVar origin prepared ready stored
      (producerResultLocal_prefix rootDone readDone namedDone)) carriers rfl, escaped⟩

private theorem producerQuery_ok_state (action : EvalM α) (query : StateQuery action)
    {initial final : ExecutionState} {value : α} (evaluated : action initial = .ok value final) :
    final = initial := by
  simpa only [evaluated, Goose.Proofs.Exit.stepState] using query initial

elab "producer_query_ok_state" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type ← Lean.instantiateMVars declaration.type
    unless type.isAppOfArity ``Eq 3 do continue
    let arguments := type.getAppArgs
    let left := arguments[1]!
    let right := arguments[2]!
    unless right.getAppFn.isConstOf ``ExecutionStep.ok do continue
    let some name := left.getAppFn.constName? | continue
    let queryName ← if name == ``getDestination then pure ``stateQuery_getDestination
      else if name == ``expectBool then pure ``stateQuery_expectBool
      else continue
    let actionArguments := left.getAppArgs
    let initial := actionArguments.back!
    let final := right.getAppArgs.back!
    if ← Lean.Meta.isDefEq initial final then continue
    let query ← Lean.Meta.mkAppM queryName (actionArguments.extract 0 (actionArguments.size - 1))
    let unchanged ← Lean.Meta.mkAppM ``producerQuery_ok_state #[left.appFn!, query, declaration.toExpr]
    let (equation, goal) ← (← Lean.Elab.Tactic.getMainGoal).note `producerQueryState unchanged
    let goal ← Lean.Meta.subst goal equation
    Lean.Elab.Tactic.replaceMainGoal [goal]
    return
  throwError "no successful state query to normalize"

elab "producer_generalize_match " hypothesis:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let hypothesisId ← Lean.Elab.Tactic.getFVarId hypothesis
  let type ← Lean.instantiateMVars (← hypothesisId.getType)
  unless type.isAppOfArity ``Eq 3 do throwError "expected escape equality"
  let some application ← Lean.Meta.matchMatcherApp? type.getAppArgs[1]! | throwError "expected native match"
  let some discriminant := application.discrs.find? (fun expression => !expression.isFVar) |
    throwError "native match already has variable discriminants"
  let (_, _, goal) ← (← Lean.Elab.Tactic.getMainGoal).generalizeHyp
    #[{ expr := discriminant, xName? := some `producerDiscriminant, hName? := some `producerDiscriminantEq }]
    #[hypothesisId]
  Lean.Elab.Tactic.replaceMainGoal [goal]

elab "producer_escape_refocus " hypothesis:ident : tactic => Lean.Elab.Tactic.withMainContext do
  if ((← Lean.getLCtx).findFromUserName? hypothesis.getId).isSome then
    throwError "escape equation still present"
  let mut selected : Option Lean.Expr := none
  let mut selectedSize := 1000000000
  for declaration in (← Lean.getLCtx) do
    let type ← Lean.instantiateMVars declaration.type
    unless type.isAppOfArity ``Eq 3 do continue
    let arguments := type.getAppArgs
    unless arguments[2]!.getAppFn.isConstOf ``ExecutionStep.escape do continue
    if [``ExecutionStep.ok, ``ExecutionStep.stop, ``ExecutionStep.escape, ``ExecutionStep.jump].any
        arguments[1]!.getAppFn.isConstOf then continue
    let size := arguments[1]!.sizeWithoutSharing
    if size < selectedSize then
      selected := some declaration.toExpr
      selectedSize := size
  let some proof := selected | throwError "no native escape equation"
  let (_, goal) ← (← Lean.Elab.Tactic.getMainGoal).note hypothesis.getId proof
  Lean.Elab.Tactic.replaceMainGoal [goal]

private def producerHasEscapeHead (names : List Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    for declaration in (← Lean.getLCtx) do
      let type ← Lean.instantiateMVars declaration.type
      unless type.isAppOfArity ``Eq 3 do continue
      let arguments := type.getAppArgs
      unless arguments[2]!.getAppFn.isConstOf ``ExecutionStep.escape do continue
      if names.any arguments[1]!.getAppFn.isConstOf then return
    throwError "no native escape action"

elab "producer_child_escape_head" : tactic =>
  producerHasEscapeHead [``evalValue, ``evalOperands, ``buildExpr, ``buildElement,
    ``invokeCall, ``execResultBlock, ``evalPlace, ``evalPrintArg]

elab "producer_callback_escape_head" : tactic =>
  producerHasEscapeHead [``List.mapM, ``ForIn.forIn]

macro "producer_escape_native" : tactic => `(tactic|
  first
  | (producer_callback_escape_head; exact False.elim (producerNeverEscapes_renewChannels _ _ _ _ _ _ (by assumption)))
  | (producer_callback_escape_head; exact False.elim (producerNeverEscapes_selectChannels _ _ _ _ _ _ _ (by assumption)))
  | (producer_callback_escape_head; exact False.elim (producerNeverEscapes_listBytes _ _ _ _ _ _ _ (by assumption)))
  | (producer_callback_escape_head; exact False.elim (producerNeverEscapes_arrayBytes _ _ _ _ _ _ _ (by assumption)))
  | (producer_callback_escape_head; exact False.elim (producerNeverEscapes_writeRange _ _ _ _ _ _ _ _ (by assumption)))
  | (producer_callback_escape_head; exact False.elim (producerNeverEscapes_repeatRange _ _ _ _ _ _ _ _ _ _ _ (by assumption)))
  | simp_all only [producerNeverEscapes_renewChannels, producerNeverEscapes_selectChannels,
    producerNeverEscapes_liftConstruction, producerNeverEscapes_get, producerNeverEscapes_pure,
    producerNeverEscapes_timeout, producerNeverEscapes_fault, producerNeverEscapes_readLoc,
    producerNeverEscapes_expectBool, producerNeverEscapes_resultFlow, producerNeverEscapes_unitFlow,
    producerNeverEscapes_rootOf, producerNeverEscapes_receivingAction, producerNeverEscapes_getDestination,
    producerNeverEscapes_receivingLayout, producerNeverEscapes_completedReceivingDestination,
    producerNeverEscapes_prepareNamedCarrier, producerNeverEscapes_prepareNamedCarrierAt,
    producerNeverEscapes_cleanupReceivingDestination, producerNeverEscapes_newDestination,
    producerNeverEscapes_singleCarrier, producerNeverEscapes_receivingDestination,
    producerNeverEscapes_copyValue, producerNeverEscapes_repeatElement,
    producerNeverEscapes_liftExcept, producerNeverEscapes_landCarriersInto,
    producerNeverEscapes_listBytes, producerNeverEscapes_arrayBytes,
    producerNeverEscapes_writeRange, producerNeverEscapes_repeatRange])


macro "producer_escape_witness " receiving:ident : tactic => `(tactic|
  (producer_child_escape_head; first
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.value _ _ _ (by rfl) (Or.inl rfl)) _ rfl))
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.value _ _ _ (by rfl) (Or.inr ⟨_, rfl⟩)) _ rfl))
    | (solve | (exact producerResultLocal_cause (by assumption) (by assumption) (by assumption) $receiving:ident (by assumption)))
    | (solve | (refine producerCause_child (.build ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.build _ _ _ (by rfl) (by intro localVar origin impossible; cases impossible)) _ rfl))
    | (solve | (refine producerCause_child (.operands ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.operands ..) _ rfl))
    | (solve | (refine producerCause_child (.call ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.call ..) _ rfl))
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.condition ..) _ rfl))
    | (solve | (refine producerCause_child (.resultBlock ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.conditionalResult (evaluated := by assumption) (boolean := by first | assumption | simp_all [expectBool]) ..) _ rfl))
    | (solve | (refine producerCause_child (.resultBlock ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .produce $receiving:ident (.blockResult ..) _ rfl))))


macro "builder_escape_witness" : tactic => `(tactic|
  (producer_child_escape_head; first
    | (solve | (refine producerCause_child (.call ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.call ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.condition ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.build ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.values ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.place ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.copy ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.value (fallback := by simp only [builderValueExpression]) ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.resultBlock ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.conditionalResult (evaluated := by assumption) (boolean := by first | assumption | simp_all [expectBool]) ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.resultBlock ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.blockResult ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.build ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.fillBuild (dynamic := by assumption) (created := by assumption) ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.fillValue (fixed := by exact Bool.eq_false_iff.mpr (by assumption)) ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.element ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.array (lookup := by first | assumption | simp_all only [getDestination, EvalM.get, bind, pure]) (elementType := by assumption) (preceding := by assumption) ..) _ (by assumption)))
    | (solve | (refine producerCause_child (.printArgument ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .build (by assumption) (.stringArgument (preceding := by assumption) ..) _ (by assumption)))))

macro "builder_escape_mapped" : tactic => `(tactic|
  (producer_callback_escape_head; first
    | (obtain ⟨earlier, item, rest, ready, decomposition, preceding, childEscape⟩ :=
        producerRawForEach_escape_inv _ _ _ _ _ _ (by assumption)
       cases decomposition
       builder_escape_witness)
    | (obtain ⟨earlier, argument, rest, ready, decomposition, preceding, childEscape⟩ :=
        producerStringForEach_escape_inv _ _ _ _ _ _ _ _ _ _ (by assumption)
       cases decomposition
       builder_escape_witness)))

macro "element_escape_witness" : tactic => `(tactic|
  (producer_child_escape_head; first
    | (solve | (refine producerCause_child (.build ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .elementBuild (dynamic := by assumption) (opened := by simp_all only [bind, pure]) ..))
    | (solve | (refine producerCause_child (.value ..) _ _ (by simp only [ExitInvocation.action, producerBreakState]; assumption) ?_; exact .elementValue (fixed := by exact Bool.eq_false_iff.mpr (by assumption)) ..))))

elab "producer_escape_constructor " hypothesis:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let hypothesisId ← Lean.Elab.Tactic.getFVarId hypothesis
  let declaration ← hypothesisId.getDecl
  let type ← Lean.instantiateMVars declaration.type
  unless type.getAppFn.isConstOf ``Eq do throwError "expected equality"
  let left := type.getAppArgs[1]!
  unless left.isFVar || [``ExecutionStep.ok, ``ExecutionStep.stop, ``ExecutionStep.escape, ``ExecutionStep.jump].any left.getAppFn.isConstOf do
    throwError "expected execution constructor or variable"
  Lean.Elab.Tactic.evalTactic (← `(tactic| cases $hypothesis:ident))

syntax "producer_escape_steps " ident ident : tactic
macro_rules
  | `(tactic| producer_escape_steps $escaped:ident $receiving:ident) => `(tactic|
    repeat' first
      | producer_escape_witness $receiving:ident
      | (solve | producer_escape_native)
      | producer_query_ok_state
      | producer_escape_constructor $escaped:ident
      | simp only [bind, pure, fault, EvalM.stop] at $escaped:ident
      | producer_generalize_match $escaped:ident
      | split at $escaped:ident
      | producer_escape_refocus $escaped:ident)

private theorem producerSource_lit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Goose.Core.IntTy) (n : Int) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.lit t n) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.lit t n)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_bool_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (b : Bool) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.bool b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.bool b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_read_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (p : Place) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.read p) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.read p)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_ref_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (m : Goose.Core.Mutability) (p : Place) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.ref m p) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.ref m p)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_slice_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.slice m v lo hi org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.slice m v lo hi org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_len_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (v : View) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.len v) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.len v)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_un_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.UnOp) (e : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.un op e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.un op e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_bin_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.BinOp) (a b : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.bin op a b org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.bin op a b org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_cmp_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.CmpOp) (a b : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.cmp op a b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.cmp op a b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_and_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (a b : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.and a b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.and a b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_or_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (a b : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.or a b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.or a b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_not_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (e : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.not e) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.not e)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_conv_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.conv k target e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.conv k target e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_call_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (c : Nat) (args : List Arg) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.call c args org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.call c args org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_push_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (owner : Place) (e : Expr) (org : Option Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.push owner e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.push owner e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_pop_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (owner : Place) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.pop owner org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.pop owner org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_ifE_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (c : Expr) (thenB elseB : Block) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.ifE c thenB elseB org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.ifE c thenB elseB org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_blockE_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (b : Block) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.blockE b org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.blockE b org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  simp only [bind, pure, withBreakTarget, mapStepState] at bodyEscape
  cases evaluated : execResultBlock fuel config environment actualChannels b (producerBreakState environment actualChannels prepared)
  all_goals simp only [producerBreakState] at evaluated
  all_goals simp only [evaluated] at bodyEscape
  all_goals producer_escape_steps bodyEscape receiving


private theorem producerSource_arrLit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (es : List Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.arrLit t es org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.arrLit t es org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_fill_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (e : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.fill t e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.fill t e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_structLit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (es : List Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.structLit t es) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.structLit t es)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_bytes_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (data : List UInt8) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.bytes t data org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.bytes t data org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_str_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (args : List PrintArg) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.str t args org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.str t args org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_copy_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (source : Place) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.copy t source org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.copy t source org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


private theorem producerSource_resultLocal_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (var : Nat) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.resultLocal var org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.resultLocal var org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  cases planned with
  | nil => producer_escape_steps bodyEscape receiving
  | cons channel rest =>
      cases rest with
      | nil => cases channel <;> producer_escape_steps bodyEscape receiving
      | cons next rest => cases channel <;> producer_escape_steps bodyEscape receiving


private theorem producerSource_values_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce (fuel + 1) config environment channels (.values operands) initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce (fuel + 1) environment channels (.values operands)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [evalProduce] at escaped
  obtain ⟨planned, actualChannels, prepared, receiving, bodyEscape⟩ :=
    producerReceiving_escape_prefix environment channels _ _ initial final address carriers escaped
  clear escaped
  try simp only [bind, pure] at bodyEscape
  producer_escape_steps bodyEscape receiving


theorem produceInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalProduce fuel config environment channels expression initial = .escape address carriers final) :
    ProducerInvocationCause config (.produce fuel environment channels expression) initial address carriers final := by
  cases fuel with
  | zero => simp only [evalProduce, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      cases expression with

      | lit t n => exact producerSource_lit_escape_inv fuel config environment channels t n initial address carriers final escaped

      | bool b => exact producerSource_bool_escape_inv fuel config environment channels b initial address carriers final escaped

      | read p => exact producerSource_read_escape_inv fuel config environment channels p initial address carriers final escaped

      | ref m p => exact producerSource_ref_escape_inv fuel config environment channels m p initial address carriers final escaped

      | slice m v lo hi org => exact producerSource_slice_escape_inv fuel config environment channels m v lo hi org initial address carriers final escaped

      | len v => exact producerSource_len_escape_inv fuel config environment channels v initial address carriers final escaped

      | un op e org => exact producerSource_un_escape_inv fuel config environment channels op e org initial address carriers final escaped

      | bin op a b org => exact producerSource_bin_escape_inv fuel config environment channels op a b org initial address carriers final escaped

      | cmp op a b => exact producerSource_cmp_escape_inv fuel config environment channels op a b initial address carriers final escaped

      | and a b => exact producerSource_and_escape_inv fuel config environment channels a b initial address carriers final escaped

      | or a b => exact producerSource_or_escape_inv fuel config environment channels a b initial address carriers final escaped

      | not e => exact producerSource_not_escape_inv fuel config environment channels e initial address carriers final escaped

      | conv k target e org => exact producerSource_conv_escape_inv fuel config environment channels k target e org initial address carriers final escaped

      | call c args org => exact producerSource_call_escape_inv fuel config environment channels c args org initial address carriers final escaped

      | push owner e org => exact producerSource_push_escape_inv fuel config environment channels owner e org initial address carriers final escaped

      | pop owner org => exact producerSource_pop_escape_inv fuel config environment channels owner org initial address carriers final escaped

      | ifE c thenB elseB org => exact producerSource_ifE_escape_inv fuel config environment channels c thenB elseB org initial address carriers final escaped

      | blockE b org => exact producerSource_blockE_escape_inv fuel config environment channels b org initial address carriers final escaped

      | arrLit t es org => exact producerSource_arrLit_escape_inv fuel config environment channels t es org initial address carriers final escaped

      | fill t e org => exact producerSource_fill_escape_inv fuel config environment channels t e org initial address carriers final escaped

      | structLit t es => exact producerSource_structLit_escape_inv fuel config environment channels t es initial address carriers final escaped

      | bytes t data org => exact producerSource_bytes_escape_inv fuel config environment channels t data org initial address carriers final escaped

      | str t args org => exact producerSource_str_escape_inv fuel config environment channels t args org initial address carriers final escaped

      | copy t source org => exact producerSource_copy_escape_inv fuel config environment channels t source org initial address carriers final escaped

      | resultLocal var org => exact producerSource_resultLocal_escape_inv fuel config environment channels var org initial address carriers final escaped

      | values operands => exact producerSource_values_escape_inv fuel config environment channels operands initial address carriers final escaped

syntax "builder_escape_steps " ident : tactic
macro_rules
  | `(tactic| builder_escape_steps $escaped:ident) => `(tactic|
    repeat' first
      | builder_escape_witness
      | (solve | builder_escape_mapped)
      | (solve | producer_escape_native)
      | producer_query_ok_state
      | producer_escape_constructor $escaped:ident
      | simp only [bind, pure, fault, EvalM.stop] at $escaped:ident
      | producer_generalize_match $escaped:ident
      | split at $escaped:ident
      | producer_escape_refocus $escaped:ident)

private theorem builderSource_lit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Goose.Core.IntTy) (n : Int) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.lit t n) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.lit t n)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.lit t n)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_bool_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (b : Bool) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.bool b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.bool b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.bool b)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_read_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (p : Place) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.read p) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.read p)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.read p)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_ref_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (m : Goose.Core.Mutability) (p : Place) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.ref m p) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.ref m p)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.ref m p)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_slice_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.slice m v lo hi org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.slice m v lo hi org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.slice m v lo hi org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_len_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (v : View) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.len v) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.len v)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.len v)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_un_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (op : Goose.Core.UnOp) (e : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.un op e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.un op e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.un op e org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_bin_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (op : Goose.Core.BinOp) (a b : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.bin op a b org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.bin op a b org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.bin op a b org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_cmp_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (op : Goose.Core.CmpOp) (a b : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.cmp op a b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.cmp op a b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.cmp op a b)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_and_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (a b : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.and a b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.and a b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.and a b)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_or_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (a b : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.or a b) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.or a b)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.or a b)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_not_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (e : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.not e) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.not e)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.not e)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_conv_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.conv k target e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.conv k target e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.conv k target e org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_call_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (c : Nat) (args : List Arg) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.call c args org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.call c args org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.call c args org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_push_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (owner : Place) (e : Expr) (org : Option Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.push owner e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.push owner e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.push owner e org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_pop_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (owner : Place) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.pop owner org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.pop owner org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.pop owner org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_ifE_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (c : Expr) (thenB elseB : Block) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.ifE c thenB elseB org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.ifE c thenB elseB org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.ifE c thenB elseB org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_blockE_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (b : Block) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.blockE b org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.blockE b org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.blockE b org)) destination _ prepared final address carriers protectedEscape
  clear escaped protectedEscape
  simp only [withBreakTarget, mapStepState, bind, pure] at bodyEscape
  cases evaluated : execResultBlock fuel config environment [.construct destination] b (producerBreakState environment [.construct destination] prepared)
  all_goals simp only [producerBreakState] at evaluated
  all_goals simp only [evaluated] at bodyEscape
  all_goals builder_escape_steps bodyEscape


private theorem builderSource_arrLit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Ty) (es : List Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.arrLit t es org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.arrLit t es org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.arrLit t es org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_fill_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Ty) (e : Expr) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.fill t e org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.fill t e org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.fill t e org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_structLit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Ty) (es : List Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.structLit t es) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.structLit t es)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.structLit t es)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_bytes_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Ty) (data : List UInt8) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.bytes t data org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.bytes t data org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.bytes t data org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_str_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Ty) (args : List PrintArg) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.str t args org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.str t args org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.str t args org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_copy_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (t : Ty) (source : Place) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.copy t source org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.copy t source org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.copy t source org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_resultLocal_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (var : Nat) (org : Nat) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.resultLocal var org) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.resultLocal var org)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.resultLocal var org)) destination _ prepared final address carriers protectedEscape
  builder_escape_steps bodyEscape


private theorem builderSource_values_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (operands : List Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr (fuel + 1) config environment incoming (.values operands) initial = .escape address carriers final) :
    ProducerInvocationCause config (.build (fuel + 1) environment incoming (.values operands)) initial address carriers final := by
  unfold ProducerInvocationCause
  simp only [buildExpr] at escaped
  obtain ⟨destination, prepared, renewed, protectedEscape⟩ :=
    producerBind_escape_first_never _ _ (producerNeverEscapes_liftConstruction _ _) initial final address carriers escaped
  obtain ⟨beforeCleanup, bodyEscape, cleaned⟩ :=
    producerProtect_escape_inv (expressionOrigin (.values operands)) destination _ prepared final address carriers protectedEscape
  clear escaped protectedEscape
  cases operands with
  | nil => builder_escape_steps bodyEscape
  | cons operand rest =>
      cases rest with
      | nil => builder_escape_steps bodyEscape
      | cons next rest => builder_escape_steps bodyEscape


theorem buildInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (incoming : Nat) (expression : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildExpr fuel config environment incoming expression initial = .escape address carriers final) :
    ProducerInvocationCause config (.build fuel environment incoming expression) initial address carriers final := by
  cases fuel with
  | zero => simp only [buildExpr, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      cases expression with

      | lit t n => exact builderSource_lit_escape_inv fuel config environment incoming t n initial address carriers final escaped

      | bool b => exact builderSource_bool_escape_inv fuel config environment incoming b initial address carriers final escaped

      | read p => exact builderSource_read_escape_inv fuel config environment incoming p initial address carriers final escaped

      | ref m p => exact builderSource_ref_escape_inv fuel config environment incoming m p initial address carriers final escaped

      | slice m v lo hi org => exact builderSource_slice_escape_inv fuel config environment incoming m v lo hi org initial address carriers final escaped

      | len v => exact builderSource_len_escape_inv fuel config environment incoming v initial address carriers final escaped

      | un op e org => exact builderSource_un_escape_inv fuel config environment incoming op e org initial address carriers final escaped

      | bin op a b org => exact builderSource_bin_escape_inv fuel config environment incoming op a b org initial address carriers final escaped

      | cmp op a b => exact builderSource_cmp_escape_inv fuel config environment incoming op a b initial address carriers final escaped

      | and a b => exact builderSource_and_escape_inv fuel config environment incoming a b initial address carriers final escaped

      | or a b => exact builderSource_or_escape_inv fuel config environment incoming a b initial address carriers final escaped

      | not e => exact builderSource_not_escape_inv fuel config environment incoming e initial address carriers final escaped

      | conv k target e org => exact builderSource_conv_escape_inv fuel config environment incoming k target e org initial address carriers final escaped

      | call c args org => exact builderSource_call_escape_inv fuel config environment incoming c args org initial address carriers final escaped

      | push owner e org => exact builderSource_push_escape_inv fuel config environment incoming owner e org initial address carriers final escaped

      | pop owner org => exact builderSource_pop_escape_inv fuel config environment incoming owner org initial address carriers final escaped

      | ifE c thenB elseB org => exact builderSource_ifE_escape_inv fuel config environment incoming c thenB elseB org initial address carriers final escaped

      | blockE b org => exact builderSource_blockE_escape_inv fuel config environment incoming b org initial address carriers final escaped

      | arrLit t es org => exact builderSource_arrLit_escape_inv fuel config environment incoming t es org initial address carriers final escaped

      | fill t e org => exact builderSource_fill_escape_inv fuel config environment incoming t e org initial address carriers final escaped

      | structLit t es => exact builderSource_structLit_escape_inv fuel config environment incoming t es initial address carriers final escaped

      | bytes t data org => exact builderSource_bytes_escape_inv fuel config environment incoming t data org initial address carriers final escaped

      | str t args org => exact builderSource_str_escape_inv fuel config environment incoming t args org initial address carriers final escaped

      | copy t source org => exact builderSource_copy_escape_inv fuel config environment incoming t source org initial address carriers final escaped

      | resultLocal var org => exact builderSource_resultLocal_escape_inv fuel config environment incoming var org initial address carriers final escaped

      | values operands => exact builderSource_values_escape_inv fuel config environment incoming operands initial address carriers final escaped

syntax "element_escape_steps " ident : tactic
macro_rules
  | `(tactic| element_escape_steps $escaped:ident) => `(tactic|
    repeat' first
      | element_escape_witness
      | (solve | producer_escape_native)
      | producer_escape_constructor $escaped:ident
      | simp only [bind, pure, fault, EvalM.stop] at $escaped:ident
      | producer_generalize_match $escaped:ident
      | split at $escaped:ident
      | producer_escape_refocus $escaped:ident)

theorem elementInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (parent : Nat) (element : Ty) (operand : Expr) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : buildElement fuel config environment parent element operand initial = .escape address carriers final) :
    ProducerInvocationCause config (.element fuel environment parent element operand) initial address carriers final := by
  unfold ProducerInvocationCause
  cases fuel with
  | zero => simp only [buildElement, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      simp only [buildElement, bind] at escaped
      element_escape_steps escaped

#print axioms produceInvocation_escape_inv
#print axioms buildInvocation_escape_inv
#print axioms elementInvocation_escape_inv

end Goose.Proofs.ExitExecution
