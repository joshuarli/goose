import Goose.Proofs.ExitExecutionInvocation
import Goose.Proofs.ExitExecutionActivationChannelsHelpers

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

inductive ValueInvocationEdge (config : EvalConfig) :
    {α β : Type} → ExitInvocation α → ExecutionState → ExitInvocation β → ExecutionState → Prop
  | valueRead :
      ValueInvocationEdge config (.value (fuel + 1) environment (.read place)) initial (.place fuel environment place) initial
  | valueRef :
      ValueInvocationEdge config (.value (fuel + 1) environment (.ref ty place)) initial (.place fuel environment place) initial
  | valueSliceView :
      ValueInvocationEdge config (.value (fuel + 1) environment (.slice ty view lo hi origin)) initial (.view fuel environment view) initial
  | valueLength :
      ValueInvocationEdge config (.value (fuel + 1) environment (.len view)) initial (.view fuel environment view) initial
  | valueUnary :
      ValueInvocationEdge config (.value (fuel + 1) environment (.un operation operand origin)) initial (.value fuel environment operand) initial
  | valueBinaryFirst :
      ValueInvocationEdge config (.value (fuel + 1) environment (.bin operation first second origin)) initial (.value fuel environment first) initial
  | valueCompareFirst :
      ValueInvocationEdge config (.value (fuel + 1) environment (.cmp operation first second)) initial (.value fuel environment first) initial
  | valueAndFirst :
      ValueInvocationEdge config (.value (fuel + 1) environment (.and first second)) initial (.value fuel environment first) initial
  | valueOrFirst :
      ValueInvocationEdge config (.value (fuel + 1) environment (.or first second)) initial (.value fuel environment first) initial
  | valueNot :
      ValueInvocationEdge config (.value (fuel + 1) environment (.not operand)) initial (.value fuel environment operand) initial
  | valueConvert :
      ValueInvocationEdge config (.value (fuel + 1) environment (.conv kind target operand origin)) initial (.value fuel environment operand) initial
  | valuePush :
      ValueInvocationEdge config (.value (fuel + 1) environment (.push owner operand origin)) initial (.push fuel environment owner operand (origin.getD 0)) initial
  | valuePop :
      ValueInvocationEdge config (.value (fuel + 1) environment (.pop owner origin)) initial (.place fuel environment owner) initial
  | valueIfCondition :
      ValueInvocationEdge config (.value (fuel + 1) environment (.ifE condition yes no origin)) initial (.value fuel environment condition) initial
  | valueValues :
      ValueInvocationEdge config (.value (fuel + 1) environment (.values [operand])) initial (.value fuel environment operand) initial
  | boundExpr :
      ValueInvocationEdge config (.bound (fuel + 1) environment count defaultValue (.expr operand)) initial (.value fuel environment operand) initial
  | boundFromEnd :
      ValueInvocationEdge config (.bound (fuel + 1) environment count defaultValue (.fromEnd operand)) initial (.value fuel environment operand) initial
  | placeDeref :
      ValueInvocationEdge config (.place (fuel + 1) environment (.deref operand)) initial (.value fuel environment operand) initial
  | placeElementView :
      ValueInvocationEdge config (.place (fuel + 1) environment (.elem view operand origin)) initial (.view fuel environment view) initial
  | placeField :
      ValueInvocationEdge config (.place (fuel + 1) environment (.field owner index)) initial (.place fuel environment owner) initial
  | viewOf :
      ValueInvocationEdge config (.view (fuel + 1) environment (.of place)) initial (.place fuel environment place) initial
  | viewValue :
      ValueInvocationEdge config (.view (fuel + 1) environment (.val operand)) initial (.value fuel environment operand) initial
  | printValue :
      ValueInvocationEdge config (.printArgument (fuel + 1) environment (.expr expression)) initial (.value fuel environment expression) initial
  | printView :
      ValueInvocationEdge config (.printArgument (fuel + 1) environment (.view view)) initial (.view fuel environment view) initial
  | valueSliceLow (evaluated : evalView fuel config environment view initial = .ok runtimeView prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.slice ty view lo hi origin)) initial (.bound fuel environment runtimeView.count 0 lo) prepared
  | valueSliceHigh (viewDone : evalView fuel config environment view initial = .ok runtimeView viewState)
      (lowDone : evalBound fuel config environment runtimeView.count 0 lo viewState = .ok low prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.slice ty view lo hi origin)) initial (.bound fuel environment runtimeView.count runtimeView.count hi) prepared
  | valueBinarySecond (firstDone : evalValue fuel config environment first initial = .ok value firstState)
      (integer : expectInt value firstState = .ok pair prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.bin operation first second origin)) initial (.value fuel environment second) prepared
  | valueCompareSecond (firstDone : evalValue fuel config environment first initial = .ok value prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.cmp operation first second)) initial (.value fuel environment second) prepared
  | valueAndSecond (firstDone : evalValue fuel config environment first initial = .ok value firstState)
      (boolean : expectBool value firstState = .ok true prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.and first second)) initial (.value fuel environment second) prepared
  | valueOrSecond (firstDone : evalValue fuel config environment first initial = .ok value firstState)
      (boolean : expectBool value firstState = .ok false prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.or first second)) initial (.value fuel environment second) prepared
  | valueIfYes (conditionDone : evalValue fuel config environment condition initial = .ok value conditionState)
      (boolean : expectBool value conditionState = .ok true prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.ifE condition yes no origin)) initial (.block fuel environment [] [] yes) prepared
  | valueIfNo (conditionDone : evalValue fuel config environment condition initial = .ok value conditionState)
      (boolean : expectBool value conditionState = .ok false prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.ifE condition yes no origin)) initial (.block fuel environment [] [] no) prepared
  | placeElementIndex (viewDone : evalView fuel config environment view initial = .ok runtimeView prepared) :
      ValueInvocationEdge config (.place (fuel + 1) environment (.elem view operand origin)) initial (.value fuel environment operand) prepared
  | valueCall (lookup : getImplementation config context initial = .ok (implementationId, implementation) lookupState)
      (receiving : channelsFor config.layout environment.act implementation.results.toList origin lookupState = .ok channels prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.call context arguments origin)) initial (.call fuel environment context arguments channels origin) prepared
  | valueBlockProduce (typesFound : blockResultTypes? (max fuel (blockQueryBudget body)) ⟨config.module, environment.vars⟩ body = some types)
      (receiving : channelsFor config.layout environment.act
        (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin initial = .ok channels prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.blockE body origin)) initial (.produce fuel environment channels (.blockE body origin)) prepared
  | valueArrayBuild (nonfixed : ty.nonfixed = true)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands origin)) initial = .ok destination prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.arrLit ty operands origin)) initial (.build fuel environment destination (.arrLit ty operands origin)) prepared
  | valueFillBuild (nonfixed : (Ty.arr element count).nonfixed = true)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act (.arr element count) .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.fill (.arr element count) operand origin)) initial = .ok destination prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.fill (.arr element count) operand origin)) initial (.build fuel environment destination (.fill (.arr element count) operand origin)) prepared
  | valueBytesBuild (notSlice : ∀ element, ty ≠ .slice element (.int .u8))
      (nonfixed : ty.nonfixed = true)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.bytes ty bytes origin)) initial = .ok destination prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.bytes ty bytes origin)) initial (.build fuel environment destination (.bytes ty bytes origin)) prepared
  | valueStringBuild
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.str ty text origin)) initial = .ok destination prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.str ty text origin)) initial (.build fuel environment destination (.str ty text origin)) prepared
  | valueCopyBuild (nonfixed : ty.nonfixed = true)
      (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
        (producerCount? ⟨config.module, environment.vars⟩ (.copy ty source origin)) initial = .ok destination prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.copy ty source origin)) initial (.build fuel environment destination (.copy ty source origin)) prepared
  | valueCopyPlace (fixed : ty.nonfixed = false) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.copy ty source origin)) initial (.place fuel environment source) initial
  | valueFillOperand (fixed : (Ty.arr element count).nonfixed = false) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.fill (.arr element count) operand origin)) initial (.value fuel environment operand) initial
  | valueArrayOperand (fixed : ty.nonfixed = false)
      (prefixDone : earlier.mapM (evalValue fuel config environment) initial = .ok values prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.arrLit ty (earlier ++ operand :: rest) origin)) initial (.value fuel environment operand) prepared
  | valueStructOperand
      (prefixDone : earlier.mapM (evalValue fuel config environment) initial = .ok values prepared) :
      ValueInvocationEdge config (.value (fuel + 1) environment (.structLit (.structT structId fields) (earlier ++ operand :: rest))) initial (.value fuel environment operand) prepared

private theorem valueEdgeFreshNormal (action : EvalM α) (initial final : ExecutionState) (value : α)
    (normal : action initial = .ok value final) (fresh : FreshActivations initial)
    (preserved : PreservesFresh action) : FreshActivations final := by
  have after := preserved initial fresh
  simpa only [normal, Goose.Proofs.Exit.stepState] using after

theorem ValueInvocationEdge.fresh {config : EvalConfig}
    (previous : ∀ fuel, EvaluationPreservesFresh fuel config)
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (edge : ValueInvocationEdge config parent initial child prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases edge
  all_goals try first
    | exact fresh
    | (apply valueEdgeFreshNormal _ _ _ _ (by assumption) fresh
       exact (previous _).view _ _)
    | (apply valueEdgeFreshNormal _ _ _ _ (by assumption) fresh
       exact (previous _).value _ _)
    | (apply valueEdgeFreshNormal _ _ _ _ (by assumption) fresh
       exact preservesFresh_channelsFor _ _ _ _)
    | (apply valueEdgeFreshNormal _ _ _ _ (by assumption) fresh
       exact preservesFresh_newDestination _ _ _ _ _ _ _)
    | (apply valueEdgeFreshNormal _ _ _ _ (by assumption) fresh
       exact preservesFresh_listMapM _ _ (fun _ => (previous _).value _ _))
  case valueSliceHigh =>
    apply valueEdgeFreshNormal _ _ _ _ (by assumption)
    · exact valueEdgeFreshNormal _ _ _ _ (by assumption) fresh ((previous _).view _ _)
    · exact (previous _).bound _ _ _ _
  case valueBinarySecond =>
    apply valueEdgeFreshNormal _ _ _ _ (by assumption)
    · exact valueEdgeFreshNormal _ _ _ _ (by assumption) fresh ((previous _).value _ _)
    · exact stateQuery_preservesFresh _ (stateQuery_expectInt _)
  case valueAndSecond | valueOrSecond | valueIfYes | valueIfNo =>
    apply valueEdgeFreshNormal _ _ _ _ (by assumption)
    · exact valueEdgeFreshNormal _ _ _ _ (by assumption) fresh ((previous _).value _ _)
    · exact stateQuery_preservesFresh _ (stateQuery_expectBool _)
  case valueCall =>
    apply valueEdgeFreshNormal _ _ _ _ (by assumption)
    · exact valueEdgeFreshNormal _ _ _ _ (by assumption) fresh
        (stateQuery_preservesFresh _ (stateQuery_getImplementation _ _))
    · exact preservesFresh_channelsFor _ _ _ _

private def ValuePrefixInvariant (initial prepared : ExecutionState) : Prop :=
  ∀ _fresh : FreshActivations initial,
    FreshActivations prepared ∧ ActivationChannelsProjection prepared = ActivationChannelsProjection initial

private theorem valuePrefixInvariant_refl (state : ExecutionState) : ValuePrefixInvariant state state :=
  fun fresh => ⟨fresh, rfl⟩

private theorem valuePrefixInvariant_trans {first middle last : ExecutionState}
    (head : ValuePrefixInvariant first middle) (tail : ValuePrefixInvariant middle last) :
    ValuePrefixInvariant first last := by
  intro fresh
  obtain ⟨middleFresh, middleProjection⟩ := head fresh
  obtain ⟨lastFresh, lastProjection⟩ := tail middleFresh
  exact ⟨lastFresh, lastProjection.trans middleProjection⟩

private theorem valuePrefixInvariant_normal (action : EvalM α) (initial final : ExecutionState) (value : α)
    (normal : action initial = .ok value final) (freshness : PreservesFresh action)
    (channels : PreservesActivationChannels action) : ValuePrefixInvariant initial final := by
  intro fresh
  refine ⟨valueEdgeFreshNormal _ _ _ _ normal fresh freshness, ?_⟩
  have after := channels initial fresh
  simpa only [normal, ActivationChannelsOutcome] using after

theorem ValueInvocationEdge.transport {config : EvalConfig}
    (previousFresh : ∀ fuel, EvaluationPreservesFresh fuel config)
    (previous : ∀ fuel, EvaluationActivationChannels fuel config)
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (edge : ValueInvocationEdge config parent initial child prepared)
    (fresh : FreshActivations initial) :
    FreshActivations prepared ∧ ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  suffices ValuePrefixInvariant initial prepared from this fresh
  cases edge
  all_goals try first
    | exact valuePrefixInvariant_refl _
    | (apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
       · exact (previousFresh _).view _ _
       · exact (previous _).view _ _)
    | (apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
       · exact (previousFresh _).value _ _
       · exact (previous _).value _ _)
    | (apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
       · exact preservesFresh_channelsFor _ _ _ _
       · exact preservesActivationChannels_channelsFor _ _ _ _)
    | (apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
       · exact preservesFresh_newDestination _ _ _ _ _ _ _
       · exact preservesActivationChannels_newDestination _ _ _ _ _ _ _)
    | (apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
       · exact preservesFresh_listMapM _ _ (fun _ => (previousFresh _).value _ _)
       · exact preservesActivationChannels_listMapM _ _ (fun _ => (previous _).value _ _)
           (fun _ => (previousFresh _).value _ _))
  case valueSliceHigh =>
    apply valuePrefixInvariant_trans
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact (previousFresh _).view _ _
      · exact (previous _).view _ _
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact (previousFresh _).bound _ _ _ _
      · exact (previous _).bound _ _ _ _
  case valueBinarySecond =>
    apply valuePrefixInvariant_trans
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact (previousFresh _).value _ _
      · exact (previous _).value _ _
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact stateQuery_preservesFresh _ (stateQuery_expectInt _)
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectInt _)
  case valueAndSecond | valueOrSecond | valueIfYes | valueIfNo =>
    apply valuePrefixInvariant_trans
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact (previousFresh _).value _ _
      · exact (previous _).value _ _
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact stateQuery_preservesFresh _ (stateQuery_expectBool _)
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_expectBool _)
  case valueCall =>
    apply valuePrefixInvariant_trans
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact stateQuery_preservesFresh _ (stateQuery_getImplementation _ _)
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getImplementation _ _)
    · apply valuePrefixInvariant_normal _ _ _ _ (by assumption)
      · exact preservesFresh_channelsFor _ _ _ _
      · exact preservesActivationChannels_channelsFor _ _ _ _

theorem ValueInvocationEdge.escape {config : EvalConfig}
    {parent : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (edge : ValueInvocationEdge config parent initial child prepared)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : child.action config prepared = .escape address carriers final) :
    parent.action config initial = .escape address carriers final := by
  cases edge
  all_goals simp only [ExitInvocation.action] at escaped ⊢
  all_goals simp_all [evalValue, evalBound, evalPlace, evalView, evalPrintArg, constructLocal,
    bind, List.mapM_append]

theorem valueMapM_escape (action : α → EvalM β) (items : List α)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : items.mapM action initial = .escape address carriers final) :
    ∃ earlier item rest values prepared,
      items = earlier ++ item :: rest ∧
      earlier.mapM action initial = .ok values prepared ∧
      action item prepared = .escape address carriers final := by
  induction items generalizing initial with
  | nil => cases escaped
  | cons item rest ih =>
    simp only [List.mapM_cons, bind] at escaped
    cases head : action item initial with
    | stop reason state => simp only [head] at escaped; cases escaped
    | jump target kind state => simp only [head] at escaped; cases escaped
    | escape target values state =>
      simp only [head] at escaped
      cases escaped
      exact ⟨[], item, rest, [], initial, rfl, rfl, head⟩
    | ok value middle =>
      simp only [head] at escaped
      cases tail : rest.mapM action middle with
      | stop reason state => simp only [tail] at escaped; cases escaped
      | jump target kind state => simp only [tail] at escaped; cases escaped
      | ok values state => simp only [tail, pure] at escaped; cases escaped
      | escape target values state =>
        simp only [tail] at escaped
        cases escaped
        obtain ⟨earlier, child, remaining, values, prepared, decomposition, prefixDone, childEscape⟩ := ih middle tail
        refine ⟨item :: earlier, child, remaining, value :: values, prepared, ?_, ?_, childEscape⟩
        · simp only [List.cons_append, decomposition]
        · simp only [List.mapM_cons, bind, head, prefixDone, pure]

end Goose.Proofs.ExitExecution
