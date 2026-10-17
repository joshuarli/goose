import Goose.Proofs.ExitExecutionInvocationValues
import Goose.Proofs.ExitExecutionInvocationValuesNative
import Goose.Proofs.ExitExecutionArgumentOrigins

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def ValueInvocationCause (config : EvalConfig) (parent : ExitInvocation α) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState) : Prop :=
  ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
    ValueInvocationEdge config parent initial child prepared ∧
    child.action config prepared = .escape address carriers final

private theorem valueBooleanPrefix_true (value : Value) (initial prepared : ExecutionState) (observed : Bool)
    (evaluated : expectBool value initial = .ok observed prepared) (truth : observed = true) :
    expectBool value initial = .ok true prepared := by simpa only [truth] using evaluated

private theorem valueBooleanPrefix_false (value : Value) (initial prepared : ExecutionState) (observed : Bool)
    (evaluated : expectBool value initial = .ok observed prepared) (truth : observed ≠ true) :
    expectBool value initial = .ok false prepared := by
  cases observed <;> simp_all

private theorem valueBytesBuildCause (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
    (destination : Nat) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ (.bytes ty bytes origin)) initial = .ok destination prepared)
    (childEscape : buildExpr fuel config environment destination (.bytes ty bytes origin) prepared = .escape address carriers final)
    (notSlice : ∀ element, ty ≠ .slice element (.int .u8)) (nonfixed : ty.nonfixed = true) :
    ValueInvocationCause config (.value (fuel + 1) environment (.bytes ty bytes origin)) initial address carriers final := by
  exact ⟨Unit, .build fuel environment destination (.bytes ty bytes origin), prepared,
    .valueBytesBuild notSlice nonfixed allocation, childEscape⟩

macro "value_escape_witness" : tactic => `(tactic|
  first
    | (refine ⟨_, _, _, .valueRead , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueRef , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueSliceView , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueLength , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueUnary , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueBinaryFirst , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueCompareFirst , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueAndFirst , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueOrFirst , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueNot , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueConvert , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valuePush , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valuePop , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueIfCondition , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueValues , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .boundExpr , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .boundFromEnd , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .placeDeref , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .placeElementView , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .placeField , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .viewOf , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .viewValue , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .printValue , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .printView , ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueSliceLow (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueSliceHigh (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueBinarySecond (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueCompareSecond (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueAndSecond (by assumption) (valueBooleanPrefix_true _ _ _ _ (by assumption) (by assumption)), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueOrSecond (by assumption) (valueBooleanPrefix_false _ _ _ _ (by assumption) (by assumption)), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueIfYes (by assumption) (valueBooleanPrefix_true _ _ _ _ (by assumption) (by assumption)), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueIfNo (by assumption) (valueBooleanPrefix_false _ _ _ _ (by assumption) (by assumption)), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .placeElementIndex (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueCall (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueBlockProduce (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueArrayBuild (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueFillBuild (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueStringBuild (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueCopyBuild (by assumption) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueCopyPlace (by simp_all only [Bool.not_eq_true]), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueFillOperand (by simp_all only [Bool.not_eq_true]), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueArrayOperand (by simp_all only [Bool.not_eq_true]) (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption)
    | (refine ⟨_, _, _, .valueStructOperand (by assumption), ?_⟩; simp only [ExitInvocation.action]; assumption))

macro "value_escape_native" : tactic => `(tactic|
  simp_all only [producerNeverEscapes_pure, producerNeverEscapes_get, producerNeverEscapes_set, producerNeverEscapes_fault, producerNeverEscapes_timeout, producerNeverEscapes_liftConstruction, producerNeverEscapes_liftLayout, producerNeverEscapes_liftExcept, producerNeverEscapes_readLoc, producerNeverEscapes_readStoredElement, valueNeverEscapes_readStoredElements, producerNeverEscapes_sampledStored, producerNeverEscapes_rootOf, producerNeverEscapes_getStorage, producerNeverEscapes_newDestination, producerNeverEscapes_completedReceivingDestination, producerNeverEscapes_carrierValue, producerNeverEscapes_singleCarrier, valueNeverEscapes_expectInt, valueNeverEscapes_expectBool, valueNeverEscapes_expectRef, valueNeverEscapes_sameIntType, valueNeverEscapes_comparable, valueNeverEscapes_freshScope, valueNeverEscapes_bindRoot, valueNeverEscapes_bindStaticRoot, valueNeverEscapes_arrayLength, valueNeverEscapes_getImplementation, valueNeverEscapes_channelsFor, valueNeverEscapes_publishCarriers, valueNeverEscapes_truncateOwner, valueNeverEscapes_renderAny, valueNeverEscapes_renderView])

macro "value_escape_mapped" : tactic => `(tactic|
  (obtain ⟨earlier, item, rest, values, prepared, decomposition, prefixDone, childEscape⟩ :=
    valueMapM_escape _ _ _ _ _ _ (by assumption)
   cases decomposition
   value_escape_witness))

elab "value_escape_construct" : tactic => Lean.Elab.Tactic.withMainContext do
  for declaration in (← Lean.getLCtx) do
    let type ← Lean.instantiateMVars declaration.type
    if type.getAppFn.isConstOf ``Eq then
      let arguments := type.getAppArgs
      if arguments[1]!.getAppFn.isConstOf ``constructLocal && arguments[2]!.getAppFn.isConstOf ``ExecutionStep.escape then
        let source ← Lean.PrettyPrinter.delab (Lean.mkFVar declaration.fvarId)
        if arguments[1]!.getAppArgs[4]!.getAppFn.isConstOf ``Expr.bytes then
          Lean.Elab.Tactic.evalTactic (← `(tactic|
            obtain ⟨destination, prepared, allocation, childEscape⟩ :=
              (constructLocal_escape_call _ _ _ _ _ _ _ _ _ _ $source);
            exact valueBytesBuildCause _ _ _ _ _ _ _ _ _ _ _ _ allocation childEscape (by assumption) (by assumption)))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic|
            obtain ⟨destination, prepared, allocation, childEscape⟩ :=
              (constructLocal_escape_call _ _ _ _ _ _ _ _ _ _ $source);
            value_escape_witness))
        return
  throwError "no native local-construction escape"

elab "value_escape_constructor " hypothesis:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let hypothesisId ← Lean.Elab.Tactic.getFVarId hypothesis
  let declaration ← hypothesisId.getDecl
  let type ← Lean.instantiateMVars declaration.type
  unless type.getAppFn.isConstOf ``Eq do throwError "expected equality"
  let left := type.getAppArgs[1]!
  unless [``ExecutionStep.ok, ``ExecutionStep.stop, ``ExecutionStep.escape, ``ExecutionStep.jump].any left.getAppFn.isConstOf do
    throwError "expected execution constructor"
  Lean.Elab.Tactic.evalTactic (← `(tactic| cases $hypothesis:ident))

syntax "value_escape_steps " ident : tactic
macro_rules
  | `(tactic| value_escape_steps $escaped:ident) => `(tactic|
  repeat' first
    | value_escape_witness
    | (solve | value_escape_construct)
    | (solve | value_escape_native)
    | value_escape_constructor $escaped:ident
    | split at $escaped:ident
    | simp only [bind, pure, abortAt, fault, EvalM.stop] at $escaped:ident)

theorem boundInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalBound fuel config environment count defaultValue operand initial = .escape address carriers final) :
    ValueInvocationCause config (.bound fuel environment count defaultValue operand) initial address carriers final := by
  unfold ValueInvocationCause
  cases fuel with
  | zero => simp only [evalBound, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases operand <;> simp only [evalBound, bind] at escaped
    all_goals value_escape_steps escaped

theorem placeInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : Place) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalPlace fuel config environment operand initial = .escape address carriers final) :
    ValueInvocationCause config (.place fuel environment operand) initial address carriers final := by
  unfold ValueInvocationCause
  cases fuel with
  | zero => simp only [evalPlace, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases operand <;> simp only [evalPlace, bind] at escaped
    all_goals value_escape_steps escaped

theorem viewInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : View) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalView fuel config environment operand initial = .escape address carriers final) :
    ValueInvocationCause config (.view fuel environment operand) initial address carriers final := by
  unfold ValueInvocationCause
  cases fuel with
  | zero => simp only [evalView, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases operand <;> simp only [evalView, bind] at escaped
    all_goals value_escape_steps escaped

theorem printInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operand : PrintArg) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalPrintArg fuel config environment operand initial = .escape address carriers final) :
    ValueInvocationCause config (.printArgument fuel environment operand) initial address carriers final := by
  unfold ValueInvocationCause
  cases fuel with
  | zero => simp only [evalPrintArg, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases operand <;> simp only [evalPrintArg, bind] at escaped
    all_goals value_escape_steps escaped

private theorem valueInvocation_lit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.lit ty number) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.lit ty number)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  cases escaped

private theorem valueInvocation_bool_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.bool boolean) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.bool boolean)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  cases escaped

private theorem valueInvocation_read_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.read place) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.read place)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_ref_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.ref ty place) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.ref ty place)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_slice_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.slice ty view lo hi origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.slice ty view lo hi origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_len_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.len view) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.len view)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_un_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.un operation operand origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.un operation operand origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped
  all_goals exact False.elim (valueNeverEscapes_numericResult _ _ _ _ _ _ _ (by assumption))

private theorem valueInvocation_bin_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.bin operation first second origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.bin operation first second origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped
  all_goals exact False.elim (valueNeverEscapes_numericResult _ _ _ _ _ _ _ (by assumption))

private theorem valueInvocation_cmp_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.cmp operation first second) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.cmp operation first second)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_and_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.and first second) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.and first second)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_or_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.or first second) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.or first second)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_not_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.not operand) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.not operand)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_conv_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.conv kind target operand origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.conv kind target operand origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped
  all_goals exact False.elim (valueNeverEscapes_numericResult _ _ _ _ _ _ _ (by assumption))

private theorem valueInvocation_call_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.call context arguments origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.call context arguments origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_push_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.push owner operand origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.push owner operand origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  value_escape_steps escaped

private theorem valueInvocation_pop_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.pop owner origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.pop owner origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_ifE_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.ifE condition yes no origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.ifE condition yes no origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_blockE_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.blockE body origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.blockE body origin)) initial address carriers final := by
  unfold ValueInvocationCause
  cases typesFound : blockResultTypes? (max fuel (blockQueryBudget body)) ⟨config.module, environment.vars⟩ body with
  | none =>
    simp only [evalValue, typesFound, fault, EvalM.stop] at escaped
    cases escaped
  | some types =>
    simp only [evalValue, typesFound, bind] at escaped
    value_escape_steps escaped

private theorem valueInvocation_arrLit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.arrLit ty operands origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.arrLit ty operands origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped
  all_goals value_escape_mapped

private theorem valueInvocation_fill_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.fill ty operand origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.fill ty operand origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_structLit_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.structLit ty operands) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.structLit ty operands)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped
  all_goals value_escape_mapped

private theorem valueInvocation_bytes_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.bytes ty bytes origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.bytes ty bytes origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_str_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.str ty text origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.str ty text origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_copy_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.copy ty source origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.copy ty source origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_resultLocal_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.resultLocal localVar origin) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.resultLocal localVar origin)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  try simp only [bind] at escaped
  value_escape_steps escaped

private theorem valueInvocation_values_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue (fuel + 1) config environment (.values operands) initial = .escape address carriers final) :
    ValueInvocationCause config (.value (fuel + 1) environment (.values operands)) initial address carriers final := by
  unfold ValueInvocationCause
  unfold evalValue at escaped
  value_escape_steps escaped

theorem valueInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (initial : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (escaped : evalValue fuel config environment expression initial = .escape address carriers final) :
    ValueInvocationCause config (.value fuel environment expression) initial address carriers final := by
  cases fuel with
  | zero => simp only [evalValue, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
    cases expression
    all_goals first
      | exact valueInvocation_lit_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_bool_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_read_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_ref_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_slice_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_len_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_un_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_bin_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_cmp_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_and_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_or_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_not_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_conv_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_call_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_push_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_pop_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_ifE_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_blockE_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_arrLit_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_fill_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_structLit_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_bytes_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_str_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_copy_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_resultLocal_escape_inv fuel config environment initial address carriers final escaped
      | exact valueInvocation_values_escape_inv fuel config environment initial address carriers final escaped

end Goose.Proofs.ExitExecution
