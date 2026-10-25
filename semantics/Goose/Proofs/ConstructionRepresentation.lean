import Goose.Construct.Validate
import Goose.Proofs.ConstructionExecutionOwnershipExecutionContext
import Goose.Proofs.ConstructionExecutionSourceOrder

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct
open Goose.Core (VarId GlobalId RootInst Loc)

inductive ValueRepresentation : Ty → Value → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : ValueRepresentation (.int ty) (.int ty value)
  | boolean (value : Bool) : ValueRepresentation .bool (.bool value)
  | unit : ValueRepresentation .unit .unit
  | reference (mutability : Goose.Core.Mutability) (ty : Ty) (location : Loc) :
      ValueRepresentation (.ref mutability ty) (.ref location)
  | slice (mutability : Goose.Core.Mutability) (ty : Ty) (location : Loc) (start count : Nat) :
      ValueRepresentation (.slice mutability ty) (.slice location start count)
  | array (element : Ty) (count : Nat) (values : Array Value)
      (inline : (Ty.arr element count).nonfixed = false)
      (length : values.size = count)
      (elements : ∀ value ∈ values.toList, ValueRepresentation element value) :
      ValueRepresentation (.arr element count) (.fixed values)
  | record (id : Goose.Core.StructId) (types : TyList) (values : Array Value)
      (length : values.size = types.toList.length)
      (fields : ∀ (index : Nat) (ty : Ty) (value : Value), types.toList[index]? = some ty →
        values[index]? = some value → ValueRepresentation ty value) :
      ValueRepresentation (.structT id types) (.record id values)
  | stored (ty : Ty) (value : StoredValue) (nonfixed : ty.nonfixed = true)
      (logicalType : value.ty = ty) : ValueRepresentation ty (.stored value)

def LocalRepresentations (state : ExecutionState) (environment : RuntimeActivation)
    (visible : List VarId) : Prop :=
  ∀ id ∈ visible, ∃ descriptor root value,
    environment.vars[id]? = some descriptor ∧
    rootOf environment id state = .ok root state ∧
    state.objects.lookup root = some value ∧ ValueRepresentation descriptor.ty value

def GlobalRepresentations (module : Module) (initialized : Nat) (state : ExecutionState) : Prop :=
  initialized ≤ module.globals.size ∧ ∀ global, global < initialized →
    ∃ descriptor value, module.globals[global]? = some descriptor ∧
      state.objects.lookup (.global global) = some value ∧ ValueRepresentation descriptor.ty value

structure AcceptedRepresentationState (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) : Prop where
  accepted : validate config.module = .ok ()
  ownership : Goose.Proofs.ConstructionExecutionOwnership.OwnershipExecutionContext state ambient
  globals : GlobalRepresentations config.module initialized state

structure AcceptedRepresentationInput (config : EvalConfig) (typing : TypingEnv)
    (environment : RuntimeActivation) (initialized : Nat) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) : Prop where
  execution : AcceptedRepresentationState config initialized state ambient
  module : typing.module = config.module
  variables : environment.vars = typing.variables
  globals : typing.globalLimit ≤ initialized
  locals : LocalRepresentations state environment typing.visible

theorem initial_acceptedRepresentationState (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    AcceptedRepresentationState config 0 .initial [] := by
  refine ⟨accepted, Goose.Proofs.ConstructionExecutionOwnership.initial_ownershipExecutionContext, ?_⟩
  exact ⟨Nat.zero_le _, fun global bound => (Nat.not_lt_zero global bound).elim⟩

theorem initial_acceptedRepresentationInput (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    AcceptedRepresentationInput config
      ⟨config.module, none, #[], [], 0, 0, .ordinary, .value, [], none, 0⟩
      ⟨0, 0, #[], [], []⟩ 0 .initial [] := by
  refine ⟨initial_acceptedRepresentationState config accepted, rfl, rfl, Nat.le_refl _, ?_⟩
  intro id present
  cases present

def ValueRepresentationOutcome (ty : Ty) : ExecutionStep Value → Prop
  | .ok value _ => ValueRepresentation ty value
  | .stop _ _ | .escape _ _ _ | .jump _ _ _ => True

theorem evalValue_integer_representation (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Goose.Core.IntTy) (value : Int) (state : ExecutionState) :
    evalValue (fuel + 1) config environment (.lit ty value) state = .ok (.int ty value) state ∧
      ValueRepresentationOutcome (.int ty)
        (evalValue (fuel + 1) config environment (.lit ty value) state) :=
  by
    simp only [evalValue, pure, ValueRepresentationOutcome]
    exact ⟨True.intro, ValueRepresentation.integer ty value⟩

theorem evalValue_boolean_representation (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (value : Bool) (state : ExecutionState) :
    evalValue (fuel + 1) config environment (.bool value) state = .ok (.bool value) state ∧
      ValueRepresentationOutcome .bool
        (evalValue (fuel + 1) config environment (.bool value) state) :=
  by
    simp only [evalValue, pure, ValueRepresentationOutcome]
    exact ⟨True.intro, ValueRepresentation.boolean value⟩

theorem evalValue_visibleLocal_representation (fuel : Nat) (config : EvalConfig)
    (typing : TypingEnv) (environment : RuntimeActivation) (initialized : Nat)
    (state : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (input : AcceptedRepresentationInput config typing environment initialized state ambient)
    (id : VarId) (visible : id ∈ typing.visible) :
    ∃ descriptor value, typing.variables[id]? = some descriptor ∧
      evalValue (fuel + 2) config environment (.read (.var id)) state = .ok value state ∧
      ValueRepresentation descriptor.ty value := by
  obtain ⟨descriptor, root, value, declared, resolved, found, represented⟩ := input.locals id visible
  refine ⟨descriptor, value, ?_, ?_, represented⟩
  · simpa only [input.variables] using declared
  · simp only [evalValue, evalPlace, bind, resolved, pure, readLoc, EvalM.get,
      found, readValuePath]

theorem evalValue_initializedGlobal_representation (fuel : Nat) (config : EvalConfig)
    (typing : TypingEnv) (environment : RuntimeActivation) (initialized : Nat)
    (state : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (input : AcceptedRepresentationInput config typing environment initialized state ambient)
    (id : GlobalId) (visible : id < typing.globalLimit) :
    ∃ descriptor value, config.module.globals[id]? = some descriptor ∧
      evalValue (fuel + 2) config environment (.read (.global id)) state = .ok value state ∧
      ValueRepresentation descriptor.ty value := by
  obtain ⟨descriptor, value, declared, found, represented⟩ :=
    input.execution.globals.2 id (Nat.lt_of_lt_of_le visible input.globals)
  refine ⟨descriptor, value, declared, ?_, represented⟩
  simp only [evalValue, evalPlace, bind, pure, readLoc, EvalM.get, found, readValuePath]

theorem mapM_representation (action : Expr → EvalM Value) (operands : List Expr) (ty : Ty)
    (invariant : ExecutionState → Prop)
    (represented : ∀ operand ∈ operands, ∀ before, invariant before → ∀ value after,
      action operand before = .ok value after → ValueRepresentation ty value ∧ invariant after)
    (initial final : ExecutionState) (valid : invariant initial) (values : List Value)
    (evaluated : operands.mapM action initial = .ok values final) :
    values.length = operands.length ∧ invariant final ∧
      ∀ value ∈ values, ValueRepresentation ty value := by
  have trace := Goose.Proofs.ConstructionExecution.listMapM_success_trace action operands initial values final evaluated
  have all : ∀ (rest : List Expr) (accumulator : List Value) (before : ExecutionState)
      (results : List Value) (after : ExecutionState),
      Goose.Proofs.ConstructionExecution.ListMapMLoopSuccess action rest accumulator before results after →
      (∀ operand ∈ rest, ∀ before, invariant before → ∀ value after,
        action operand before = .ok value after → ValueRepresentation ty value ∧ invariant after) →
      invariant before → (∀ value ∈ accumulator, ValueRepresentation ty value) →
      invariant after ∧ ∀ value ∈ results, ValueRepresentation ty value := by
    intro rest accumulator before results after trace
    induction trace with
    | nil accumulator state =>
        intro _ valid represented
        exact ⟨valid, fun value present => represented value (List.mem_reverse.mp present)⟩
    | @cons operand rest accumulator before middle after value values head tail ih =>
        intro represented valid accumulated
        have first := represented operand (List.mem_cons_self) before valid value middle head
        apply ih
        · intro operand present
          exact represented operand (List.mem_cons_of_mem _ present)
        · exact first.2
        · intro selected present
          rcases List.mem_cons.mp present with equal | present
          · subst selected; exact first.1
          · exact accumulated selected present
  exact ⟨Goose.Proofs.ConstructionExecution.listMapM_success_length action operands initial values final evaluated,
    all operands [] initial values final trace represented valid (by simp)⟩

theorem evalValue_fixedArray_representation (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (element : Ty) (count : Nat) (operands : List Expr)
    (origin : Goose.Core.OriginId) (inline : (Ty.arr element count).nonfixed = false)
    (length : operands.length = count) (invariant : ExecutionState → Prop)
    (represented : ∀ operand ∈ operands, ∀ before, invariant before → ∀ value after,
      evalValue fuel config environment operand before = .ok value after →
        ValueRepresentation element value ∧ invariant after)
    (initial final : ExecutionState) (valid : invariant initial) (value : Value)
    (evaluated : evalValue (fuel + 1) config environment (.arrLit (.arr element count) operands origin)
      initial = .ok value final) : ValueRepresentation (.arr element count) value ∧ invariant final := by
  simp only [evalValue, inline, Bool.false_eq_true, ↓reduceIte] at evaluated
  cases result : operands.mapM (evalValue fuel config environment) initial with
  | ok values after =>
      simp only [bind, result, pure] at evaluated
      cases evaluated
      have children := mapM_representation (evalValue fuel config environment) operands element invariant
        represented initial final valid values result
      exact ⟨.array element count values.toArray inline (by simpa [length] using children.1)
        (by simpa using children.2.2), children.2.1⟩
  | stop reason after | escape address carriers after | jump target kind after =>
      simp only [bind, result] at evaluated
      cases evaluated

theorem checkedFixedArray_length (fuel : Nat) (typing : TypingEnv) (element : Ty)
    (count : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (next final : Nat) (types : List Ty)
    (checked : typeExpr (fuel + 1) typing (.arrLit (.arr element count) operands origin) next =
      .ok (types, final)) : count = operands.length := by
  simp only [typeExpr] at checked
  cases constructible : (Ty.arr element count).constructible <;>
    cases equal : (count == operands.length) <;>
    simp_all [Ty.element?]
  all_goals cases checked

theorem evalValue_checkedFixedArray_representation (fuel typingFuel : Nat) (config : EvalConfig)
    (typing : TypingEnv) (environment : RuntimeActivation) (element : Ty) (count : Nat)
    (operands : List Expr) (origin : Goose.Core.OriginId) (next finalTyping : Nat) (types : List Ty)
    (checked : typeExpr (typingFuel + 1) typing (.arrLit (.arr element count) operands origin) next =
      .ok (types, finalTyping))
    (inline : (Ty.arr element count).nonfixed = false) (invariant : ExecutionState → Prop)
    (represented : ∀ operand ∈ operands, ∀ before, invariant before → ∀ value after,
      evalValue fuel config environment operand before = .ok value after →
        ValueRepresentation element value ∧ invariant after)
    (initial final : ExecutionState) (valid : invariant initial) (value : Value)
    (evaluated : evalValue (fuel + 1) config environment (.arrLit (.arr element count) operands origin)
      initial = .ok value final) : ValueRepresentation (.arr element count) value ∧ invariant final :=
  evalValue_fixedArray_representation fuel config environment element count operands origin inline
    (checkedFixedArray_length typingFuel typing element count operands origin next finalTyping types checked).symm
    invariant represented initial final valid value evaluated

theorem evalValue_fixedFill_representation (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (element : Ty) (count : Nat) (operand : Expr)
    (origin : Goose.Core.OriginId) (inline : (Ty.arr element count).nonfixed = false)
    (invariant : ExecutionState → Prop)
    (represented : ∀ before, invariant before → ∀ value after,
      evalValue fuel config environment operand before = .ok value after →
        ValueRepresentation element value ∧ invariant after)
    (initial final : ExecutionState) (valid : invariant initial) (value : Value)
    (evaluated : evalValue (fuel + 1) config environment (.fill (.arr element count) operand origin)
      initial = .ok value final) : ValueRepresentation (.arr element count) value ∧ invariant final := by
  simp only [evalValue, inline, Bool.false_eq_true, ↓reduceIte] at evaluated
  cases result : evalValue fuel config environment operand initial with
  | ok source after =>
      simp only [bind, result, pure] at evaluated
      cases evaluated
      have sourceValid := represented initial valid source final result
      refine ⟨ValueRepresentation.array element count (Array.replicate count source) inline (by simp) ?_, sourceValid.2⟩
      intro selected member
      have same : selected = source := by simpa using List.eq_of_mem_replicate member
      subst selected
      exact sourceValid.1
  | stop reason after | escape address carriers after | jump target kind after =>
      simp only [bind, result] at evaluated
      cases evaluated

inductive FixedInitializer : Nat → Ty → Expr → Prop
  | integer (fuel : Nat) (ty : Goose.Core.IntTy) (value : Int) :
      FixedInitializer (fuel + 1) (.int ty) (.lit ty value)
  | boolean (fuel : Nat) (value : Bool) :
      FixedInitializer (fuel + 1) .bool (.bool value)
  | array (fuel : Nat) (element : Ty) (operands : List Expr) (origin : Goose.Core.OriginId)
      (inline : (Ty.arr element operands.length).nonfixed = false)
      (children : ∀ operand ∈ operands, FixedInitializer fuel element operand) :
      FixedInitializer (fuel + 1) (.arr element operands.length)
        (.arrLit (.arr element operands.length) operands origin)
  | fill (fuel : Nat) (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (inline : (Ty.arr element count).nonfixed = false)
      (source : FixedInitializer fuel element operand) :
      FixedInitializer (fuel + 1) (.arr element count) (.fill (.arr element count) operand origin)

private theorem mapM_fixed_initializers (action : Expr → EvalM Value) (operands : List Expr) (ty : Ty)
    (represented : ∀ operand ∈ operands, ∀ state,
      ∃ value, action operand state = .ok value state ∧ ValueRepresentation ty value)
    (state : ExecutionState) :
    ∃ values, operands.mapM action state = .ok values state ∧
      values.length = operands.length ∧ ∀ value ∈ values, ValueRepresentation ty value := by
  induction operands with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons operand rest ih =>
      obtain ⟨value, head, shape⟩ := represented operand (List.mem_cons_self) state
      obtain ⟨values, tail, length, shapes⟩ := ih
        (fun item present => represented item (List.mem_cons_of_mem _ present))
      refine ⟨value :: values, ?_, by simp [length], ?_⟩
      · simp [List.mapM_cons, bind, head, tail, pure]
      · intro selected present
        rcases List.mem_cons.mp present with equal | present
        · subst selected; exact shape
        · exact shapes selected present

theorem fixedInitializer_evaluation {fuel : Nat} {ty : Ty} {expression : Expr}
    (initializer : FixedInitializer fuel ty expression) (config : EvalConfig)
    (environment : RuntimeActivation) (state : ExecutionState) :
    ∃ value, evalValue fuel config environment expression state = .ok value state ∧
      ValueRepresentation ty value := by
  induction initializer generalizing state with
  | integer fuel ty value =>
      exact ⟨.int ty value, (evalValue_integer_representation fuel config environment ty value state).1,
        .integer ty value⟩
  | boolean fuel value =>
      exact ⟨.bool value, (evalValue_boolean_representation fuel config environment value state).1,
        .boolean value⟩
  | array fuel element operands origin inline children ih =>
      obtain ⟨values, evaluated, length, shapes⟩ := mapM_fixed_initializers
        (evalValue fuel config environment) operands element ih state
      refine ⟨.fixed values.toArray, ?_, .array element operands.length values.toArray inline
        (by simpa using length) (by simpa using shapes)⟩
      simp [evalValue, inline, bind, evaluated, pure]
  | fill fuel element count operand origin inline source ih =>
      obtain ⟨value, evaluated, shape⟩ := ih state
      refine ⟨.fixed (Array.replicate count value), ?_, .array element count
        (Array.replicate count value) inline (by simp) ?_⟩
      · simp [evalValue, inline, bind, evaluated, pure]
      · intro selected present
        have equal : selected = value := by simpa using List.eq_of_mem_replicate present
        subst selected
        exact shape

theorem fixedInitializer_produce {fuel : Nat} {ty : Ty} {expression : Expr}
    (initializer : FixedInitializer fuel ty expression) (config : EvalConfig)
    (environment : RuntimeActivation) (state : ExecutionState) :
    ∃ value, evalProduce (fuel + 1) config environment [.register ty] expression state =
      .ok [.register value] state ∧ ValueRepresentation ty value := by
  obtain ⟨value, evaluated, represented⟩ := fixedInitializer_evaluation initializer config environment state
  refine ⟨value, ?_, represented⟩
  cases initializer <;>
    simp [evalProduce, List.mapM_cons, List.mapM_nil, selectCompletionChannel,
      bind, pure, evaluated]

#print axioms fixedInitializer_produce
#print axioms initial_acceptedRepresentationInput
#print axioms fixedInitializer_evaluation
#print axioms checkedFixedArray_length
#print axioms evalValue_checkedFixedArray_representation
#print axioms initial_acceptedRepresentationState
#print axioms evalValue_integer_representation
#print axioms evalValue_boolean_representation
#print axioms evalValue_visibleLocal_representation
#print axioms evalValue_initializedGlobal_representation
#print axioms mapM_representation
#print axioms evalValue_fixedArray_representation
#print axioms evalValue_fixedFill_representation

end Goose.Proofs.ConstructionRepresentation
