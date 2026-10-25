import Goose.GIR.ReplacementContentFlow
import Goose.GIR.Validate

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem checkInstruction_definition_of_native {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {state : State} {value : ValueId} {op : Op}
    (native : checkInstTypes func { module.tyEnv func with vals := types } types (.def value op) = .ok ())
    (ready : refReady types state (.def value op) = true)
    (calls : ∀ fn args origin, op = .call fn args origin → checkCall module func state fn args = true) :
    checkInstruction module func types state (.def value op) = true := by
  cases result : op.resultTy { module.tyEnv func with vals := types } with
  | error message => simp [checkInstTypes, result, bind, Except.bind, pure, Except.pure, tyErr] at native
  | ok type =>
    have row : (types[value]? == some (some type)) = true := by
      simpa [checkInstTypes, result, bind, Except.bind, pure, Except.pure] using native
    cases op <;> simp_all [checkInstruction, Except.toOption]

theorem checkInstruction_effect_of_native {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {state : State} {effect : Effect}
    (native : checkInstTypes func { module.tyEnv func with vals := types } types (.eff effect) = .ok ())
    (ready : refReady types state (.eff effect) = true) :
    checkInstruction module func types state (.eff effect) = true := by
  cases effect with
  | store address value origin =>
    cases addressType : ({ module.tyEnv func with vals := types } : TyEnv).refTy address with
    | error message => simp [checkInstTypes, checkEffectTypes, addressType, bind, Except.bind] at native
    | ok info =>
      rcases info with ⟨mutability, payload⟩
      cases valueType : ({ module.tyEnv func with vals := types } : TyEnv).dataTy value with
      | error message => simp [checkInstTypes, checkEffectTypes, addressType, valueType, bind, Except.bind, tyErr] at native
      | ok type =>
        simp_all [checkInstTypes, checkEffectTypes, checkInstruction, addressType, valueType,
          bind, Except.bind, pure, Except.pure, Except.toOption, tyErr]
  | slotInit slot value origin =>
    have slotsEq : (module.tyEnv func).slots = func.slots := rfl
    cases storage : func.slots[slot]? with
    | none => simp [checkInstTypes, checkEffectTypes, slotsEq, storage, bind, Except.bind, tyErr] at native
    | some actual =>
      cases valueType : ({ module.tyEnv func with vals := types } : TyEnv).dataTy value with
      | error message =>
        simp_all [checkInstTypes, checkEffectTypes, slotsEq, storage, valueType, bind, Except.bind, tyErr]
      | ok type =>
        simp_all [checkInstTypes, checkEffectTypes, checkInstruction, slotsEq, storage,
          valueType, bind, Except.bind, pure, Except.pure, Except.toOption, tyErr]
  | _ => simp_all [checkInstruction]

private theorem checked_return_values (env : TyEnv) (pairs : List (ValueId × Ty))
    (checked : (do
      for (value, type) in pairs do
        unless (← env.dataTy value) = type do tyErr "a returned value of another type than the result") =
          (.ok () : TyR Unit)) :
    pairs.all (fun (value, type) => (env.dataTy value).toOption == some type) = true := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨value, type⟩
    rw [List.forIn_cons] at checked
    cases found : env.dataTy value with
    | error message => simp [found, bind, Except.bind] at checked
    | ok actual =>
      by_cases same : actual = type
      · subst actual
        have tail := ih (by simpa [found, bind, Except.bind, pure, Except.pure] using checked)
        simpa only [List.all_cons, found, Except.toOption, beq_self_eq_true, Bool.true_and] using tail
      · simp [found, same, bind, Except.bind, tyErr] at checked

theorem checkInstruction_return_of_native {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {state : State} {values : List ValueId} {origin : Option OriginId}
    (native : checkInstTypes func { module.tyEnv func with vals := types } types (.term (.ret values origin)) = .ok ())
    (ready : refReady types state (.term (.ret values origin)) = true) :
    checkInstruction module func types state (.term (.ret values origin)) = true := by
  have arity : values.length = func.results.length := by
    by_cases equal : values.length = func.results.length
    · exact equal
    · simp [checkInstTypes, checkTermTypes, equal, bind, Except.bind, tyErr] at native
  have typed := checked_return_values { module.tyEnv func with vals := types } (values.zip func.results)
    (by simpa [checkInstTypes, checkTermTypes, arity, bind, Except.bind, pure, Except.pure] using native)
  simpa only [checkInstruction, ready, Bool.true_and, arity, beq_self_eq_true] using typed

theorem checkInstruction_branch_of_typed {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {state : State} {target : BlockId} {values : List ValueId}
    (ready : refReady types state (.term (.br target values)) = true)
    (typed : edgeTyped func types target values = true) :
    checkInstruction module func types state (.term (.br target values)) = true := by
  simp [checkInstruction, ready, typed]

theorem checkInstruction_condbr_of_native {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {state : State} {condition : ValueId}
    {thenBlock elseBlock : BlockId} {thenArgs elseArgs : List ValueId}
    (native : checkInstTypes func { module.tyEnv func with vals := types } types
      (.term (.condbr condition thenBlock thenArgs elseBlock elseArgs)) = .ok ())
    (ready : refReady types state (.term (.condbr condition thenBlock thenArgs elseBlock elseArgs)) = true)
    (thenTyped : edgeTyped func types thenBlock thenArgs = true)
    (elseTyped : edgeTyped func types elseBlock elseArgs = true) :
    checkInstruction module func types state (.term (.condbr condition thenBlock thenArgs elseBlock elseArgs)) = true := by
  cases found : ({ module.tyEnv func with vals := types } : TyEnv).dataTy condition with
  | error message => simp [checkInstTypes, checkTermTypes, found, bind, Except.bind] at native
  | ok type =>
    have boolean : type = .bool := by
      by_cases equal : type = .bool
      · exact equal
      · simp [checkInstTypes, checkTermTypes, found, equal, bind, Except.bind, tyErr] at native
    simp [checkInstruction, ready, found, boolean, thenTyped, elseTyped, Except.toOption]

theorem checkInstruction_of_native {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {state : State} {instruction : Inst}
    (native : checkInstTypes func { module.tyEnv func with vals := types } types instruction = .ok ())
    (ready : refReady types state instruction = true)
    (calls : ∀ value fn args origin, instruction = .def value (.call fn args origin) →
      checkCall module func state fn args = true)
    (branches : ∀ target args, instruction = .term (.br target args) → edgeTyped func types target args = true)
    (conditionals : ∀ condition thenBlock thenArgs elseBlock elseArgs,
      instruction = .term (.condbr condition thenBlock thenArgs elseBlock elseArgs) →
      edgeTyped func types thenBlock thenArgs = true ∧ edgeTyped func types elseBlock elseArgs = true) :
    checkInstruction module func types state instruction = true := by
  cases instruction with
  | «def» value op =>
    apply checkInstruction_definition_of_native native ready
    intro fn args origin equality
    exact calls value fn args origin (by rw [equality])
  | eff effect => exact checkInstruction_effect_of_native native ready
  | term term =>
    cases term with
    | ret values origin => exact checkInstruction_return_of_native native ready
    | br target args => exact checkInstruction_branch_of_typed ready (branches target args rfl)
    | condbr condition thenBlock thenArgs elseBlock elseArgs =>
      obtain ⟨thenTyped, elseTyped⟩ := conditionals condition thenBlock thenArgs elseBlock elseArgs rfl
      exact checkInstruction_condbr_of_native native ready thenTyped elseTyped
    | _ => simp_all [checkInstruction]

#print axioms checkInstruction_of_native

#print axioms checkInstruction_return_of_native
#print axioms checkInstruction_branch_of_typed
#print axioms checkInstruction_condbr_of_native

#print axioms checkInstruction_effect_of_native

#print axioms checkInstruction_definition_of_native

end Goose.Lower.Validation.ReplacementContentFlowSource
