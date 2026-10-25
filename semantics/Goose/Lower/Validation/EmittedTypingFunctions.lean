import Goose.Lower.Validation.EmittedTypingSource
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Core.Sound.Module
import Goose.Lower.Validation.OperandFunctions

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem EmittedBuilder.finishFunction {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (impl : Core.Impl) (value : ValueId)
    (bounded : impl.body.value.isSome = true → before.cur.isSome = true → value < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.finishFunction impl value le before).2 := by
  have state : (Goose.Lower.finishFunction impl value le before).2 =
      if before.cur.isSome then
        if !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn then
          ((do
            let (sink, _) ← Goose.Lower.newBlock []
            Goose.Lower.emitTerm (.br sink [])
            Goose.Lower.setCur (some sink)
            Goose.Lower.emitTerm (.br sink []) : B Unit) le before).2
        else (Goose.Lower.emitTerm (.ret (if impl.body.value.isSome then [value] else []) none) le before).2
      else before := by
    have test : isLive le before = (before.cur.isSome, before) := by
      simp [isLive, bind_run, curBlock_run, pure_run]
    simp only [Goose.Lower.finishFunction, bind_run, read_apply, test]
    by_cases active : before.cur.isSome = true
    · simp only [active, reduceIte]
      by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
      · simp only [sink, reduceIte, bind_run]
      · simp only [sink, Bool.false_eq_true, reduceIte]
    · simp only [active, Bool.false_eq_true, reduceIte, pure_run]
  rw [state]
  cases live : before.cur.isSome
  · exact builder
  · simp only [reduceIte]
    by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, reduceIte, bind_run]
      let allocated := Goose.Lower.newBlock [] le before
      let closed := Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2
      have allocatedBuilder := builder.newBlock []
      have closedBuilder := allocatedBuilder.emitTerm (.br allocated.1.1 [])
        (by intro active operand member; simp [Term.uses] at member)
      have selectedBuilder := closedBuilder.setCur (some allocated.1.1) (by
        intro block same
        cases Option.some.inj same
        exact Nat.lt_of_lt_of_le (by simp [allocated, newBlock_run_general])
          (advB_emitTerm (.br allocated.1.1 []) le allocated.2 _ _ rfl).ext.1)
      exact selectedBuilder.emitTerm (.br allocated.1.1 [])
        (by intro active operand member; simp [Term.uses] at member)
    · rw [ite_eq_right sink]
      apply builder.emitTerm
      intro active operand member
      cases present : impl.body.value.isSome
      · simp [Term.uses, present] at member
      · have equal : operand = value := by simpa [Term.uses, present] using member
        subst operand
        exact bounded present active

theorem lowerImpl_emittedBuilder {module : Core.Module} {impl : Core.Impl} {type : Ty} {finish : Nat}
    (typed : Core.tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish)) :
    EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl) := by
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun param => VTy.data (tyOfVar impl param.var)
  let allocated := newBlock types le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let pre : List (SlotId × ValueId × OriginId) := (impl.params.toList.zip allocated.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let output := lowerBlock none pre false impl.body le selected.2
  have allocatedBuilder := (EmittedBuilder.initState le).newBlock types
  have allocatedGenerated : GeneratedBuilderState allocated.2 := GeneratedBuilderState.initState.newBlock (env := le) types rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have selectedBound : ∀ block, some allocated.1.1 = some block → block < allocated.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact fresh
  have selectedBuilder := allocatedBuilder.setCur (some allocated.1.1) selectedBound
  have selectedGenerated : GeneratedBuilderState selected.2 := allocatedGenerated.setCur (env := le) _ selectedBound rfl
  have preBounds : ∀ slot value origin, (slot, value, origin) ∈ pre → value < selected.2.vals.size := by
    intro slot value origin member
    obtain ⟨⟨param, value⟩, paired, same⟩ := List.mem_map.mp member
    cases same
    exact newBlock_param_bound (show newBlock types le initState = allocated from rfl) value (List.of_mem_zip paired).2
  have outputBuilder := emitted_source_block impl.body (implEnv module impl) impl.results.toList typed
    none pre false selectedGenerated selectedBuilder trivial trivial preBounds
  have finished := outputBuilder.finishFunction impl output.1 (by
    intro present
    exact value_lowerBlock_with_tail none pre false impl.body present le selected.2 output.1 output.2 rfl)
  simpa only [cfg_implState, cfg_implAction, bind_run, implEnv, le, types, allocated, selected, pre, output] using finished

theorem lowerGlobal_emittedBuilder {module : Core.Module} {global : Core.Global} {index finish : Nat}
    (typed : Core.tyExpr (initEnv module index) global.init 0 = .ok (global.ty, finish)) :
    EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global) := by
  let le := lowerEnv module #[] [global.ty]
  let allocated := newBlock [] le initState
  let selected := setCur (some allocated.1.1) le allocated.2
  let output := lowerExpr global.init le selected.2
  have allocatedBuilder := (EmittedBuilder.initState le).newBlock []
  have allocatedGenerated : GeneratedBuilderState allocated.2 := GeneratedBuilderState.initState.newBlock (env := le) [] rfl
  have fresh : allocated.1.1 < allocated.2.blocks.size := by simp [allocated, newBlock_run_general]
  have selectedBound : ∀ block, some allocated.1.1 = some block → block < allocated.2.blocks.size := by
    intro block same
    cases Option.some.inj same
    exact fresh
  have selectedBuilder := allocatedBuilder.setCur (some allocated.1.1) selectedBound
  have selectedGenerated : GeneratedBuilderState selected.2 := allocatedGenerated.setCur (env := le) _ selectedBound rfl
  have outputBuilder := emitted_source_expression global.init (initEnv module index) [global.ty] typed selectedGenerated selectedBuilder
  have finished := outputBuilder.emitTerm (.ret [output.1] (some global.org)) (by
    intro active value member
    have equal : value = output.1 := by simpa [Term.uses] using member
    subst value
    exact value_lowerExpr global.init le selected.2 output.1 output.2 rfl active)
  simpa only [cfg_globalState, cfg_globalAction, bind_run, initEnv, le, allocated, selected, output] using finished

theorem lowerImpl_emittedBuilder_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {impl : Core.Impl} {index : Nat} (row : module.impls[index]? = some impl) :
    EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl) := by
  obtain ⟨type, finish, typed, _⟩ := ((validate_modOk module accepted).impl index impl row).body
  exact lowerImpl_emittedBuilder typed

theorem lowerGlobal_emittedBuilder_of_accepted {module : Core.Module} (accepted : Core.validate module = .ok ())
    {global : Core.Global} {index : Nat} (row : module.globals[index]? = some global) :
    EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global) := by
  obtain ⟨finish, typed⟩ := ((validate_modOk module accepted).glob index global row).init
  exact lowerGlobal_emittedBuilder typed

end Goose.Lower.Validation
