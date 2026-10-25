import Goose.Lower.Validation.EmittedMetadataStaticTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EmittedResolvedValues (module : Core.Module) (state : LS) : Prop :=
  ∀ (value : ValueId) (type : VTy), state.vals[value]? = some (some type) →
    EmittedVTyResolved module type

structure EmittedStaticTables (module : Core.Module) (le : LEnv) : Prop where
  slots : ∀ (index : Nat) (descriptor : Slot), le.slots[index]? = some descriptor →
    Core.checkResolvedType module descriptor.ty = .ok ()
  globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), le.globals[index]? = some (type, kind) →
    Core.checkResolvedType module type = .ok ()
  signatures : ∀ (index : Nat) (params results : List Ty), le.sigs[index]? = some (params, results) →
    ∀ type ∈ results, Core.checkResolvedType module type = .ok ()
  fields : ∀ (index : Nat) (descriptor : StructDef), le.mod.structs[index]? = some descriptor →
    ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field →
      Core.checkResolvedType module field.ty = .ok ()

theorem EmittedStaticTables.environment {module : Core.Module} {le : LEnv} {state : LS}
    (tables : EmittedStaticTables module le) (values : EmittedResolvedValues module state) :
    EmittedTyEnvResolved module (tyEnv le state) := by
  refine ⟨?_, tables.slots, tables.globals, tables.signatures, tables.fields⟩
  intro value type typed
  unfold TyEnv.valTy at typed
  cases row : state.vals[value]? with
  | none => simp [tyEnv, row, tyErr] at typed
  | some found =>
    cases found with
    | none => simp [tyEnv, row, tyErr] at typed
    | some known =>
      simp only [tyEnv, row, Except.ok.injEq] at typed
      subst type
      exact values value known row

structure EmittedStaticState (module : Core.Module) (state : LS) : Prop extends EmittedStatic module state where
  values : EmittedResolvedValues module state

def EmittedStaticStateRun (module : Core.Module) (le : LEnv) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) →
    EmittedStaticState module before → EmittedStaticState module after

theorem EmittedStaticStateRun.pure (module : Core.Module) (le : LEnv) (value : α) :
    EmittedStaticStateRun module le (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem EmittedStaticStateRun.bind {module : Core.Module} {le : LEnv}
    {action : B α} {next : α → B β} (first : EmittedStaticStateRun module le action)
    (second : ∀ value, EmittedStaticStateRun module le (next value)) :
    EmittedStaticStateRun module le (action >>= next) := by
  intro before result after run checked
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ secondRun (first _ _ _ firstRun checked)

theorem EmittedStaticState.initState (module : Core.Module) : EmittedStaticState module initState := by
  refine ⟨EmittedStatic.initState module, ?_⟩
  intro value type row
  simp [Goose.Lower.initState] at row

theorem EmittedStaticState.valTy {module : Core.Module} {state : LS}
    (checked : EmittedStaticState module state) (le : LEnv) (value : ValueId) :
    EmittedVTyResolved module (Goose.Lower.valTy value le state).1 := by
  unfold Goose.Lower.valTy
  simp only [bind_run, get_apply]
  cases row : state.vals[value]? with
  | none => simp [row, pure_run, EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure]
  | some found =>
    cases found with
    | none => simp [row, pure_run, EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure]
    | some type => simpa [row, pure_run] using checked.values value type row

theorem staticState_emitDef {module : Core.Module} {le : LEnv}
    (tables : EmittedStaticTables module le) (op : Op)
    (profile : ∀ value, EmittedProfileInst module.profile (.def value op))
    (annotation : ∀ value, EmittedAnnotationResolved module (.def value op)) :
    EmittedStaticStateRun module le (emitDef op) := by
  intro before result after run checked
  refine ⟨static_emitDef op profile annotation _ _ _ run checked.toEmittedStatic, ?_⟩
  cases live : before.cur with
  | none =>
    rw [emitDef_none op le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.values
  | some block =>
    rw [emitDef_run op le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro value type row
    change (before.vals.push (some ((op.resultTy (tyEnv le before)).toOption.getD (.data .unit))))[value]? = some (some type) at row
    by_cases fresh : value = before.vals.size
    · subst value
      simp only [Array.getElem?_push_size, Option.some.injEq] at row
      subst type
      cases output : op.resultTy (tyEnv le before) with
      | error _ => rfl
      | ok outputType =>
        exact op_resultTy_resolved (tables.environment checked.values) op annotation output
    · have old : before.vals[value]? = some (some type) := by
        simpa only [Array.getElem?_push, fresh, ↓reduceIte] using row
      exact checked.values value type old

theorem EmittedStaticStateRun.of_static {module : Core.Module} {le : LEnv} {action : B α}
    (static : EmittedStaticRun module le action)
    (values : ∀ before, (action le before).2.vals = before.vals) :
    EmittedStaticStateRun module le action := by
  intro before result after run checked
  refine ⟨static _ _ _ run checked.toEmittedStatic, ?_⟩
  have same := values before
  rw [run] at same
  change after.vals = before.vals at same
  intro value type row
  exact checked.values value type (same ▸ row)

theorem EmittedResolvedValues.push {module : Core.Module} {state : LS}
    (checked : EmittedResolvedValues module state) (type : VTy)
    (resolved : EmittedVTyResolved module type) :
    EmittedResolvedValues module {state with vals := state.vals.push (some type)} := by
  intro value found row
  change (state.vals.push (some type))[value]? = some (some found) at row
  by_cases fresh : value = state.vals.size
  · subst value
    simp only [Array.getElem?_push_size, Option.some.injEq] at row
    cases row
    exact resolved
  · exact checked value found (by simpa only [Array.getElem?_push, fresh, ↓reduceIte] using row)

theorem EmittedResolvedValues.pushTypes {module : Core.Module} (types : List VTy) (state : LS)
    (checked : EmittedResolvedValues module state)
    (resolved : ∀ type ∈ types, EmittedVTyResolved module type) :
    EmittedResolvedValues module {state with vals := pushParamTypes types state.vals} := by
  induction types generalizing state with
  | nil => exact checked
  | cons type types ih =>
    exact ih {state with vals := state.vals.push (some type)}
      (checked.push type (resolved type (by simp))) (fun item member => resolved item (by simp [member]))

theorem staticState_newBlock {module : Core.Module} {le : LEnv} (types : List VTy)
    (resolved : ∀ type ∈ types, EmittedVTyResolved module type) :
    EmittedStaticStateRun module le (newBlock types) := by
  intro before result after run checked
  refine ⟨static_newBlock types resolved _ _ _ run checked.toEmittedStatic, ?_⟩
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked.values.pushTypes types before resolved

theorem staticState_emitEffect {module : Core.Module} {le : LEnv} (effect : Effect)
    (profile : EmittedProfileInst module.profile (.eff effect)) :
    EmittedStaticStateRun module le (emitEffect effect) := by
  apply EmittedStaticStateRun.of_static (static_emitEffect effect profile)
  intro before
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live]
  | some block => rw [emitEffect_run effect le live]

theorem staticState_emitTerm {module : Core.Module} {le : LEnv} (term : Term)
    (profile : EmittedProfileInst module.profile (.term term)) :
    EmittedStaticStateRun module le (emitTerm term) := by
  apply EmittedStaticStateRun.of_static (static_emitTerm term profile)
  intro before
  cases live : before.cur with
  | none => rw [emitTerm_none term le live]
  | some block => rw [emitTerm_run term le live]

theorem staticState_patchTerm {module : Core.Module} {le : LEnv} (block : BlockId) (term : Term)
    (profile : EmittedProfileInst module.profile (.term term)) :
    EmittedStaticStateRun module le (patchTerm block term) := by
  apply EmittedStaticStateRun.of_static (static_patchTerm block term profile)
  intro before
  rw [patchTerm_run]

theorem staticState_get (module : Core.Module) (le : LEnv) : EmittedStaticStateRun module le (get : B LS) :=
  EmittedStaticStateRun.of_static (static_get module le) (fun _ => rfl)

theorem staticState_read (module : Core.Module) (le : LEnv) : EmittedStaticStateRun module le (read : B LEnv) :=
  EmittedStaticStateRun.of_static (static_read module le) (fun _ => rfl)

theorem staticState_valTy (module : Core.Module) (le : LEnv) (value : ValueId) :
    EmittedStaticStateRun module le (valTy value) :=
  EmittedStaticStateRun.of_static (static_valTy module le value) (fun before => by rw [valTy_run])

theorem staticState_curBlock (module : Core.Module) (le : LEnv) : EmittedStaticStateRun module le curBlock :=
  EmittedStaticStateRun.of_static (static_curBlock module le) (fun before => by rw [curBlock_run])

theorem staticState_setCur (module : Core.Module) (le : LEnv) (block : Option BlockId) :
    EmittedStaticStateRun module le (setCur block) :=
  EmittedStaticStateRun.of_static (static_setCur module le block) (fun before => by rw [setCur_run])

theorem staticState_pushScope (module : Core.Module) (le : LEnv) (scope : ScopeId) :
    EmittedStaticStateRun module le (pushScope scope) :=
  EmittedStaticStateRun.of_static (static_pushScope module le scope) (fun before => by rw [pushScope_run])

theorem staticState_popScope (module : Core.Module) (le : LEnv) : EmittedStaticStateRun module le popScope :=
  EmittedStaticStateRun.of_static (static_popScope module le) (fun before => by rw [popScope_run])

end Goose.Lower.Validation
