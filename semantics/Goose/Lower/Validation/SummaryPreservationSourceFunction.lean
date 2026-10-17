import Goose.Lower.Validation.SummaryPreservationSourceReplay
import Goose.Lower.Validation.SummaryPreservationEntryBindings
import Goose.Lower.Validation.SummaryPreservationSourceBodyResults
import Goose.Lower.Validation.SummaryPreservationSourceScopeBoundsAccepted
import Goose.Lower.Validation.SummaryPreservationReplayFunctionFinish
import Goose.Lower.Validation.ValidationTypedModuleTables

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def contextEntryBindings (impl : Impl) (le : LEnv) : List (SlotId × ValueId × OriginId) :=
  (impl.params.toList.zip (newBlock (impl.params.toList.map fun p => .data (tyOfVar impl p.var)) le initState).1.2).map
    fun (param, value) => (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)

theorem contextEntryBindings_metadata {module : Core.Module} {impl : Impl} {index : ImplId}
    (le : LEnv) (accepted : Core.validate module = .ok ()) (row : module.impls[index]? = some impl) :
    ∀ binding ∈ contextEntryBindings impl le,
      binding.1 < impl.vars.size ∧ binding.2.2 < module.origins.size := by
  intro binding member
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, localVar, _, identity, _, variableRow, originBound⟩ := entry_parameter_pair le accepted row paired
  constructor
  · change param.var < impl.vars.size
    rw [identity]
    exact (Array.getElem?_eq_some_iff.mp variableRow).1
  · simpa only [identity, variableRow, Option.map_some, Option.getD_some] using originBound

theorem contextEntryBindings_values {module : Core.Module} {impl : Impl} {index : ImplId}
    (le : LEnv) (accepted : Core.validate module = .ok ()) (row : module.impls[index]? = some impl) :
    ∀ binding ∈ contextEntryBindings impl le, binding.2.1 <
      (entryReplayState (impl.params.toList.map fun p => .data (tyOfVar impl p.var)) le).vals.size := by
  intro binding member
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, localVar, parameterRow, _, same, _, _⟩ := entry_parameter_pair le accepted row paired
  rw [same, entryReplayState_values_size]
  simpa only [List.length_map, Array.length_toList] using (Array.getElem?_eq_some_iff.mp parameterRow).1

theorem contextEntryBindings_roots {module : Core.Module} {ctx : Context} {impl : Impl} {index : ImplId}
    (le : LEnv) (accepted : Core.validate module = .ok ()) (row : module.impls[index]? = some impl)
    (checked : CtxOk module impl ctx) :
    ∀ binding ∈ contextEntryBindings impl le, ∀ root ∈ rootsAt
      (entryRootValues (impl.params.toList.map fun p => .data (tyOfVar impl p.var))) binding.2.1,
      root ∈ rootsAt (typedContextSlotUpper module ctx impl) binding.1 := by
  intro binding member
  obtain ⟨⟨param, value⟩, paired, rfl⟩ := List.mem_map.mp member
  obtain ⟨i, localVar, parameterRow, identity, same, variableRow, _⟩ := entry_parameter_pair le accepted row paired
  rw [same]
  exact entry_parameter_roots_within_slots checked parameterRow identity variableRow

theorem entryReplayState_generated (types : List VTy) (le : LEnv) :
    GeneratedBuilderState (entryReplayState types le) := by
  have allocated := GeneratedBuilderState.initState.newBlock types (env := le) rfl
  exact allocated.setCur (some (newBlock types le initState).1.1) (by
    intro block same
    cases Option.some.inj same
    simp [newBlock_run_general]) (env := le) rfl

theorem lowerBlock_value_want (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (body : Core.Block) : lowerBlock loop pre body.value.isSome body = lowerBlock loop pre false body := by
  cases body with
  | mk scope statements value => cases value <;> rfl

def ContextReplayProduced (module : Core.Module) (ctx : Context) (impl : Impl)
    (results : Array (List RootRef)) : Prop :=
  ∃ roots range after upper,
    rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ = .ok ((roots, range), after) ∧
    ReplayBuilder (lower module) results ((lowerContextAt module ctx impl).valueTypes (lower module))
      (lowerContextAt module ctx impl) after.eff (lowerEnv module impl.vars impl.results.toList)
      (lowerContextAt module ctx impl).scopes.size (typedContextSlotUpper module ctx impl)
      (cfg_implState module impl) upper ∧
    BuilderReturnsBound upper (contextTypedResultUpper module ctx) (cfg_implState module impl) ∧
    ∀ index, index < impl.params.size → rootsAt upper.vals index =
      rootsAt (entryRootValues (impl.params.toList.map fun p => .data (tyOfVar impl p.var))) index

theorem accepted_context_replay_produced {module : Core.Module} {ctx : Context} {impl : Impl} {context : ContextId}
    {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow results (moduleTypedResultUpper module)) :
    ContextReplayProduced module ctx impl results := by
  let env : PEnv := ⟨module, impl, ctx, []⟩
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun p => VTy.data (tyOfVar impl p.var)
  let entry := entryReplayState types le
  let startUpper : Prov := ⟨typedContextSlotUpper module ctx impl, entryRootValues types⟩
  let bindings := contextEntryBindings impl le
  let body := lowerBlock none bindings impl.body.value.isSome impl.body le entry
  let vt := (lowerContextAt module ctx impl).valueTypes (lower module)
  have source : SourceContextEnvironment (implEnv module impl) env context :=
    ⟨accepted, ⟨rfl, rfl⟩, rfl, contextRow, implementationRow⟩
  obtain ⟨type, finish, typed, _⟩ := (validate_modOk module accepted).impl ctx.impl impl implementationRow |>.body
  obtain ⟨roots, range, after, replayed, _, _⟩ := source.contextOk.body
  have whole : cfg_implState module impl = (Goose.Lower.finishFunction impl body.1 le body.2).2 := by
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, body, bindings, contextEntryBindings,
      entry, entryReplayState, types, le, lowerBlock_value_want]
  have nativeFinal : NativeRows vt (cfg_implState module impl) := by
    rw [show vt = (cfg_implState module impl).vals from lowerContext_valueTypes_of_accepted accepted implementationRow]
    exact NativeRows.refl _
  have nativeBody : NativeRows vt body.2 := by
    rw [whole] at nativeFinal
    exact nativeFinal.of_prefix (ReplayBuilder.types_finishFunction impl body.1 le body.2 _ _ rfl)
  have ready := lowerContext_entryReplayBuilder module ctx impl results vt after.eff (lowerContextAt module ctx impl).scopes.size
  have scopes := accepted_context_scope_bounds accepted contextRow implementationRow
  obtain ⟨upper, bodyReady, bodyValue, retained, transferred⟩ :=
    source_block_replay impl.body source bounded scopes none bindings impl.body.value.isSome entry startUpper
      type impl.params.size finish ⟨impl.params.size, {}⟩ after roots range typed replayed
      (EffectRefinement.refl _ after.eff) scopes
      (contextEntryBindings_metadata le accepted implementationRow)
      (fun _ => contextEntryBindings_values le accepted implementationRow)
      (contextEntryBindings_roots le accepted implementationRow source.contextOk)
      (by intro _ scope member; simp [entry, entryReplayState, newBlock_run_general, initState] at member)
      ready (entryReplayState_generated types le) trivial trivial nativeBody
  have prior : BuilderReturnsBound startUpper (contextTypedResultUpper module ctx) entry := by
    intro value origin member
    rw [entryReplayState_instructions types le] at member
    cases member
  have bodyReturns := transferred.apply_expected prior
  obtain ⟨finished, finishReturns⟩ := bodyReady.finishFunction impl body.1 (contextTypedResultUpper module ctx)
    (fun live present => (bodyValue present live).bound)
    (fun live present => source_body_result_upper accepted contextRow implementationRow typed replayed present
      (bodyValue present live))
  refine ⟨roots, range, after, upper, replayed, ?_, ?_, ?_⟩
  · rw [whole]
    exact finished
  · rw [whole]
    exact finishReturns.apply_expected bodyReturns
  · intro index bound
    apply retained index
    simpa only [startUpper, entryRootValues, Array.size_mapIdx, List.size_toArray, List.length_map,
      Array.length_toList, types] using bound

#print axioms accepted_context_replay_produced

end Goose.Lower.Validation.SummaryPreservation
