import Goose.Lower.Validation.SummaryPreservationRefinedAppend
import Goose.Lower.Validation.SummaryPreservationRecipeBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

structure ReplayBuilder (module : GIR.Module) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (target : Core.Eff) (le : LEnv)
    (scopeCount : Nat) (slots : Array (List RootRef)) (ls : LS) (upper : Prov) : Prop where
  roots : BuilderRootWitness results vt func upper ls
  effects : BuilderEffectRefinement module vt func upper target ls
  symbols : ls.SymbolWF le scopeCount
  current : ls.CurrentBlocks
  slotsEq : upper.slots = slots
  recipes : RecipeBounds func upper ls

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target later : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem source_mono (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (bound : EffectRefinement func target later) :
    ReplayBuilder module results vt func later le scopeCount slots ls upper :=
  ⟨ready.roots, fun inst member => (ready.effects inst member).trans bound,
    ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq, ready.recipes⟩

theorem setCur (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (next : Option BlockId) (bound : ∀ block, next = some block → block < ls.blocks.size) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.setCur next le ls).2 upper := by
  rw [setCur_run]
  exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
    ready.symbols.changeCur _, bound, ready.slotsEq, ready.recipes.same rfl⟩

theorem pushScope (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (scope : ScopeId) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.pushScope scope le ls).2 upper := by
  rw [pushScope_run]
  exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
    ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq, ready.recipes.same rfl⟩

theorem popScope (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.popScope le ls).2 upper := by
  rw [popScope_run]
  exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
    ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq, ready.recipes.same rfl⟩

theorem emitEffect (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (effect : Effect)
    (symbols : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.eff effect))
    (roots : InstructionRootsClosed results vt { func with blocks := finishBlocks ls.blocks } upper (.eff effect))
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.eff effect)) target) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.emitEffect effect le ls).2 upper := by
  cases current : ls.cur with
  | none =>
    rw [emitEffect_none _ _ current]
    exact ready
  | some block =>
    have bound := ready.current block current
    have completed := emitEffect_refined_witness (le := le) current bound ready.roots ready.effects roots delta
    refine ⟨completed.1, completed.2, ?_, ?_, ready.slotsEq, ?_⟩
    · rw [emitEffect_run _ _ current]
      exact ready.symbols.emitEffect bound symbols
    · rw [emitEffect_run _ _ current]
      intro candidate candidateRow
      simpa using ready.current candidate candidateRow
    · rw [emitEffect_run _ _ current]
      exact ready.recipes.same rfl


theorem enter (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (scope : ScopeId) (bound : scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.emitEffect (.enter scope) le ls).2 upper := by
  apply ready.emitEffect (.enter scope)
  · apply Inst.SymbolsWithin.eff
    · simp [Effect.uses]
    · simp [Effect.origin]
    · exact bound
  · trivial
  · exact effectRefinement_empty func target

theorem leave (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (scope : ScopeId) (bound : scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.emitEffect (.leave scope) le ls).2 upper := by
  apply ready.emitEffect (.leave scope)
  · apply Inst.SymbolsWithin.eff
    · simp [Effect.uses]
    · simp [Effect.origin]
    · exact bound
  · trivial
  · exact effectRefinement_empty func target

theorem recordValueRootSourceWhen
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (value : ValueId) (source : ValueRootSource)
    (rows : (Goose.Lower.recordValueRootSource value source le ls).2.valueRootRecipes =
      ls.valueRootRecipes.push (value, source) →
      ∀ row ∈ func.roots.values.getD #[], row.1 = value →
        row.2 ⊆ rootsAt upper.vals value ∧ rootsAt upper.vals value ⊆ row.2) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.recordValueRootSource value source le ls).2 upper := by
  let reference := match ls.vals[value]?.join with
    | some (.data type) => type.isRefLike
    | some (.view ..) => true
    | none => false
  have recorded := ready.recipes.recordSourceWhen value source le
    (fun recorded => by simpa only [ready.roots.valueSize] using recordValueRootSource_bound recorded) rows
  change RecipeBounds func upper (if ls.cur.isSome && reference then
    {ls with valueRootRecipes := ls.valueRootRecipes.push (value, source)} else ls) at recorded
  change ReplayBuilder module results vt func target le scopeCount slots
    (if ls.cur.isSome && reference then
      {ls with valueRootRecipes := ls.valueRootRecipes.push (value, source)} else ls) upper
  by_cases active : (ls.cur.isSome && reference) = true
  · rw [if_pos active] at recorded ⊢
    exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
      ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq, recorded⟩
  · rw [if_neg active]
    exact ready

theorem recordValueRootRecipeWhen
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (value : ValueId) (scope : ScopeId)
    (rows : (Goose.Lower.recordValueRootRecipe value scope le ls).2.valueRootRecipes =
      ls.valueRootRecipes.push (value, .conditionalScope scope) →
      ∀ row ∈ func.roots.values.getD #[], row.1 = value →
        row.2 ⊆ rootsAt upper.vals value ∧ rootsAt upper.vals value ⊆ row.2) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.recordValueRootRecipe value scope le ls).2 upper := by
  exact ready.recordValueRootSourceWhen value (.conditionalScope scope) rows

theorem recordValueRootRecipe
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (value : ValueId) (scope : ScopeId)
    (rows : ∀ row ∈ func.roots.values.getD #[], row.1 = value →
      row.2 ⊆ rootsAt upper.vals value ∧ rootsAt upper.vals value ⊆ row.2) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.recordValueRootRecipe value scope le ls).2 upper := by
  exact ready.recordValueRootRecipeWhen value scope (fun _ => rows)

theorem recordReadValueRootRecipeWhen
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (value : ValueId) (place : Place)
    (rows : ∀ source,
      (Goose.Lower.recordReadValueRootRecipe value place le ls).2.valueRootRecipes =
        ls.valueRootRecipes.push (value, source) →
      ∀ row ∈ func.roots.values.getD #[], row.1 = value →
        row.2 ⊆ rootsAt upper.vals value ∧ rootsAt upper.vals value ⊆ row.2) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.recordReadValueRootRecipe value place le ls).2 upper := by
  cases place with
  | var variableId =>
    by_cases reference : ((le.vars[variableId]?).any (·.ty.isRefSlice)) = true
    · have result := ready.recordValueRootSourceWhen value (.refSliceVar variableId) (fun recorded =>
        rows (.refSliceVar variableId) (by
          simpa only [Goose.Lower.recordReadValueRootRecipe, bind_run, read_apply, reference, ite_true]
            using recorded))
      simpa only [Goose.Lower.recordReadValueRootRecipe, bind_run, read_apply, reference, ite_true]
        using result
    · simpa [Goose.Lower.recordReadValueRootRecipe, bind_run, read_apply, reference,
        pure_run] using ready
  | global global => exact ready
  | deref expression => exact ready
  | field owner field => exact ready
  | elem view index => exact ready

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
