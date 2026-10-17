import Goose.Lower.Validation.SummaryPreservationRefinedAppend

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

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target later : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem source_mono (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (bound : EffectRefinement func target later) :
    ReplayBuilder module results vt func later le scopeCount slots ls upper :=
  ⟨ready.roots, fun inst member => (ready.effects inst member).trans bound,
    ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq⟩

theorem setCur (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (next : Option BlockId) (bound : ∀ block, next = some block → block < ls.blocks.size) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.setCur next le ls).2 upper := by
  rw [setCur_run]
  exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
    ready.symbols.changeCur _, bound, ready.slotsEq⟩

theorem pushScope (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (scope : ScopeId) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.pushScope scope le ls).2 upper := by
  rw [pushScope_run]
  exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
    ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq⟩

theorem popScope (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.popScope le ls).2 upper := by
  rw [popScope_run]
  exact ⟨⟨ready.roots.valueSize, ready.roots.instructions⟩, ready.effects,
    ⟨ready.symbols.definitions, ready.symbols.instructions⟩, ready.current, ready.slotsEq⟩

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
    refine ⟨completed.1, completed.2, ?_, ?_, ready.slotsEq⟩
    · rw [emitEffect_run _ _ current]
      exact ready.symbols.emitEffect bound symbols
    · rw [emitEffect_run _ _ current]
      intro candidate candidateRow
      simpa using ready.current candidate candidateRow


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

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
