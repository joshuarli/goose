import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit
import Goose.Lower.Validation.SummaryPreservationRefinedBlocks
import Goose.Lower.Validation.SummaryPreservationPatchBranches
import Goose.Lower.Validation.SummaryPreservationInitialSlots

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem loopEmptyBlock (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper) :
    ReplayBuilder module results vt func target le scopeCount slots (newBlock [] le ls).2 upper := by
  have generated := newBlock_empty_refined_witness ready.symbols ready.roots ready.effects
  refine ⟨generated.1, generated.2, ?_, ?_, ready.slotsEq⟩
  · simpa [newBlock0_run, paramIds, pushParamTypes] using
      (ready.symbols.newBlock (tys := []))
  · rw [newBlock0_run]
    intro block current
    have bound := ready.current block current
    simpa using Nat.lt_succ_of_lt bound

theorem loopScalarBlock (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (type : VTy) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots (newBlock [type] le ls).2 next ∧
      rootsAt next.vals ls.vals.size = [] ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, roots, effects, scalar, slotsEq, growth⟩ :=
    newBlock_parameter_refined_frame [] type ready.symbols ready.roots ready.effects
  refine ⟨next, ⟨roots, effects, ?_, ?_, slotsEq.trans ready.slotsEq⟩, scalar, growth⟩
  · simpa [newBlock1_run, paramIds, pushParamTypes] using
      (ready.symbols.newBlock (tys := [type]))
  · rw [newBlock1_run]
    intro block current
    have bound := ready.current block current
    simpa using Nat.lt_succ_of_lt bound

private theorem emitLoopTerm (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (term : Term)
    (symbols : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.term term))
    (closed : InstructionRootsClosed results vt { func with blocks := finishBlocks ls.blocks } upper (.term term))
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.term term)) target) :
    ReplayBuilder module results vt func target le scopeCount slots (emitTerm term le ls).2 upper := by
  cases current : ls.cur with
  | none => rw [emitTerm_none _ _ current]; exact ready
  | some block =>
    have bound := ready.current block current
    have next := emitTerm_refined_witness (le := le) current bound ready.roots ready.effects closed delta
    refine ⟨next.1, next.2, ?_, ?_, ready.slotsEq⟩
    · rw [emitTerm_run _ _ current]
      exact ready.symbols.emitTerm bound symbols
    · rw [emitTerm_run _ _ current]
      intro block current
      cases current

theorem loopBranch (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (destination : BlockId) (arguments : List ValueId)
    (destinationBound : destination < ls.blocks.size)
    (bounds : ∀ value ∈ arguments, value < ls.vals.size)
    (scalar : ∀ value ∈ arguments, rootsAt upper.vals value = []) :
    ReplayBuilder module results vt func target le scopeCount slots
      (emitTerm (.br destination arguments) le ls).2 upper := by
  apply ready.emitLoopTerm (.br destination arguments)
  · apply Inst.SymbolsWithin.term
    · simpa [Term.uses] using bounds
    · simp [Term.origin]
    · simpa [Term.successors] using destinationBound
  · intro block row pair member root rootMember
    have argument := (List.of_mem_zip member).2
    rw [scalar pair.2 argument] at rootMember
    cases rootMember
  · exact effectRefinement_empty func target

theorem loopConditional (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (condition : ValueId) (yes no : BlockId) (conditionBound : condition < ls.vals.size)
    (yesBound : yes < ls.blocks.size) (noBound : no < ls.blocks.size) :
    ReplayBuilder module results vt func target le scopeCount slots
      (emitTerm (.condbr condition yes [] no []) le ls).2 upper := by
  apply ready.emitLoopTerm (.condbr condition yes [] no [])
  · apply Inst.SymbolsWithin.term
    · simpa [Term.uses] using conditionBound
    · simp [Term.origin]
    · simp [Term.successors, yesBound, noBound]
  · constructor <;> intro block row pair member <;> simp at member
  · exact effectRefinement_empty func target

theorem loopFork (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (condition : ValueId) (conditionBound : condition < ls.vals.size) :
    ReplayBuilder module results vt func target le scopeCount slots (fork condition le ls).2 upper := by
  have first := ready.loopEmptyBlock
  have second := first.loopEmptyBlock
  have conditional := second.loopConditional condition ls.blocks.size (ls.blocks.size + 1)
    (by simpa [newBlock0_run] using conditionBound) (by simpa [newBlock0_run] using (show ls.blocks.size < ls.blocks.size + 1 + 1 by omega))
    (by simpa [newBlock0_run] using (show ls.blocks.size + 1 < ls.blocks.size + 1 + 1 by omega))
  simpa only [fork, bind_run, newBlock0_run, Array.size_push, pure_run] using conditional

theorem loopRangeBack (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (type : IntTy) (counter : ValueId) (header : BlockId)
    (headerBound : header < ls.blocks.size)
    (counterBound : counter < ls.vals.size) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (rangeBack type counter header le ls).2 next ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    have stopped : rangeBack type counter header le ls = ((), ls) := by
      simp [rangeBack, bind_run, isLive_none current, pure_run]
    rw [stopped]
    exact ⟨upper, ready, fun _ _ => rfl⟩
  | some block =>
    obtain ⟨next, nextReady, scalar, growth⟩ := ready.emitTypedDef (.next type counter) [] (.data (.int type))
      (by simpa [Op.uses] using counterBound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
      (effectRefinement_empty func target) (fun _ member => by cases member) (fun _ => rfl)
    have nextLive : (Goose.Lower.emitDef (.next type counter) le ls).2.cur.isSome = true := by
      simp [emitDef_run _ _ current, current]
    have value := scalar nextLive
    have back := nextReady.loopBranch header [(Goose.Lower.emitDef (.next type counter) le ls).1]
      (by simpa [emitDef_run _ _ current] using headerBound)
      (by simpa using value.bound) (by simpa using value.scalar rfl)
    refine ⟨next, ?_, growth⟩
    simpa only [rangeBack, bind_run, isLive_run current, Option.isSome_some, ite_true] using back

#print axioms loopScalarBlock
#print axioms loopFork
#print axioms loopRangeBack

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
