import Goose.Lower.Validation.SummaryPreservationReplayBuilder

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem emitTerm (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (term : Term)
    (symbols : ls.cur.isSome = true →
      Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.term term))
    (roots : ls.cur.isSome = true →
      InstructionRootsClosed results vt { func with blocks := finishBlocks ls.blocks } upper (.term term))
    (delta : ls.cur.isSome = true →
      EffectRefinement func (func.effectStep module vt upper {} (.term term)) target) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.emitTerm term le ls).2 upper := by
  cases current : ls.cur with
  | none =>
    rw [emitTerm_none _ _ current]
    exact ready
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    have bound := ready.current block current
    have completed := emitTerm_refined_witness (le := le) current bound ready.roots ready.effects
      (roots live) (delta live)
    refine ⟨completed.1, completed.2, ?_, ?_, ready.slotsEq, ready.recipes.same (recipesUnchangedB_emitTerm term le ls)⟩
    · rw [emitTerm_run _ _ current]
      exact ready.symbols.emitTerm bound (symbols live)
    · rw [emitTerm_run _ _ current]
      intro candidate candidateRow
      cases candidateRow

theorem unreachable (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.emitTerm .unreachable le ls).2 upper := by
  apply ready.emitTerm .unreachable
  · intro _
    apply Inst.SymbolsWithin.term <;> simp [Term.uses, Term.origin, Term.successors]
  · intro _
    trivial
  · intro _
    exact effectRefinement_empty func target

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
