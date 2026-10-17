import Goose.Lower.Validation.SummaryPreservationReplayMutationsOwners
import Goose.Lower.Validation.SummaryPreservationLowerResizeFill

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem popN {env : PEnv} {owner : Place} {count : Expr} {origin : OriginId}
    {initialSource ownerState before after : RState} {ownerRoots countRoots : List RootRef}
    {initial ownerLS : LS} {address amount : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, ownerState))
    (countReplay : rpExpr env count ownerState = .ok (countRoots, before))
    (source : rpStmt env (.popN owner count origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (countRun : lowerExpr count le ownerLS = (amount, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ amount < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.popN owner count origin) le initial).2 upper := by
  have sourceEffect := rpStmt_popN_effect ownerReplay countReplay source
  have whole : lowerStmt loop (.popN owner count origin) le initial = Goose.Lower.emitEffect (.popN address amount (some origin)) le ls := by
    simp only [lowerStmt, bind_run, ownerRun, countRun]
  rw [whole]
  apply ready.emitEffect_live (.popN address amount (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (input live).1 (input live).2.1
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live
    trivial
  · intro live
    have delta := effectStep_popN_refines (module := module) (vt := vt) (count := amount) (origin := some origin) closed (effectRefinement_empty func before.eff) (input live).2.2
    rw [← sourceEffect] at delta
    exact delta.trans wholeEffect

theorem resizeWithoutFill {env : PEnv} {owner : Place} {size : Expr} {origin : OriginId}
    {initialSource ownerState before after : RState} {ownerRoots sizeRoots : List RootRef}
    {initial ownerLS : LS} {address amount : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, ownerState))
    (sizeReplay : rpExpr env size ownerState = .ok (sizeRoots, before))
    (source : rpStmt env (.resize owner size none origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (sizeRun : lowerExpr size le ownerLS = (amount, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ amount < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.resize owner size none origin) le initial).2 upper := by
  rw [rpStmt_resize_noFill_eq_popN] at source
  have sourceEffect := rpStmt_popN_effect ownerReplay sizeReplay source
  have whole : lowerStmt loop (.resize owner size none origin) le initial = Goose.Lower.emitEffect (.resize address amount none (some origin)) le ls := by
    simp only [lowerStmt, bind_run, ownerRun, sizeRun, pure_run]
  rw [whole]
  apply ready.emitEffect_live (.resize address amount none (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (input live).1 (input live).2.1
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live
    trivial
  · intro live
    have delta := effectStep_resize_refines (module := module) (vt := vt) (size := amount) (origin := some origin) (fill := none) closed (effectRefinement_empty func before.eff) (input live).2.2
    rw [← sourceEffect] at delta
    exact delta.trans wholeEffect

theorem resizeWithFill {env : PEnv} {owner : Place} {size fill : Expr} {origin : OriginId}
    {initialSource ownerState sizeState before after : RState} {ownerRoots sizeRoots fillRoots : List RootRef}
    {initial ownerLS sizeLS : LS} {address amount value : ValueId} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, ownerState))
    (sizeReplay : rpExpr env size ownerState = .ok (sizeRoots, sizeState))
    (fillReplay : rpExpr env fill sizeState = .ok (fillRoots, before))
    (source : rpStmt env (.resize owner size (some fill) origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (sizeRun : lowerExpr size le ownerLS = (amount, sizeLS))
    (fillRun : lowerExpr fill le sizeLS = (value, ls))
    (closed : ParameterRootsClosed func) (originBound : origin < le.mod.origins.size)
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ amount < ls.vals.size ∧ value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.resize owner size (some fill) origin) le initial).2 upper := by
  have sourceEffect := rpStmt_resize_fill_effect ownerReplay sizeReplay fillReplay source
  have whole : lowerStmt loop (.resize owner size (some fill) origin) le initial = Goose.Lower.emitEffect (.resize address amount (some value) (some origin)) le ls := by
    simp only [lowerStmt, bind_run, ownerRun, sizeRun, fillRun, pure_run]
  rw [whole]
  apply ready.emitEffect_live (.resize address amount (some value) (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (input live).1 (And.intro (input live).2.1 (input live).2.2.1)
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live
    trivial
  · intro live
    have delta := effectStep_resize_refines (module := module) (vt := vt) (size := amount) (origin := some origin) (fill := some value) closed (effectRefinement_empty func before.eff) (input live).2.2.2
    rw [← sourceEffect] at delta
    exact delta.trans wholeEffect

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
