import Goose.Lower.Validation.SummaryPreservationReplayMutationsEmit
import Goose.Lower.Validation.SummaryPreservationAppendSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_push_after_operands {env : PEnv} {owner : Place} {expression : Expr}
    {origin : Option OriginId} {initial ownerState before : RState}
    {ownerRoots valueRoots : List RootRef} {limited : Bool}
    (ownerReplay : rpPlace env owner initial = .ok (ownerRoots, ownerState))
    (valueReplay : rpExpr env expression ownerState = .ok (valueRoots, before))
    (limitedRun : env.limitedOwner owner = .ok limited) :
    rpExpr env (.push owner expression origin) initial = .ok (ownerRoots,
      if env.mod.profile == .shrink then
        { before with eff := { before.eff with
          grows := addTargets before.eff.grows (rootsTargets ownerRoots)
          writes := addTargets before.eff.writes (rootsTargets ownerRoots)
          aborts := before.eff.aborts || limited } }
      else { before with eff := { before.eff with grows := addTargets before.eff.grows (rootsTargets ownerRoots) } }) := by
  cases profile : env.mod.profile <;> cases limited <;>
    simp [rpExpr, ownerReplay, valueReplay, profile, limitedRun, liftV, addGrows, addWrites,
      addRoots, noteAborts, bind, pure, modify, Except.bind, Except.pure, StateT.bind,
      StateT.pure, StateT.modifyGet, modifyGet, MonadStateOf.modifyGet] <;> rfl

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem push {env : PEnv} {owner : Place} {expression : Expr} {origin : Option OriginId} {element ownerType : Ty}
    {initialSource ownerState before after : RState} {ownerRoots valueRoots sourceRoots : List RootRef}
    {initial ownerLS : LS} {address value : ValueId} {mutability : Mutability}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, ownerState))
    (valueReplay : rpExpr env expression ownerState = .ok (valueRoots, before))
    (source : rpExpr env (.push owner expression origin) initialSource = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (valueRun : lowerExpr expression le ownerLS = (value, ls))
    (closed : ParameterRootsClosed func) (profile : module.profile = env.mod.profile)
    (originBound : ∀ candidate, origin = some candidate → candidate < le.mod.origins.size)
    (sourceType : env.access.placeType? owner = some ownerType)
    (actualType : ls.cur.isSome = true → vt[address]? = some (some (.data (.ref mutability ownerType))))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.push owner expression origin) le initial).2 next ∧
      ((lowerExpr (.push owner expression origin) le initial).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.push owner expression origin) le initial).2
          (lowerExpr (.push owner expression origin) le initial).1 sourceRoots (.data (.ref .mutable element))) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have whole : lowerExpr (.push owner expression origin) le initial = Goose.Lower.emitDef (.push address value origin) le ls := by
    simp only [lowerExpr, bind_run, ownerRun, valueRun]
  rw [whole]
  cases current : ls.cur with
  | none =>
    rw [emitDef_none _ _ current]
    exact ⟨upper, ready, by simp [current], fun _ _ => rfl⟩
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    have limited := limitedOwner_matches_valueType sourceType (actualType live)
    rw [rpExpr_push_after_operands ownerReplay valueReplay limited] at source
    cases source
    apply ready.emitTypedDef_live (.push address value origin) ownerRoots (.data (.ref .mutable element))
    · intro live
      simpa [Op.uses] using And.intro (input live).1 (input live).2.1
    · simpa [Op.origin] using originBound
    · simp [Op.SymbolRefsValid]
    · intro live
      have delta := effectStep_push_refines (module := module) (vt := vt) (result := ls.vals.size)
        (value := value) (origin := origin) closed (effectRefinement_empty func before.eff) (input live).2.2 rfl
      rw [profile] at delta
      by_cases shrink : (env.mod.profile == .shrink) = true <;>
        simp only [shrink, reduceIte] at delta wholeEffect <;> exact delta.trans wholeEffect
    · intro live
      exact (input live).2.2
    · intros
      simp [VTy.refLike, Ty.isRefLike] at *

theorem append {env : PEnv} {owner : Place} {view : View} {origin : OriginId} {ownerType : Ty}
    {initialSource ownerState before after : RState} {ownerRoots viewRoots : List RootRef}
    {initial ownerLS : LS} {address value : ValueId} {mutability : Mutability} (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (ownerReplay : rpPlace env owner initialSource = .ok (ownerRoots, ownerState))
    (viewReplay : rpView env view ownerState = .ok (viewRoots, before))
    (source : rpStmt env (.append owner view origin) initialSource = .ok ((), after))
    (wholeEffect : EffectRefinement func after.eff target)
    (ownerRun : lowerPlace owner le initial = (address, ownerLS))
    (viewRun : lowerView view le ownerLS = (value, ls))
    (closed : ParameterRootsClosed func) (profile : module.profile = env.mod.profile)
    (originBound : origin < le.mod.origins.size)
    (sourceType : env.access.placeType? owner = some ownerType)
    (actualType : ls.cur.isSome = true → vt[address]? = some (some (.data (.ref mutability ownerType))))
    (input : ls.cur.isSome = true → address < ls.vals.size ∧ value < ls.vals.size ∧
      RootsRefine func (rootsAt upper.vals address) ownerRoots ∧ RootsRefine func (rootsAt upper.vals value) viewRoots) :
    ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.append owner view origin) le initial).2 upper := by
  have whole : lowerStmt loop (.append owner view origin) le initial = Goose.Lower.emitEffect (.append address value (some origin)) le ls := by
    simp only [lowerStmt, bind_run, ownerRun, viewRun]
  rw [whole]
  apply ready.emitEffect_live (.append address value (some origin))
  · intro live
    apply Inst.SymbolsWithin.eff
    · simpa [Effect.uses] using And.intro (input live).1 (input live).2.1
    · simpa [Effect.origin] using originBound
    · trivial
  · intro live
    trivial
  · intro live
    have sourceEffect := rpStmt_append_effect ownerReplay viewReplay
      (limitedOwner_matches_valueType sourceType (actualType live)) source
    have delta := effectStep_append_refines (module := module) (vt := vt) (origin := some origin)
      closed (effectRefinement_empty func before.eff) (input live).2.2.1 (input live).2.2.2 rfl
    rw [profile, ← sourceEffect] at delta
    exact delta.trans wholeEffect

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
