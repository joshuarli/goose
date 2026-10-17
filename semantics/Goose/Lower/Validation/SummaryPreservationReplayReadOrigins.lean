import Goose.Lower.Validation.SourceReadablePlaceShape
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SummaryPreservationReplayScalarReadOrigins
import Goose.Lower.Validation.SummaryPreservationReplayContentReadOrigins
import Goose.Lower.Validation.SummaryPreservationReplayAcceptedReadOrigins

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem emitDef_current (op : Op) (le : LEnv) (ls : LS) :
    (Goose.Lower.emitDef op le ls).2.cur = ls.cur := by
  cases current : ls.cur with
  | none => rw [emitDef_none _ _ current]; exact current
  | some block => rw [emitDef_run _ _ current]; exact current

private theorem local_read_current (variableId : VarId) (le : LEnv) (ls : LS) :
    (lowerExpr (.read (.var variableId)) le ls).2.cur = ls.cur := by
  let slot := Goose.Lower.emitDef (.slotAddr variableId) le ls
  change (Goose.Lower.emitDef (.load slot.1) le slot.2).2.cur = ls.cur
  exact (emitDef_current _ _ _).trans (emitDef_current _ _ _)

namespace ReplayBuilder

theorem readExpressionWithOrigins {typingEnv : TEnv} {env : PEnv} {context : ContextId} {place : Place} {ty : Ty}
    {typingStart typingFinish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (typed : tyExpr typingEnv (.read place) typingStart = .ok (ty, typingFinish))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (source : rpExpr env (.read place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (placeStep : ∀ (info : PlaceInfo) (finish : Nat),
      tyPlace typingEnv place typingStart = .ok (info, finish) →
      ∀ roots state, rpPlace env place before = .ok (roots, state) →
      ∃ middle, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
          (typedContextSlotUpper env.mod env.ctx env.impl)
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 middle ∧
        ((lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt middle.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) roots) ∧
        ∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old)
    (resultType : (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
      vt[(lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size]? =
        some (some (.data ty)))
    (holderType : ∀ (variableId : VarId) (localVar : LocalVar),
      place = .deref (.read (.var variableId)) → typingEnv.vars[variableId]? = some localVar →
      localVar.ty.isRefSlice = true → ls.cur.isSome = true →
      vt[(lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1]? =
        some (some (.data localVar.ty))) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 sourceRoots (.data ty)) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∃ placeRoots placeAfter, rpPlace env place before = .ok (placeRoots, placeAfter) ∧
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) placeRoots) := by
  have accepted : Core.validate env.mod = .ok () := by
    simpa only [tables.moduleEq] using checked.accepted
  by_cases reference : ty.isRefLike = true
  · have shape := source_read_expression_shape checked typed reference
    rcases shape with ⟨variableId, localVar, rfl, variableRow, rfl⟩ |
      ⟨variableId, localVar, mu, sliceMu, element, rfl, variableRow, localType, rfl, elementFlat⟩
    · have actualRow : env.impl.vars[variableId]? = some localVar := by
        simpa only [tables.variablesEq] using variableRow
      obtain ⟨next, generated, value, growth, origins⟩ := ready.acceptedLocalReadWithOrigins accepted contextRow implementationRow
        actualRow source (by intro _ nonref; rw [reference] at nonref; cases nonref)
      exact ⟨next, generated, fun live => (value live).1, growth, origins⟩
    · have actualRow : env.impl.vars[variableId]? = some localVar := by
        simpa only [tables.variablesEq] using variableRow
      have refSlice : localVar.ty.isRefSlice = true := by simp [localType, Ty.isRefSlice, elementFlat]
      obtain ⟨param, parameter, identity, _⟩ := accepted_refSlice_parameter accepted implementationRow actualRow refSlice
      have parameterVariable : env.impl.vars[param.var]? = some localVar := by simpa only [identity] using actualRow
      have sourceParam : rpExpr env (.read (.deref (.read (.var param.var)))) before = .ok (sourceRoots, after) := by
        simpa only [identity] using source
      have addressTag : ls.cur.isSome = true → vt[(lowerExpr (.read (.var param.var))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1]? = some (some (.data localVar.ty)) := by
        intro live
        simpa only [identity] using holderType variableId localVar rfl variableRow refSlice live
      have contentTag : ls.cur.isSome = true → vt[(lowerExpr (.read (.var param.var))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size]? =
            some (some (.data (.slice sliceMu element))) := by
        intro live
        have placeLive : (lowerPlace (.deref (.read (.var variableId)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true := by
          simpa only [lowerPlace, local_read_current] using live
        simpa only [lowerPlace, identity] using resultType placeLive
      simpa only [identity] using ready.contentReadWithOrigins accepted contextRow implementationRow parameter parameterVariable
        refSlice sourceParam wholeEffect addressTag contentTag
  · have nonref : ty.isRefLike = false := by cases row : ty.isRefLike <;> simp_all
    obtain ⟨info, finish, placeTyped, _⟩ := tyExpr_read_place typed
    have sourceCopy := source
    simp only [rpExpr] at sourceCopy
    obtain ⟨roots, state, placeReplay, _⟩ := (st_bind_ok _ _ _ _).mp sourceCopy
    obtain ⟨middle, middleReady, input, middleGrowth⟩ := placeStep info finish placeTyped roots state placeReplay
    let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
    let address := lowerPlace place le ls
    obtain ⟨next, generated, value, nextGrowth, origins⟩ := middleReady.scalarReadWithOrigins ty nonref
      (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow) placeReplay source wholeEffect
      (placeRun := rfl) input resultType
    refine ⟨next, generated, value, ?_, ?_⟩
    · intro old bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, middleReady.roots.valueSize]
        exact (advB_lowerPlace place le ls address.1 address.2 rfl).vals
      exact (nextGrowth old (Nat.lt_of_lt_of_le bound growth)).trans (middleGrowth old bound)
    · intro live
      exact ⟨roots, state, placeReplay, origins live⟩

#print axioms readExpressionWithOrigins

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
