import Goose.Lower.Validation.SummaryPreservationReplayRead
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes
import Goose.Lower.Validation.SummaryPreservationSourceEffectCeiling

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem retainedCur_emitDef (op : Op) (le : LEnv) (ls : LS) :
    (Goose.Lower.emitDef op le ls).2.cur = ls.cur := by
  cases active : ls.cur with
  | none => rw [emitDef_none _ _ active]; exact active
  | some block => rw [emitDef_run _ _ active]; exact active

private theorem retainedCur_localRead (variableId : VarId) (le : LEnv) (ls : LS) :
    (lowerExpr (.read (.var variableId)) le ls).2.cur = ls.cur :=
  (retainedCur_emitDef _ _ _).trans (retainedCur_emitDef _ _ _)

namespace ReplayBuilder

theorem typedRead {typingEnv : TEnv} {env : PEnv} {context : ContextId} {place : Place} {type : Ty}
    {start finish : Nat} {before after : RState} {sourceRoots : List RootRef}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {ls : LS} {upper : Prov}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (source : tyExpr typingEnv (.read place) start = .ok (type, finish))
    (replayed : rpExpr env (.read place) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.read place)
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (placeChild : ∀ info tn2 roots state,
      tyPlace typingEnv place start = .ok (info, tn2) →
      rpPlace env place before = .ok (roots, state) →
      EffectRefinement (lowerContextAt env.mod env.ctx env.impl) state.eff target →
      ∃ middle, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
          (typedContextSlotUpper env.mod env.ctx env.impl)
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 middle ∧
        ((lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
          (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt middle.vals (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) roots) ∧
        ∀ old, old < upper.vals.size → rootsAt middle.vals old = rootsAt upper.vals old) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read place) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 sourceRoots (.data type)) ∧
      ∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  have lowerEnvironment : lowerEnv typingEnv.mod typingEnv.vars env.impl.results.toList = le := by
    rw [← tables.moduleEq, ← tables.variablesEq]
  have resultTag (live : (lowerExpr (.read place) le ls).2.cur.isSome = true) :
      vt[(lowerExpr (.read place) le ls).1]? = some (some (.data type)) := by
    apply native.expression generated source
    · rw [lowerEnvironment]
    · exact live
  apply ready.readExpression checked tables contextRow implementationRow source replayed wholeEffect
  · intro info tn2 typedPlace roots state placeReplay
    have rootReplay := replayed
    obtain ⟨_, _, first, tail⟩ := (st_bind_ok _ _ _ _).mp rootReplay
    rw [placeReplay] at first
    cases first
    have effectBound := effectRefinement_before_of_replay
      (PMono.bind (PMono.addReads roots) (fun _ => PMono.readRoots env place))
      (PMonoRebinds.bind (PMonoRebinds.addReads roots) (fun _ => PMonoRebinds.readRoots env place))
      (PFlagsMono.bind (PFlagsMono.addReads roots) (fun _ => PFlagsMono.readRoots env place)) tail wholeEffect
    exact placeChild info tn2 roots state typedPlace placeReplay effectBound
  · intro active
    let address := lowerPlace place le ls
    have whole : lowerExpr (.read place) le ls = Goose.Lower.emitDef (.load address.1) le address.2 := by
      simp only [lowerExpr, bind_run]
      rfl
    have addressLive : address.2.cur.isSome = true := active
    have live : (lowerExpr (.read place) le ls).2.cur.isSome = true := by
      rw [whole, retainedCur_emitDef]
      exact active
    have tag := resultTag live
    have fresh : (lowerExpr (.read place) le ls).1 = address.2.vals.size := by
      rw [whole]
      cases current : address.2.cur with
      | none => simp [current] at addressLive
      | some block => rw [emitDef_run _ _ current]
    simpa only [fresh] using tag
  · intro variableId localVar shape variableRow _reference live
    subst place
    let holder := lowerExpr (.read (.var variableId)) le ls
    have nativeHolder : NativeRows vt holder.2 := by
      apply native.of_prefix
      exact types_emitDef (.load holder.1) le holder.2 _ _ rfl
    have holderLive : holder.2.cur.isSome = true := by
      rw [retainedCur_localRead]
      exact live
    apply nativeHolder.local_read (by simpa only [tables.variablesEq] using variableRow) holderLive

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
