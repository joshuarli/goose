import Goose.Lower.Validation.SummaryPreservationReplayTypedCall
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedCallNative {env : TEnv} {penv : PEnv} {calleeId : ContextId} {ctx : Context}
    {callee : Impl} {func : Func} {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {target : Core.Eff} {le : LEnv} {scopeCount : Nat} {slots : Array (List RootRef)}
    {ls : LS} {upper : Prov} {syntaxArgs : List Arg} {origin : OriginId}
    {start finish : Nat} {type : Ty} {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots ls upper)
    (tables : SourceRootTables env penv)
    (accepted : Core.validate penv.mod = .ok ())
    (contextLookup : penv.mod.contexts[calleeId]? = some ctx)
    (implLookup : penv.mod.impls[ctx.impl]? = some callee)
    (closed : ParameterRootsClosed func)
    (bounded : RootsBelow results (moduleTypedResultUpper penv.mod))
    (source : tyExpr env (.call calleeId syntaxArgs origin) start = .ok (type, finish))
    (replayed : rpExpr penv (.call calleeId syntaxArgs origin) before = .ok (sourceRoots, after))
    (wholeEffect : EffectRefinement func after.eff target)
    (originBound : origin < le.mod.origins.size) (calleeBound : calleeId < le.sigs.size)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerExpr (.call calleeId syntaxArgs origin) le ls).2)
    (argumentsChild : ∀ tn2 argumentRoots sourceAfter state provenance,
      tyArgs env callee callee.params.toList syntaxArgs start = .ok ((), tn2) →
      rpArgs penv syntaxArgs before = .ok (argumentRoots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots state provenance →
      state = ls → GeneratedBuilderState state →
      NativeRows vt (lowerArgs syntaxArgs le state).2 →
      ∃ next, ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots
          (lowerArgs syntaxArgs le state).2 next ∧
        ((lowerArgs syntaxArgs le state).2.cur.isSome = true →
          (lowerArgs syntaxArgs le state).1.length = syntaxArgs.length ∧
          ∀ (index : Nat) (value : ValueId), (lowerArgs syntaxArgs le state).1[index]? = some value →
            value < (lowerArgs syntaxArgs le state).2.vals.size ∧
            ∃ roots, argumentRoots[index]? = some roots ∧ RootsRefine func (rootsAt next.vals value) roots) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder (lower penv.mod) results vt func target le scopeCount slots
        (lowerExpr (.call calleeId syntaxArgs origin) le ls).2 next ∧
      ((lowerExpr (.call calleeId syntaxArgs origin) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.call calleeId syntaxArgs origin) le ls).2
          (lowerExpr (.call calleeId syntaxArgs origin) le ls).1 sourceRoots (.data type)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have contextTyped : env.mod.contexts[calleeId]? = some ctx := by
    simpa only [← tables.moduleEq] using contextLookup
  have implTyped : env.mod.impls[ctx.impl]? = some callee := by
    simpa only [← tables.moduleEq] using implLookup
  obtain ⟨arity, argumentCounter, typedArguments, resultTyped⟩ :=
    tyExpr_call_arguments contextTyped implTyped source
  have resultType := callResultTy_default resultTyped
  obtain ⟨argumentRoots, argumentState, argumentReplay, _tail⟩ := (st_bind_ok _ _ _ _).mp replayed
  have callReplay := (rpExpr_call_contract argumentReplay replayed).2
  have argumentEffect := effectRefinement_before_of_replay
    (PMono.rpCall penv calleeId argumentRoots) (PMonoRebinds.rpCall penv calleeId argumentRoots)
    (PFlagsMono.rpCall penv calleeId argumentRoots) callReplay wholeEffect
  have tailTypes (values : List ValueId) : TypeRun (do
      let returned ← Goose.Lower.emitDef (.call calleeId values (some origin))
      if (← read).mod.noReturn calleeId then Goose.Lower.emitTerm .unreachable
      pure returned) := by
    exact TypeRun.bind (types_emitDef _) fun returned => TypeRun.bind types_read fun environment => by
      cases environment.mod.noReturn calleeId <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact TypeRun.pure _ | exact TypeRun.bind (types_emitTerm _) fun _ => TypeRun.pure _
  have argumentNative : NativeRows vt (lowerArgs syntaxArgs le ls).2 :=
    native.of_prefix (tailTypes (lowerArgs syntaxArgs le ls).1 le (lowerArgs syntaxArgs le ls).2 _ _ rfl)
  obtain ⟨middle, argumentReady, argumentValues, argumentPrefix⟩ :=
    argumentsChild argumentCounter argumentRoots argumentState ls upper typedArguments argumentReplay argumentEffect ready rfl generated argumentNative
  let arguments := lowerArgs syntaxArgs le ls
  obtain ⟨next, completed, returned, retained⟩ := argumentReady.call accepted contextLookup implLookup
    closed bounded
    (fun live => (argumentValues live).1.trans arity)
    (fun live value member => by
      obtain ⟨index, row⟩ := List.mem_iff_getElem?.mp member
      exact ((argumentValues live).2 index value row).1)
    (fun live index value row => ((argumentValues live).2 index value row).2)
    originBound calleeBound (initial := ls) (syntaxArgs := syntaxArgs) rfl callReplay wholeEffect
  refine ⟨next, completed, ?_, ?_⟩
  · simpa only [resultType] using returned
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, argumentReady.roots.valueSize]
      exact (advB_lowerArgs syntaxArgs le ls arguments.1 arguments.2 rfl).vals
    exact (retained index (Nat.lt_of_lt_of_le bound growth)).trans (argumentPrefix index bound)

#print axioms typedCallNative

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
