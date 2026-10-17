import Goose.Lower.Validation.SummaryPreservationReplayAcceptedRead

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

theorem referenceSlicePlace {env : PEnv} {context : ContextId} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : rpPlace env (.deref (.read (.var variableId))) before = .ok (sourceRoots, after)) :
    variableId < env.impl.params.size ∧ env.isRefSliceVar variableId = true ∧
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerPlace (.deref (.read (.var variableId)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerPlace (.deref (.read (.var variableId)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        (lowerPlace (.deref (.read (.var variableId)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
          (lowerPlace (.deref (.read (.var variableId)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
        RootsRefine (lowerContextAt env.mod env.ctx env.impl)
          (rootsAt next.vals (lowerPlace (.deref (.read (.var variableId)))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) sourceRoots ∧
        ∀ root ∈ rootsAt next.vals (lowerPlace (.deref (.read (.var variableId)))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1,
            root ∈ [RootRef.param variableId]) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨param, parameterRow, _identity, _mode⟩ :=
    accepted_refSlice_parameter accepted implementationRow variableRow reference
  have refLike : localVar.ty.isRefLike = true := by
    cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
  obtain ⟨next, nextReady, value, retained⟩ := ready.acceptedLocalRead accepted contextRow
    implementationRow variableRow (show rpExpr env (.read (.var variableId)) before =
      .ok (sourceRoots, after) from source)
    (by intro _ nonref; rw [refLike] at nonref; cases nonref)
  refine ⟨(Array.getElem?_eq_some_iff.mp parameterRow).1, ?_, next, nextReady, ?_, retained⟩
  · simp [PEnv.isRefSliceVar, variableRow, reference]
  · intro live
    obtain ⟨typed, raw⟩ := value live
    refine ⟨typed.bound, typed.refined, ?_⟩
    intro root member
    change root ∈ rootsAt next.vals (lowerExpr (.read (.var variableId))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 at member
    rw [raw, typedContextSlotUpper_at variableRow, if_pos reference] at member
    split at member
    · exact member
    · cases member

#print axioms referenceSlicePlace

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
