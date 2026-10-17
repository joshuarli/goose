import Goose.Lower.Validation.SummaryPreservationReplayLocalReadOrigins
import Goose.Lower.Validation.SummaryPreservationTypedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem typedContextSlotUpper_local_read_refines {env : PEnv} {implementation : ImplId}
    {variableId : VarId} {localVar : LocalVar} {before after : RState} {sourceRoots : List RootRef}
    (accepted : Core.validate env.mod = .ok ())
    (implementationRow : env.mod.impls[implementation]? = some env.impl)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : readRoots env (.var variableId) before = .ok (sourceRoots, after)) :
    RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId)
      (env.ann variableId |>.getD []) := by
  by_cases reference : localVar.ty.isRefSlice = true
  · have refLike : localVar.ty.isRefLike = true := by
      cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
    cases annotation : env.ann variableId with
    | none =>
      simp only [readRoots, variableRow, refLike, ite_true, annotation] at source
      cases source
    | some roots =>
      have refined := typedContextSlotUpper_refines accepted implementationRow variableRow annotation
      simpa only [annotation, Option.getD_some] using refined
  · rw [typedContextSlotUpper_at variableRow, if_neg reference]
    exact refinedResultUpper_refines _ _

namespace ReplayBuilder

theorem acceptedLocalReadWithOrigins {env : PEnv} {context : ContextId} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : rpExpr env (.read (.var variableId)) before = .ok (sourceRoots, after))
    (scalarType : ls.cur.isSome = true → localVar.ty.isRefLike = false →
      valRefLike vt (ls.vals.size + 1) = false) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      ((lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ReplayValue (lowerContextAt env.mod env.ctx env.impl) next
          (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
          (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1
          sourceRoots (.data localVar.ty) ∧
        rootsAt next.vals (lowerExpr (.read (.var variableId))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 =
          if valRefLike vt (lowerExpr (.read (.var variableId))
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 then
            rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId else []) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ((lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∃ placeRoots placeAfter, rpPlace env (.var variableId) before = .ok (placeRoots, placeAfter) ∧
          (lowerPlace (.var variableId) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerPlace (.var variableId) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) placeRoots) := by
  obtain ⟨found, foundRow, contextOk⟩ := (validate_modOk env.mod accepted).ctx context env.ctx contextRow
  rw [implementationRow] at foundRow
  cases Option.some.inj foundRow
  have readReplay : readRoots env (.var variableId) before = .ok (sourceRoots, after) := by
    simpa only [rpExpr_read_variable] using source
  have slotBound : variableId < (lowerEnv env.mod env.impl.vars env.impl.results.toList).slots.size := by
    simpa [lowerEnv] using (Array.getElem?_eq_some_iff.mp variableRow).1
  obtain ⟨next, generated, value, growth, origins⟩ := ready.localReadWithOrigins contextOk.annotationShape variableRow source
    slotBound (typedContextSlotUpper_local_read_refines accepted implementationRow variableRow readReplay) scalarType
  exact ⟨next, generated, value, growth, origins⟩

#print axioms acceptedLocalReadWithOrigins

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
