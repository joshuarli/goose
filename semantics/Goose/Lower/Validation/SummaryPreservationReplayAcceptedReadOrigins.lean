import Goose.Lower.Validation.SummaryPreservationReplayLocalReadOrigins
import Goose.Lower.Validation.SummaryPreservationTypedSlots
import Goose.Lower.Validation.SourceCanonicalRootFloorsMetadata

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

theorem refSliceReadRootCeiling_refines {env : PEnv} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef}
    (accepted : Core.validate env.mod = .ok ())
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (source : readRoots env (.var variableId) before = .ok (sourceRoots, after)) :
    RootsRefine (lowerContextAt env.mod env.ctx env.impl)
      (lowerValueRootCeiling env #[] (.refSliceVar variableId)) sourceRoots := by
  have refLike : localVar.ty.isRefLike = true := by
    cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
  cases annotation : env.ann variableId with
  | none =>
    simp only [readRoots, variableRow, refLike, ite_true, annotation] at source
    cases source
  | some roots =>
    have same : roots = sourceRoots := by
      have reading := source
      simp only [readRoots, variableRow, refLike, ite_true, annotation] at reading
      exact (congrArg Prod.fst ((st_pure_ok _ _ _).mp reading)).symm
    obtain ⟨param, parameterRow, identity, _⟩ :=
      accepted_refSlice_parameter accepted implementationRow variableRow reference
    have parameters := lowerContextAt_parameterRoots_eq (module := env.mod) parameterRow
      (by simpa only [PEnv.ann, identity] using annotation)
    intro root member
    simp only [lowerValueRootCeiling, annotation, Option.getD_some, parameterRow, Option.any_some,
      identity, beq_self_eq_true, ite_true] at member
    rcases unionRoots_mem _ _ _ member with literal | own
    · exact Or.inl (same ▸ literal)
    · have equal : root = .param variableId := List.mem_singleton.mp own
      subst root
      exact Or.inr (by simpa only [Func.expandParameterRoot, parameters, same] using
        (fun concrete (member : concrete ∈ sourceRoots) => member))

theorem refSliceReadRootCeiling_observed {env : PEnv} {context : ContextId}
    {variableId : VarId} {localVar : LocalVar}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (observed : (env.cont variableId).isSome = true) :
    lowerValueRootCeiling env #[] (.refSliceVar variableId) = [.param variableId] := by
  obtain ⟨impl, row, contextOk⟩ := (validate_modOk env.mod accepted).ctx context env.ctx contextRow
  rw [implementationRow] at row
  cases row
  obtain ⟨param, parameterRow, identity, _⟩ :=
    accepted_refSlice_parameter accepted implementationRow variableRow reference
  cases contents : env.cont variableId with
  | none => simp [contents] at observed
  | some roots =>
    have annotation := (contextOk.content variableId roots contents).2.1
    simp only [lowerValueRootCeiling, PEnv.ann, annotation, Option.getD_some, parameterRow,
      Option.any_some, identity, beq_self_eq_true, ite_true]
    simp [unionRoots]

namespace ReplayBuilder

theorem acceptedLocalReadWithOrigins {env : PEnv} {context : ContextId} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {siteRoot : DemandNode} {scopeCount : Nat} {ls : LS} {upper : Prov}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : rpExpr env (.read (.var variableId)) before = .ok (sourceRoots, after))
    (scalarType : ls.cur.isSome = true → localVar.ty.isRefLike = false →
      valRefLike vt (ls.vals.size + 1) = false)
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2) :
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
          if localVar.ty.isRefSlice then lowerValueRootCeiling env #[] (.refSliceVar variableId)
          else if valRefLike vt (ls.vals.size + 1) then
            rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId else []) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ((lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        ∃ placeRoots placeAfter, rpPlace env (.var variableId) before = .ok (placeRoots, placeAfter) ∧
          (lowerPlace (.var variableId) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 <
            (lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.vals.size ∧
          RootsRefine (lowerContextAt env.mod env.ctx env.impl)
            (rootsAt next.vals (lowerPlace (.var variableId) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1) placeRoots) ∧
      ((lowerExpr (.read (.var variableId)) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.cur.isSome = true →
        rootsAt next.vals (lowerPlace (.var variableId) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).1 =
          [.local variableId]) := by
  obtain ⟨found, foundRow, contextOk⟩ := (validate_modOk env.mod accepted).ctx context env.ctx contextRow
  rw [implementationRow] at foundRow
  cases Option.some.inj foundRow
  have readReplay : readRoots env (.var variableId) before = .ok (sourceRoots, after) := by
    simpa only [rpExpr_read_variable] using source
  have slotBound : variableId < (lowerEnv env.mod env.impl.vars env.impl.results.toList).slots.size := by
    simpa [lowerEnv] using (Array.getElem?_eq_some_iff.mp variableRow).1
  let chosen := if localVar.ty.isRefSlice then lowerValueRootCeiling env #[] (.refSliceVar variableId)
    else if valRefLike vt (ls.vals.size + 1) then
      rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId else []
  have included : ls.cur.isSome = true →
      (if valRefLike vt (ls.vals.size + 1) then
        rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId else []) ⊆ chosen := by
    intro live root member
    by_cases reference : localVar.ty.isRefSlice = true
    · obtain ⟨param, parameterRow, identity, _⟩ :=
        accepted_refSlice_parameter accepted implementationRow variableRow reference
      simp only [chosen, reference, ite_true, typedContextSlotUpper_at variableRow] at *
      split at member
      · have equal : root = .param variableId := List.mem_singleton.mp member
        subst root
        simp only [lowerValueRootCeiling, parameterRow, Option.any_some, identity, beq_self_eq_true, ite_true]
        exact unionRoots_right _ _ _ (by simp)
      · cases member
    · simpa only [chosen, reference, Bool.false_eq_true, ite_false] using member
  have refined : ls.cur.isSome = true → RootsRefine (lowerContextAt env.mod env.ctx env.impl) chosen sourceRoots := by
    intro live
    by_cases reference : localVar.ty.isRefSlice = true
    · simpa only [chosen, reference, ite_true] using
        refSliceReadRootCeiling_refines accepted implementationRow variableRow reference readReplay
    · simp only [chosen, reference, Bool.false_eq_true, ite_false]
      by_cases like : localVar.ty.isRefLike = true
      · cases annotation : env.ann variableId with
        | none =>
          have reading := readReplay
          simp only [readRoots, variableRow, like, ite_true, annotation] at reading
          cases reading
        | some roots =>
          have sourceEq : roots = sourceRoots := by
            have reading := readReplay
            simp only [readRoots, variableRow, like, ite_true, annotation] at reading
            exact (congrArg Prod.fst ((st_pure_ok _ _ _).mp reading)).symm
          split
          · simpa only [annotation, Option.getD_some, sourceEq] using
              typedContextSlotUpper_local_read_refines accepted implementationRow variableRow readReplay
          · intro root member; cases member
      · have nonref : localVar.ty.isRefLike = false := Bool.eq_false_iff.mpr like
        simp only [scalarType live nonref, Bool.false_eq_true, ite_false]
        intro root member; cases member
  have scalar : ls.cur.isSome = true → localVar.ty.isRefLike = false → chosen = [] := by
    intro live nonref
    have ordinary : localVar.ty.isRefSlice = false := by
      cases ty : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
    simp [chosen, ordinary, scalarType live nonref]
  obtain ⟨next, generated, value, growth, origins, physical⟩ := ready.localReadWithOrigins
    variableRow source slotBound chosen included refined scalar (by
      intro value afterLoad run tag recorded row member same
      have tagInfo := recordReadValueRootRecipe_push_source value variableId
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) afterLoad tag recorded
      have reference : localVar.ty.isRefSlice = true := by
        simpa only [lowerEnv, variableRow, Option.any_some] using tagInfo.2
      have whole : lowerExpr (.read (.var variableId))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls =
          (value, (Goose.Lower.recordReadValueRootRecipe value (.var variableId)
            (lowerEnv env.mod env.impl.vars env.impl.results.toList) afterLoad).2) := by
        simp only [lowerExpr, lowerPlace, bind_run, run, pure_run]
      have added : (value, tag) ∈ (lowerExpr (.read (.var variableId))
          (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2.valueRootRecipes := by
        rw [whole, recorded]
        exact Array.mem_push_self
      have rowMember : (value, row.2) ∈ (lowerContextAt env.mod env.ctx env.impl).roots.values.getD #[] := by
        simpa only [← same, Prod.eta] using member
      have exactRow := metadata.project (value, tag) added row.2 rowMember
      rw [exactRow, tagInfo.1]
      change lowerValueRootCeiling env (SourceCanonicalRootFloors.sourceNodeRootTable env siteRoot)
          (.refSliceVar variableId) ⊆ chosen ∧ chosen ⊆
        lowerValueRootCeiling env (SourceCanonicalRootFloors.sourceNodeRootTable env siteRoot)
          (.refSliceVar variableId)
      simp only [chosen, reference, ite_true]
      exact ⟨fun _ member => member, fun _ member => member⟩)
  exact ⟨next, generated, value, growth, origins, physical⟩

#print axioms acceptedLocalReadWithOrigins

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
