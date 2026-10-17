import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadLocal
import Goose.Lower.Validation.SummaryPreservationReplayNativeTypes

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {context : ContextId} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}
  {siteRoot : DemandNode} {siteTargets : List BlockId} {index : VarId}
  {before after : RState} {sourceRoots : List RootRef}

theorem contextArgumentVariablePlace {info : PlaceInfo} {start finish : Nat}
    (source : SourceContextEnvironment typingEnv env context)
    (typed : tyPlace typingEnv (.var index) start = .ok (info, finish))
    (replay : rpPlace env (.var index) before = .ok (sourceRoots, after))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl) (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 < (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt next.vals (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots ∧
        rootsAt next.vals (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 = [.local index]) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.place (.var index)) (lowerContextAt env.mod env.ctx env.impl) vt next initial (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace (.var index) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  have slotBound : index < le.slots.size := by
    simpa only [le, lowerEnv, Array.size_mapIdx, source.tables.variablesEq] using
      Core.tyPlace_var_success_bound typed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj replay)
  obtain ⟨next, completed, value, retained⟩ := ready.emitDef (.slotAddr index) [.local index]
    (by simp [Op.uses]) (by simp [Op.origin]) slotBound
    (effectRefinement_empty _ _) (GIR.RootsRefine.refl _ _)
  have emitted : OccurrenceLedger env (.place (.var index)) (lowerContextAt env.mod env.ctx env.impl) vt next
      initial (lowerPlace (.var index) le initial).2 :=
    emitsOnly_emitDef rfl (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands])
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, completed.roots.valueSize]
    exact (advB_lowerPlace (.var index) le initial _ _ rfl).vals
  exact ⟨next, completed, fun live => ⟨(value live).1, (value live).2.2, (value live).2.1⟩,
    retained, emitted, sites.of_emits (emitsOnly_emitDef rfl trivial)
      (types_lowerPlace (.var index) le initial _ _ rfl)
      (.of_run (generatedTargetFrame_lowerPlace none (.var index)) rfl) growth retained⟩

theorem contextArgumentReferencePlace {localVar : LocalVar}
    (source : SourceContextEnvironment typingEnv env context)
    (variableRow : env.impl.vars[index]? = some localVar) (reference : localVar.ty.isRefSlice = true)
    (contents : (env.cont index).isSome = true)
    (replay : rpPlace env (.deref (.read (.var index))) before = .ok (sourceRoots, after))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) initial upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial
      (lowerContextAt env.mod env.ctx env.impl) vt upper)
    (metadata : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerPlace (.deref (.read (.var index)))
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl) (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 next ∧
      ((lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true →
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 < (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals.size ∧
        GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl) (rootsAt next.vals (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots ∧
        rootsAt next.vals (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 = [.param index]) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env (.place (.deref (.read (.var index)))) (lowerContextAt env.mod env.ctx env.impl) vt next initial (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerPlace (.deref (.read (.var index))) (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 (lowerContextAt env.mod env.ctx env.impl) vt next := by
  have refLike : localVar.ty.isRefLike = true := by
    cases type : localVar.ty <;> simp_all [Ty.isRefLike, Ty.isRefSlice]
  have annotation : env.ann index = some [.param index] := by
    cases found : env.ctx.contentRoots.find? (·.1 == index) with
    | none => simp [PEnv.cont, found] at contents
    | some row =>
      have identity : row.1 = index := by simpa using List.find?_some found
      obtain ⟨_, localVar, _, _, annotation, _⟩ := Core.Declarative.declaredContents_sound
        env.mod env.impl env.ctx source.contextOk.contentShape row.1 row.2
          (List.mem_of_find?_eq_some found)
      simpa only [PEnv.ann, identity] using annotation
  have sourceExact : sourceRoots = [.param index] := by
    have sourceRead : readRoots env (.var index) before = .ok (sourceRoots, after) := by
      simpa only [rpExpr_read_variable] using
        (show rpExpr env (.read (.var index)) before = .ok (sourceRoots, after) from replay)
    simp only [readRoots, variableRow, refLike, ite_true, annotation] at sourceRead
    exact (congrArg Prod.fst (Except.ok.inj sourceRead)).symm
  obtain ⟨next, completed, value, retained, origins, physical⟩ := ready.acceptedLocalReadWithOrigins
    source.accepted source.contextRow source.implementationRow variableRow
    (show rpExpr env (.read (.var index)) before = .ok (sourceRoots, after) from replay)
    (by intro _ nonref; rw [refLike] at nonref; cases nonref) metadata
  refine ⟨next, completed, ?_, retained,
    accessLocalReadLedger (accessChildNode 0 rfl) replay completed.roots.valueSize
      (fun live => (value live).1) origins physical,
    accessLocalReadSites ready completed sites retained⟩
  intro live
  obtain ⟨returned, raw⟩ := value live
  have exactRoots : rootsAt next.vals (lowerExpr (.read (.var index))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1 = [.param index] := by
    have cap := refSliceReadRootCeiling_observed source.accepted source.contextRow
      source.implementationRow variableRow reference contents
    simpa only [reference, ite_true, cap] using raw
  refine ⟨returned.bound, ?_, exactRoots⟩
  change GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl)
    (rootsAt next.vals (lowerExpr (.read (.var index))
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1) sourceRoots
  rw [exactRoots, sourceExact]
  exact GIR.RootsRefine.refl _ _

#print axioms contextArgumentVariablePlace
#print axioms contextArgumentReferencePlace

end Goose.Lower.Validation.ReplacementContentFlowSource
