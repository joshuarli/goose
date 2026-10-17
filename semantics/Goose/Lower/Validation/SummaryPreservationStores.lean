import Goose.Lower.Validation.SummaryPreservationRefinedEffects
import Goose.Lower.Validation.SummaryPreservationTypedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContext_slot {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : SlotId} {localVar : LocalVar} (lookup : impl.vars[slot]? = some localVar) :
    (lowerContextAt module ctx impl).slots[slot]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
  simp [lowerContextAt, lowerImpl, lowerEnv, Array.getElem?_mapIdx, lookup]


theorem RootsRefine.local_member {func : Func} {actual source : List RootRef} {slot : SlotId}
    (refined : RootsRefine func actual source) (member : RootRef.local slot ∈ actual) :
    RootRef.local slot ∈ source := by
  rcases refined (.local slot) member with literal | expanded
  · exact literal
  · exact expanded (.local slot) (by simp [Func.expandParameterRoot])


theorem effectStep_store_nonSlice_no_rebinds {module : Core.Module} {ctx : Context} {impl : Impl}
    {vt : Array (Option VTy)} {provenance : Prov} {address value : ValueId} {origin : OriginId}
    {sourceRoots : List RootRef}
    (roots : RootsRefine (lowerContextAt module ctx impl)
      (rootsAt provenance.vals address) sourceRoots)
    (locals : ∀ slot, RootRef.local slot ∈ sourceRoots →
      ∃ localVar, impl.vars[slot]? = some localVar ∧ localVar.ty.isRefLike = false)
    (owner : (ownerTy vt address).any Ty.isSlice = false) :
    ((lowerContextAt module ctx impl).effectStep (lower module) vt provenance {}
      (.eff (.store address value origin))).rebinds = [] := by
  simp only [Func.effectStep]
  change addTargets [] _ = addTargets [] []
  apply congrArg (addTargets [])
  apply List.filterMap_eq_nil_iff.mpr
  intro root member
  cases root with
  | «local» slot =>
    obtain ⟨localVar, variableRow, nonReference⟩ := locals slot (roots.local_member member)
    simp [lowerContext_slot variableRow, nonReference]
  | param index =>
    cases lookup : (lowerContextAt module ctx impl).params[index]? <;> simp [lookup, owner]
  | global global => rfl


theorem effectStep_store_nonSlice_refines {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {vt : Array (Option VTy)} {provenance : Prov}
    {address value : ValueId} {origin : OriginId} {sourceRoots : List RootRef} {source : Core.Eff}
    (accepted : Core.validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (roots : RootsRefine (lowerContextAt module ctx impl)
      (rootsAt provenance.vals address) sourceRoots)
    (locals : ∀ slot, RootRef.local slot ∈ sourceRoots →
      ∃ localVar, impl.vars[slot]? = some localVar ∧ localVar.ty.isRefLike = false)
    (owner : (ownerTy vt address).any Ty.isSlice = false) :
    EffectRefinement (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).effectStep (lower module) vt provenance {}
        (.eff (.store address value origin)))
      { source with writes := addTargets source.writes (rootsTargets sourceRoots) } := by
  have closed := lowerContextAt_parameterRoots_closed accepted contextLookup implLookup
  have noRebind := effectStep_store_nonSlice_no_rebinds (value := value) (origin := origin) roots locals owner
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Func.effectStep, Func.storageTargets]
  · intro target member
    change target ∈ (lowerContextAt module ctx impl).storageTargets
      (addTargets [] (rootsTargets (rootsAt provenance.vals address))) at member
    rcases storageTargets_addTargets_origin member with empty | actual
    · simp [Func.storageTargets] at empty
    · exact storageTargets_mono (fun t h => addTargets_right _ _ t h) target
        (roots.targets closed target actual)
  · simp [Func.effectStep, Func.storageTargets]
  · simp [Func.effectStep, Func.storageTargets]
  · intro target member
    rw [noRebind] at member
    cases member
  · simp [Func.effectStep]
  · simp [Func.effectStep]
  · simp [Func.effectStep]

end Goose.Lower.Validation.SummaryPreservation
