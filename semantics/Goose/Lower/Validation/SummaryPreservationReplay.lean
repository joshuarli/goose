import Goose.Lower.Validation.SummaryPreservationEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem targetsWithin_of_subset (func : Func) (what : String) {found declared : List Target}
    (subset : ∀ target ∈ found, target ∈ declared) :
    func.targetsWithin what found declared = .ok () := by
  unfold Func.targetsWithin
  have absent : found.find? (fun target => !declared.contains target) = none := by
    apply List.find?_eq_none.mpr
    intro target member
    simpa using subset target member
  rw [absent]
  rfl

theorem flagWithin_of_imp (message : String) {found declared : Bool}
    (allowed : found = true → declared = true) :
    Func.flagWithin message found declared = .ok () := by
  cases found <;> cases declared <;> simp_all [Func.flagWithin] <;> rfl

theorem checkSummary_lowerContextAt {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {effect : Core.Eff}
    (accepted : validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (checked : checkSummary module impl ctx effect = .ok ()) :
    (lowerContextAt module ctx impl).summaryClosed effect = .ok () := by
  let func := lowerContextAt module ctx impl
  cases known : impl.summary with
  | unknown =>
    simp [Func.summaryClosed, lowerContextAt, lowerImpl, known]
    rfl
  | known summary =>
    have source := sourceEffects_of_checkSummary checked known
    have allBounds := checkSummary_target_bounds checked known
    have closed := lowerContextAt_parameterRoots_closed accepted contextLookup implLookup
    have normalized {found declared : List Target}
        (within : ∀ target ∈ found, target ∈ expandTargets impl ctx declared)
        (bounds : ∀ target ∈ declared, Target.Within module impl target) :
        ∀ target ∈ func.storageTargets found, target ∈ func.storageTargets declared := by
      intro target member
      have mapped := storageTargets_mono (func := func) within target member
      rw [← lowerContextAt_storageTargets_eq accepted contextLookup implLookup bounds] at mapped
      exact storageTargets_idempotent closed target mapped
    have reads := targetsWithin_of_subset func "reads" (normalized source.reads
      (fun target member => allBounds target (by simp [member])))
    have writes := targetsWithin_of_subset func "writes" (normalized source.writes
      (fun target member => allBounds target (by simp [member])))
    have grows := targetsWithin_of_subset func "grows" (normalized source.grows
      (fun target member => allBounds target (by simp [member])))
    have shrinks := targetsWithin_of_subset func "shrinks" (normalized source.shrinks
      (fun target member => allBounds target (by simp [member])))
    have rebinds := targetsWithin_of_subset func "rebinds" source.rebinds
    have unknown : func.noUnknownCallee effect.unknown = .ok () := by
      simp [Func.noUnknownCallee, source.unknown]
      rfl
    have aborts := flagWithin_of_imp s!"{func.name} may abort, which its summary omits" source.aborts
    have outputs := flagWithin_of_imp s!"{func.name} prints, which its summary omits" source.outputs
    have functionSummary : func.summary = .known summary := known
    change func.summaryClosed effect = .ok ()
    simp only [Func.summaryClosed, functionSummary]
    change (do
      func.noUnknownCallee effect.unknown
      func.targetsWithin "reads" (func.storageTargets effect.reads) (func.storageTargets summary.reads)
      func.targetsWithin "writes" (func.storageTargets effect.writes) (func.storageTargets summary.writes)
      func.targetsWithin "grows" (func.storageTargets effect.grows) (func.storageTargets summary.grows)
      func.targetsWithin "shrinks" (func.storageTargets effect.shrinks) (func.storageTargets summary.shrinks)
      func.targetsWithin "rebinds" effect.rebinds summary.rebinds
      Func.flagWithin s!"{func.name} may abort, which its summary omits" effect.aborts summary.aborts
      Func.flagWithin s!"{func.name} prints, which its summary omits" effect.outputs summary.outputs) = .ok ()
    rw [unknown, reads, writes, grows, shrinks, rebinds, aborts, outputs]
    rfl

theorem accepted_context_replayedSummaryClosed {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    ∃ roots range state,
      rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
        .ok ((roots, range), state) ∧
      (lowerContextAt module ctx impl).summaryClosed state.eff = .ok () := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  obtain ⟨roots, range, state, body, _, summary⟩ := checked.body
  exact ⟨roots, range, state, body,
    checkSummary_lowerContextAt accepted contextLookup implLookup summary⟩

end Goose.Lower.Validation.SummaryPreservation
