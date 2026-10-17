import Goose.Lower.Validation.SummaryPreservationEffectRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem refined_checkSummary_lowerContextAt {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {effect actual : Core.Eff}
    (accepted : validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (checked : checkSummary module impl ctx effect = .ok ())
    (refined : EffectRefinement (lowerContextAt module ctx impl) actual effect) :
    (lowerContextAt module ctx impl).summaryClosed actual = .ok () := by
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
    have reads := targetsWithin_of_subset func "reads" (fun target member =>
      normalized source.reads
        (fun target member => allBounds target (by simp [member])) target
        (refined.reads target member))
    have writes := targetsWithin_of_subset func "writes" (fun target member =>
      normalized source.writes
        (fun target member => allBounds target (by simp [member])) target
        (refined.writes target member))
    have grows := targetsWithin_of_subset func "grows" (fun target member =>
      normalized source.grows
        (fun target member => allBounds target (by simp [member])) target
        (refined.grows target member))
    have shrinks := targetsWithin_of_subset func "shrinks" (fun target member =>
      normalized source.shrinks
        (fun target member => allBounds target (by simp [member])) target
        (refined.shrinks target member))
    have rebinds := targetsWithin_of_subset func "rebinds" (fun target member => source.rebinds target (refined.rebinds target member))
    have unknown : func.noUnknownCallee actual.unknown = .ok () := by
      have absent : actual.unknown = false := by
        cases h : actual.unknown
        · rfl
        · have impossible := refined.unknown h
          simp [source.unknown] at impossible
      simp [Func.noUnknownCallee, absent]
      rfl
    have aborts := flagWithin_of_imp s!"{func.name} may abort, which its summary omits" (fun h => source.aborts (refined.aborts h))
    have outputs := flagWithin_of_imp s!"{func.name} prints, which its summary omits" (fun h => source.outputs (refined.outputs h))
    have functionSummary : func.summary = .known summary := known
    change func.summaryClosed actual = .ok ()
    simp only [Func.summaryClosed, functionSummary]
    change (do
      func.noUnknownCallee actual.unknown
      func.targetsWithin "reads" (func.storageTargets actual.reads) (func.storageTargets summary.reads)
      func.targetsWithin "writes" (func.storageTargets actual.writes) (func.storageTargets summary.writes)
      func.targetsWithin "grows" (func.storageTargets actual.grows) (func.storageTargets summary.grows)
      func.targetsWithin "shrinks" (func.storageTargets actual.shrinks) (func.storageTargets summary.shrinks)
      func.targetsWithin "rebinds" actual.rebinds summary.rebinds
      Func.flagWithin s!"{func.name} may abort, which its summary omits" actual.aborts summary.aborts
      Func.flagWithin s!"{func.name} prints, which its summary omits" actual.outputs summary.outputs) = .ok ()
    rw [unknown, reads, writes, grows, shrinks, rebinds, aborts, outputs]
    rfl

end Goose.Lower.Validation.SummaryPreservation
