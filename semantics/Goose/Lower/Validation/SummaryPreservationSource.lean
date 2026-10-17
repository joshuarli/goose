import Goose.Lower.Validation.Summary

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound

structure SourceEffects (impl : Impl) (ctx : Context) (effect : Eff) (summary : Summary) : Prop where
  unknown : effect.unknown = false
  reads : ∀ target ∈ effect.reads, target ∈ expandTargets impl ctx summary.reads
  writes : ∀ target ∈ effect.writes, target ∈ expandTargets impl ctx summary.writes
  grows : ∀ target ∈ effect.grows, target ∈ expandTargets impl ctx summary.grows
  shrinks : ∀ target ∈ effect.shrinks, target ∈ expandTargets impl ctx summary.shrinks
  rebinds : ∀ target ∈ effect.rebinds, target ∈ summary.rebinds
  aborts : effect.aborts = true → summary.aborts = true
  outputs : effect.outputs = true → summary.outputs = true

theorem sourceEffects_of_checkSummary {module : Module} {impl : Impl} {ctx : Context}
    {effect : Eff} {summary : Summary}
    (checked : checkSummary module impl ctx effect = .ok ())
    (known : impl.summary = .known summary) : SourceEffects impl ctx effect summary := by
  unfold checkSummary at checked
  simp only [known] at checked
  inv at checked
  obtain ⟨_, _, _, _, _, unknown, reads, writes, grows, shrinks, rebinds, aborts, outputs⟩ := checked
  refine ⟨by simpa using unknown, effWithin_ok _ _ _ _ reads,
    effWithin_ok _ _ _ _ writes, effWithin_ok _ _ _ _ grows,
    effWithin_ok _ _ _ _ shrinks, effWithin_ok _ _ _ _ rebinds, ?_, ?_⟩
  · intro found
    simpa [found] using aborts
  · intro found
    simpa [found] using outputs

theorem accepted_context_effectReplay {module : Module} {index : ContextId} {ctx : Context}
    {impl : Impl} {summary : Summary}
    (accepted : validate module = .ok ()) (context : module.contexts[index]? = some ctx)
    (implementation : module.impls[ctx.impl]? = some impl)
    (known : impl.summary = .known summary) :
    ∃ roots range state,
      rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
        .ok ((roots, range), state) ∧
      (impl.body.value.isSome = true → checkResultV ⟨module, impl, ctx, []⟩ roots = .ok ()) ∧
      SourceEffects impl ctx state.eff summary := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx index ctx context
  rw [implementation] at lookup
  cases lookup
  obtain ⟨roots, range, state, body, result, effects⟩ := checked.body
  exact ⟨roots, range, state, body, result, sourceEffects_of_checkSummary effects known⟩

theorem accepted_implementation_effectReplay {module : Module} {index : ImplId}
    {impl : Impl} {summary : Summary} (accepted : validate module = .ok ())
    (implementation : module.impls[index]? = some impl)
    (known : impl.summary = .known summary) :
    ∃ ctx ∈ module.contexts.toList, ctx.impl = index ∧
      ∃ roots range state,
        rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
          .ok ((roots, range), state) ∧
        (impl.body.value.isSome = true → checkResultV ⟨module, impl, ctx, []⟩ roots = .ok ()) ∧
        SourceEffects impl ctx state.eff summary := by
  obtain ⟨ctx, member, identity⟩ := checkImplementationContexts_member
    (validate_implementationContexts accepted) (Array.getElem?_eq_some_iff.mp implementation).1
  obtain ⟨contextIndex, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  exact ⟨ctx, member, identity, accepted_context_effectReplay accepted lookup
    (by rw [identity]; exact implementation) known⟩

end Goose.Lower.Validation.SummaryPreservation
