import Goose.Core.Validate
import Goose.Proofs.Memory

/-!
Two facts that follow from a bounded unfolding of `validate`: the shape of the
entry, and that a run starts in a store with no reference at all. What
acceptance gives for every context, over stores, values and locations, is
`Goose.Proofs.Safety.validated_context_sound`.
-/

namespace Goose.Proofs.Core
open Goose.Core Goose.Proofs.Memory

theorem validate_entry_ok (m : Module) (h : validate m = .ok ()) : checkEntry m = .ok () := by
  unfold validate at h
  cases hc : checkEntry m with
  | error e => simp [hc, bind, Except.bind] at h
  | ok u => cases u; rfl

/-- Acceptance fixes the entry: a context whose implementation takes no
parameters and returns nothing. -/
theorem validate_entry_shape (m : Module) (h : validate m = .ok ()) :
    ∃ ctx impl, m.contexts[m.entry]? = some ctx ∧ m.impls[ctx.impl]? = some impl ∧
      impl.params.size = 0 ∧ impl.results.size = 0 := by
  have hc := validate_entry_ok m h
  unfold checkEntry at hc
  cases h1 : m.contexts[m.entry]? with
  | none => simp [h1, reject] at hc
  | some ctx =>
    cases h2 : m.impls[ctx.impl]? with
    | none => simp [h1, h2, reject] at hc
    | some impl =>
      refine ⟨ctx, impl, rfl, h2, ?_⟩
      simp [h1, h2, reject] at hc
      split at hc
      · rename_i hp
        exact ⟨by simp [hp.1], by simp [hp.2]⟩
      · simp at hc

/-- The state a run starts in satisfies the live-reference invariant. -/
theorem initial_liveRefs : LiveRefs St.initial.store := by
  intro r v h
  simp [St.initial, Store.empty] at h

end Goose.Proofs.Core
