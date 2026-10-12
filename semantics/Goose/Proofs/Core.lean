import Goose.Core.Validate
import Goose.Proofs.Memory

/-!
What acceptance by `validate` establishes, stated about the module and the
memory model rather than about the checker's functions.

Only the parts that follow from a bounded unfolding of `validate` are proved
here. The invariant the safety induction needs for statements and expressions
(well-typed stores, annotations that over-approximate the roots a variable can
hold) is defined in `Goose.Proofs.Memory` as `FlatTy`, `LocTy`, `HeldOk` and
`LiveRefs`; deriving it from acceptance needs inversion of the typing and root
passes at every syntactic form, which is the unproved part of the safety
theorem.
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
theorem th_core_01_entry (m : Module) (h : validate m = .ok ()) :
    ∃ ctx impl, m.contexts[m.entry]? = some ctx ∧ m.impls[ctx.impl]? = some impl ∧
      impl.params.size = 0 ∧ impl.results.size = 0 := by
  have hc := validate_entry_ok m h
  unfold checkEntry at hc
  cases h1 : m.contexts[m.entry]? with
  | none => simp [h1, reject] at hc
  | some ctx =>
    cases h2 : m.impls[ctx.impl]? with
    | none => simp [h1, h2, reject, bind, Except.bind] at hc
    | some impl =>
      refine ⟨ctx, impl, rfl, h2, ?_⟩
      simp [h1, h2, reject, bind, Except.bind] at hc
      split at hc
      · rename_i hp
        exact ⟨by simp [hp.1], by simp [hp.2]⟩
      · simp at hc

/-- The state a run starts in satisfies the live-reference invariant. -/
theorem initial_liveRefs : LiveRefs St.initial.store := by
  intro r v h
  simp [St.initial, Store.empty] at h

end Goose.Proofs.Core
