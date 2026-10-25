import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment
import Goose.Lower.Validation.SummaryPreservationTypedResultBounds
import Goose.Lower.Validation.SummaryPreservationReplayValue

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem source_body_result_upper {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {type : Ty} {finish : Nat} {roots : List RootRef}
    {range : Nat × Nat} {after : RState} {upper : Prov} {state : LS} {value : ValueId}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (typed : tyBlock (implEnv module impl) [] impl.body impl.params.size = .ok (type, finish))
    (replayed : rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ =
      .ok ((roots, range), after))
    (present : impl.body.value.isSome = true)
    (replayValue : ReplayValue (lowerContextAt module ctx impl) upper state value roots (.data type)) :
    ∀ root ∈ rootsAt upper.vals value, root ∈ contextTypedResultUpper module ctx := by
  have moduleOk := validate_modOk module accepted
  obtain ⟨checkedImpl, row, checked⟩ := moduleOk.ctx context ctx contextRow
  rw [implementationRow] at row
  cases row
  obtain ⟨checkedRoots, checkedRange, checkedAfter, checkedReplay, resultChecked, _⟩ := checked.body
  have same := Except.ok.inj (checkedReplay.symm.trans replayed)
  have rootsSame : checkedRoots = roots := (Prod.mk.inj (Prod.mk.inj same).1).1
  subst checkedRoots
  by_cases reference : (impl.results[0]?).any Ty.isRefLike = true
  · intro root member
    have found := checkedResult_refinedResultUpper checked replayValue.refined (resultChecked present) root member
    simpa only [contextTypedResultUpper, implementationRow, reference, ite_true,
      contextRefinedResultUpper] using found
  · have nonref : type.isRefLike = false := by
      obtain ⟨bodyType, next, bodyTyped, shape⟩ := (moduleOk.impl ctx.impl impl implementationRow).body
      have typeEq : bodyType = type := (Prod.mk.inj (Except.ok.inj (bodyTyped.symm.trans typed))).1
      subst bodyType
      rcases shape with ⟨_, rfl⟩ | ⟨expected, resultTypes, same, _⟩
      · rfl
      · have resultAt : impl.results[0]? = some expected := by
          rw [← Array.getElem?_toList, resultTypes]
          rfl
        have expectedNonref : expected.isRefLike = false := by
          simpa only [resultAt, Option.any_some, Bool.not_eq_true] using reference
        rw [same present]
        exact expectedNonref
    intro root member
    rw [replayValue.scalar nonref] at member
    cases member

#print axioms source_body_result_upper

end Goose.Lower.Validation.SummaryPreservation
