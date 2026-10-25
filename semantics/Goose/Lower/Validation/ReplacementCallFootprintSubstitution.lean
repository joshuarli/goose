import Goose.Lower.Validation.ReplacementDemandCallFootprint

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem substitute_touch_footprint_apart {module : GIR.Module} {callee caller : Func}
    {current : State} {arguments : List ValueId} {raw : Roots}
    {queries : ReplacementQueries} {owner : ValueId}
    (footprint : raw.AtomsWithin (TouchFootprintAtom callee (summaryTouchPolicy module callee)))
    (supported : raw.Supported (atomUniverse module callee))
    (normalizable : raw.AtomsWithin (fun atom => (normalizeAtom callee atom).isSome = true))
    (external : raw.AtomsWithin (fun atom => ∀ slot, atom ≠ .local slot))
    (calleeFacts : FunctionRootFacts callee)
    (argumentAt : ∀ index, index < callee.params.length → ∃ argument, arguments[index]? = some argument)
    (globals : ∀ global, global < module.globals.size → summaryTouchPolicy module callee (.global global) →
      OwnerDependencyApart module caller queries owner (.global global))
    (parameters : ∀ index, index < callee.params.length → ∀ (argument : ValueId), arguments[index]? = some argument →
      (flowAt current.values argument).AtomsWithin (OwnerDependencyApart module caller queries owner))
    (contents : ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content caller current (flowAt current.values argument)).AtomsWithin
        (OwnerDependencyApart module caller queries owner)) :
    (substitute caller current arguments raw).AtomsWithin (OwnerDependencyApart module caller queries owner) := by
  cases raw with
  | pending => trivial
  | unknown => exact False.elim footprint
  | known atoms =>
    apply Roots.AtomsWithin.bind_known
    intro atom member
    cases atom with
    | «local» slot => exact False.elim (external _ member slot rfl)
    | global global =>
      have policy : summaryTouchPolicy module callee (.global global) := by
        rcases footprint _ member with policy | ⟨slot, same⟩ | ⟨index, same⟩ | ⟨index, type, same, _⟩
        · exact policy
        · cases same
        · cases same
        · cases same
      have globalApart := globals global ((atomUniverse_global module callee global).mp (supported.2 member)) policy
      exact fun atom member => (List.mem_singleton.mp member) ▸ globalApart
    | param index =>
      have bound := (atomUniverse_param module callee index).mp (supported.2 member)
      obtain ⟨argument, row⟩ := argumentAt index bound
      simpa only [row, Option.map_some, Option.getD_some] using parameters index bound argument row
    | contents index =>
      have normalized := normalizable _ member
      cases annotation : callee.roots.contents.find? (·.1 == index) with
      | none => simp [normalizeAtom, annotation] at normalized
      | some entry =>
        have identity : entry.1 = index := eq_of_beq (Array.find?_some (p := fun row : Nat × List RootRef => row.1 == index)
          (a := entry) annotation)
        obtain ⟨selected, declared⟩ := entry
        dsimp only at identity
        subst selected
        have reference := calleeFacts.contentTypes index declared annotation
        have bound := (atomUniverse_contents module callee index).mp (supported.2 member)
        obtain ⟨argument, row⟩ := argumentAt index bound
        simpa only [row, Option.map_some, Option.getD_some] using contents index (by simp only [annotation, Option.isSome_some]) reference argument row

#print axioms substitute_touch_footprint_apart

end Goose.Lower.Validation
