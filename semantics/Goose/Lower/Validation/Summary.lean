import Goose.Lower.ContextLowering
import Goose.Core.Sound.Module

namespace Goose.Lower.Validation

open Goose.Core

def Target.Within (module : Module) (impl : Impl) : Target → Prop
  | .param index => index < impl.params.size
  | .global index => index < module.globals.size

theorem checkSummaryTargets_bounds {module : Module} {impl : Impl} {label : String}
    {targets : List Target} (checked : checkSummaryTargets module impl label targets = .ok ()) :
    ∀ target ∈ targets, Target.Within module impl target := by
  intro target member
  have one := (Core.Sound.forAll_ok _ _).mp checked target member
  cases target with
  | param index =>
    by_cases bound : index < impl.params.size
    · exact bound
    · simp [bound, reject] at one
  | global index =>
    by_cases bound : index < module.globals.size
    · exact bound
    · simp [bound, reject] at one

theorem checkSummary_target_bounds {module : Module} {impl : Impl} {ctx : Context}
    {effect : Eff} {summary : Summary}
    (checked : checkSummary module impl ctx effect = .ok ())
    (known : impl.summary = .known summary) :
    ∀ target ∈ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds,
      Target.Within module impl target := by
  simp only [checkSummary, known] at checked
  obtain ⟨_, reads, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  obtain ⟨_, writes, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  obtain ⟨_, grows, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  obtain ⟨_, shrinks, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  obtain ⟨_, rebinds, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  intro target member
  simp only [List.mem_append] at member
  rcases member with (((readsMember | writesMember) | growsMember) | shrinksMember) | rebindsMember
  · exact checkSummaryTargets_bounds reads target readsMember
  · exact checkSummaryTargets_bounds writes target writesMember
  · exact checkSummaryTargets_bounds grows target growsMember
  · exact checkSummaryTargets_bounds shrinks target shrinksMember
  · exact checkSummaryTargets_bounds rebinds target rebindsMember

theorem validate_implementationContexts {module : Module} (checked : validate module = .ok ()) :
    checkImplementationContexts module = .ok () := by
  unfold validate at checked
  obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  obtain ⟨_, _, checked⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  obtain ⟨_, implementations, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  exact implementations

theorem checkImplementationContexts_member {module : Module} {index : ImplId}
    (checked : checkImplementationContexts module = .ok ()) (bound : index < module.impls.size) :
    ∃ context ∈ module.contexts.toList, context.impl = index := by
  have one := (Core.Sound.forAll_ok _ _).mp checked index (List.mem_range.mpr bound)
  have present : (module.contexts.toList.any fun ctx => ctx.impl == index) = true := by
    by_cases present : (module.contexts.toList.any fun ctx => ctx.impl == index) = true
    · exact present
    · simp [present, reject] at one
  obtain ⟨context, member, implementation⟩ := List.any_eq_true.mp present
  exact ⟨context, member, eq_of_beq implementation⟩

theorem validate_summaryTarget_bounds {module : Module} {index : ImplId} {impl : Impl}
    {summary : Summary} (checked : validate module = .ok ())
    (lookup : module.impls[index]? = some impl) (known : impl.summary = .known summary) :
    ∀ target ∈ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds,
      Target.Within module impl target := by
  have bound : index < module.impls.size := (Array.getElem?_eq_some_iff.mp lookup).1
  obtain ⟨context, contextMember, identity⟩ :=
    checkImplementationContexts_member (validate_implementationContexts checked) bound
  obtain ⟨contextIndex, contextLookup⟩ :=
    Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp contextMember)
  obtain ⟨source, sourceLookup, contextOk⟩ :=
    (Core.Sound.validate_modOk module checked).ctx contextIndex context contextLookup
  rw [identity, lookup] at sourceLookup
  cases sourceLookup
  obtain ⟨_, _, state, _, _, summaryChecked⟩ := contextOk.body
  exact checkSummary_target_bounds summaryChecked known

theorem lowerImpl_summaryTarget_bounds {module : Module} {index : ImplId} {impl : Impl}
    {summary : Summary} (checked : validate module = .ok ())
    (lookup : module.impls[index]? = some impl) (known : impl.summary = .known summary) :
    ∀ target ∈ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks ++ summary.rebinds,
      match target with
      | .param param => param < (lowerImpl module impl).params.length
      | .global global => global < (lower module).globals.size := by
  intro target member
  have bound := validate_summaryTarget_bounds checked lookup known target member
  cases target <;> simpa only [Target.Within, lowerImpl, lowerImplFromState, lower, Array.size_map,
    List.length_map, Array.length_toList] using bound

end Goose.Lower.Validation
