import Goose.Core.DeclarativeDemand

namespace Goose.Core.DeclarativeDemandChecks

example (m : Module) (accepted : validate m = .ok ()) : DeclarativeDemand m :=
  validate_declarativeDemand m accepted

example : DemandRootSeparate (.local 0) (.local 1) := .locals (by decide)

example : ¬ DemandRootSeparate (.param 0) (.param 1) :=
  parameterRoots_notSeparate 0 1

example : ¬ DemandRootSeparate (.param 0) (.global 1) :=
  parameterGlobal_notSeparate 0 1

example : ¬ DemandInterior (.ref .mutable (.growshrink (.int .i64))) :=
  ownerReference_doesNotDemandInterior .mutable (.int .i64)

example : DemandInterior (.slice .mutable (.int .i64)) := by trivial

example : ¬ DemandInvalidatingOwner (some (.limited (.int .i64) 8)) :=
  limitedOwner_doesNotInvalidate (.int .i64) 8

example (point : DemandPoint) (access : AccessEnv)
    (held : (⟨.slice .mutable (.int .i64), [.param 1], .iteration 7⟩ : RetainedAlias)
      ∈ point.retained) :
    ¬ DeclarativeFrameDemand access point ⟨some (.growshrink (.int .i64)), [.param 0]⟩ := by
  intro demand
  have separate := demand.retainedResizable held (by trivial)
  exact parameterRoots_notSeparate 0 1 (separate (.param 0) (by simp) (.param 1) (by simp))

example (point : DemandPoint) (access : AccessEnv)
    (held : (⟨.ref .mutable (.int .i64), [.local 0], .operand [0]⟩ : RetainedAlias)
      ∈ point.retained) :
    ¬ DeclarativeFrameDemand access point ⟨some (.growshrink (.int .i64)), [.local 0]⟩ := by
  intro demand
  have separate := demand.retainedResizable held (by simp [DemandInterior, Ty.ownerElem?])
  have sameRoot := separate (.local 0) (by simp) (.local 0) (by simp)
  cases sameRoot with
  | locals ne => exact ne rfl

private def emptyModule (profile : ArtifactProfile) : Module := {
  files := #[]
  types := #[]
  globals := #[]
  impls := #[{
    name := "main"
    params := #[]
    results := #[]
    vars := #[]
    body := .mk 0 [] none
    summary := .unknown }]
  contexts := #[{ impl := 0, decl := "main", varRoots := [], resultRoots := [] }]
  entry := 0
  origins := #[]
  profile := profile }

#guard match validate (emptyModule .pilot) with
  | .ok () => true
  | .error _ => false

#guard match validate (emptyModule .shrink) with
  | .ok () => true
  | .error _ => false

example (slots : Array Val) :
    Val.truncate 0 (.limited (.int .i64) 8 slots 3) =
      some (.limited (.int .i64) 8 slots 0) :=
  limitedShrink_keepsWrittenSlots _ _ _ _ _ (by decide)



#print axioms Goose.Core.validate_declarativeDemand
#print axioms Goose.Core.DeclarativePlanDemand.directShrink
#print axioms Goose.Core.DeclarativePlanDemand.unknownCall

end Goose.Core.DeclarativeDemandChecks
