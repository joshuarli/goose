import Goose.Lower.FuelBound
import Goose.Lower.FuelBoundSize

namespace Goose.Lower

open Goose.Core

private def syntaxCapOfList (measure : α → Nat) : List α → Nat
  | [] => 0
  | value :: rest => max (measure value) (syntaxCapOfList measure rest)

private theorem syntaxCapOfList_member {measure : α → Nat} {values : List α} {value : α}
    (member : value ∈ values) : measure value ≤ syntaxCapOfList measure values := by
  induction values with
  | nil => simp at member
  | cons head tail previous =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (previous member) (Nat.le_max_right _ _)

def moduleSyntaxCap (module : Core.Module) : Nat :=
  max (syntaxCapOfList (fun impl : Impl => SourceFuelSize.block impl.body) module.impls.toList)
    (syntaxCapOfList (fun global : Core.Global => SourceFuelSize.expr global.init) module.globals.toList)

theorem moduleSyntaxCap_impl {module : Core.Module} {id : ImplId} {impl : Impl}
    (lookup : module.impls[id]? = some impl) : SourceFuelSize.block impl.body ≤ moduleSyntaxCap module := by
  unfold moduleSyntaxCap
  exact Nat.le_trans (syntaxCapOfList_member (measure := fun impl : Impl => SourceFuelSize.block impl.body)
    (by simpa using Array.mem_of_getElem? lookup)) (Nat.le_max_left _ _)

theorem moduleSyntaxCap_global {module : Core.Module} {id : GlobalId} {global : Core.Global}
    (lookup : module.globals[id]? = some global) : SourceFuelSize.expr global.init ≤ moduleSyntaxCap module := by
  unfold moduleSyntaxCap
  exact Nat.le_trans (syntaxCapOfList_member (measure := fun global : Core.Global => SourceFuelSize.expr global.init)
    (by simpa using Array.mem_of_getElem? lookup)) (Nat.le_max_right _ _)

def reflectionFuelBound (syntaxCap targetFuel nodeSize : Nat) : Nat :=
  8 * ((syntaxCap + 1) * (targetFuel + 1) + nodeSize + 1)

theorem reflectionFuelBound_positive (syntaxCap targetFuel nodeSize : Nat) :
    0 < reflectionFuelBound syntaxCap targetFuel nodeSize := by
  unfold reflectionFuelBound
  omega

theorem reflectionFuelBound_subterm {syntaxCap targetFuel child parent : Nat}
    (smaller : child < parent) :
    reflectionFuelBound syntaxCap targetFuel child + 8 ≤
      reflectionFuelBound syntaxCap targetFuel parent := by
  unfold reflectionFuelBound
  omega

theorem reflectionFuelBound_node_mono {syntaxCap targetFuel child parent : Nat}
    (bounded : child ≤ parent) :
    reflectionFuelBound syntaxCap targetFuel child ≤ reflectionFuelBound syntaxCap targetFuel parent := by
  unfold reflectionFuelBound
  omega

theorem reflectionFuelBound_step {syntaxCap targetFuel child parent : Nat}
    (bounded : child ≤ syntaxCap) :
    reflectionFuelBound syntaxCap targetFuel child + 8 ≤
      reflectionFuelBound syntaxCap (targetFuel + 1) parent := by
  unfold reflectionFuelBound
  rw [Nat.mul_add (syntaxCap + 1) (targetFuel + 1) 1]
  omega

theorem reflectionFuelBound_target_mono {syntaxCap small large nodeSize : Nat}
    (enough : small ≤ large) :
    reflectionFuelBound syntaxCap small nodeSize ≤ reflectionFuelBound syntaxCap large nodeSize := by
  have products := Nat.mul_le_mul_left (syntaxCap + 1) (Nat.add_le_add_right enough 1)
  unfold reflectionFuelBound
  omega

theorem reflectionFuelBound_recursive {syntaxCap residual fuel child parent : Nat}
    (earlier : residual < fuel) (bounded : child ≤ syntaxCap) :
    reflectionFuelBound syntaxCap residual child + 8 ≤ reflectionFuelBound syntaxCap fuel parent := by
  exact Nat.le_trans (reflectionFuelBound_step bounded)
    (reflectionFuelBound_target_mono (by omega))

theorem reflectionFuelBound_child {syntaxCap residual fuel child parent : Nat}
    (earlier : residual ≤ fuel) (smaller : child < parent) :
    reflectionFuelBound syntaxCap residual child ≤ reflectionFuelBound syntaxCap fuel (parent - 1) := by
  exact Nat.le_trans (reflectionFuelBound_target_mono earlier)
    (reflectionFuelBound_node_mono (by omega))

theorem reflectionFuelBound_parent {syntaxCap fuel parent cost : Nat}
    (positive : 0 < parent) (small : cost ≤ 8) :
    reflectionFuelBound syntaxCap fuel (parent - 1) + cost ≤ reflectionFuelBound syntaxCap fuel parent := by
  unfold reflectionFuelBound
  omega

end Goose.Lower
