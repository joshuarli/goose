import Goose.GIR.ReplacementContentFlowProofsNormalization

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

@[simp] theorem ContentInputBound.covers_none (bound : ContentInputBound) :
    bound.covers none = false := rfl

@[simp] theorem ContentInputBound.callerStorage_covers (roots : List RootRef) :
    ContentInputBound.callerStorage.covers (some roots) = true := rfl

@[simp] theorem ContentInputBound.roots_covers (expected actual : List RootRef) :
    (ContentInputBound.roots expected).covers (some actual) = actual.all expected.contains := rfl

theorem ContentInputBound.covers_subset {bound : ContentInputBound}
    {actual upper : List RootRef} (covered : bound.covers (some upper) = true)
    (within : actual ⊆ upper) : bound.covers (some actual) = true := by
  cases bound with
  | callerStorage => rfl
  | roots expected =>
      apply List.all_eq_true.mpr
      intro root member
      exact List.all_eq_true.mp covered root (within member)

theorem ContentInputBound.join_covers_left {left right : ContentInputBound}
    {actual : List RootRef} (covered : left.covers (some actual) = true) :
    (left.join right).covers (some actual) = true := by
  cases left with
  | callerStorage => rfl
  | roots expected =>
      cases right with
      | callerStorage => rfl
      | roots other =>
          apply List.all_eq_true.mpr
          intro root member
          exact List.contains_iff_mem.mpr ((unionRoots_mem_iff _ _ _).mpr
            (Or.inl (List.contains_iff_mem.mp (List.all_eq_true.mp covered root member))))

theorem ContentInputBound.join_covers_right {left right : ContentInputBound}
    {actual : List RootRef} (covered : right.covers (some actual) = true) :
    (left.join right).covers (some actual) = true := by
  cases right with
  | callerStorage => cases left <;> rfl
  | roots expected =>
      cases left with
      | callerStorage => rfl
      | roots other =>
          apply List.all_eq_true.mpr
          intro root member
          exact List.contains_iff_mem.mpr ((unionRoots_mem_iff _ _ _).mpr
            (Or.inr (List.contains_iff_mem.mp (List.all_eq_true.mp covered root member))))

theorem ContentInputBound.join_covers {left right : ContentInputBound}
    {leftRoots rightRoots : List RootRef}
    (leftCovered : left.covers (some leftRoots) = true)
    (rightCovered : right.covers (some rightRoots) = true) :
    (left.join right).covers (some (leftRoots ++ rightRoots)) = true := by
  have first := ContentInputBound.join_covers_left (right := right) leftCovered
  have second := ContentInputBound.join_covers_right (left := left) rightCovered
  cases joined : left.join right with
  | callerStorage => rfl
  | roots expected =>
      rw [joined] at first second
      exact List.all_eq_true.mpr fun root member =>
        (List.mem_append.mp member).elim
          (List.all_eq_true.mp first root) (List.all_eq_true.mp second root)

theorem admittedArgumentBound_generic (callee : Func)
    (argumentRoots : Nat → Option (List RootRef)) (index : Nat)
    (type : Core.Ty) (actual declared : List RootRef)
    (parameter : callee.params[index]? = some type)
    (known : argumentRoots index = some actual)
    (row : callee.roots.params.find? (·.1 == index) = some (index, declared))
    (reference : type.isRefLike = true)
    (generic : declared.contains (.param index) = true) :
    admittedArgumentBound callee argumentRoots index = some .callerStorage := by
  have member : RootRef.param index ∈ declared := by simpa using generic
  simp [admittedArgumentBound, parameter, known, row, reference, member]

theorem admittedArgumentBound_fixed (callee : Func)
    (argumentRoots : Nat → Option (List RootRef)) (index : Nat)
    (type : Core.Ty) (actual declared : List RootRef)
    (parameter : callee.params[index]? = some type)
    (known : argumentRoots index = some actual)
    (row : callee.roots.params.find? (·.1 == index) = some (index, declared))
    (fixed : (type.isRefLike && declared.contains (.param index)) = false) :
    admittedArgumentBound callee argumentRoots index =
      some (.roots (Core.unionRoots actual (declared.filterMap fun
        | .global global => some (.global global)
        | _ => none))) := by
  have excluded : ¬(type.isRefLike = true ∧ RootRef.param index ∈ declared) := by
    simpa using fixed
  simp [admittedArgumentBound, parameter, known, row, excluded]
  rfl

theorem admittedArgumentBound_missing (callee : Func)
    (argumentRoots : Nat → Option (List RootRef)) (index : Nat)
    (type : Core.Ty) (actual : List RootRef)
    (parameter : callee.params[index]? = some type)
    (known : argumentRoots index = some actual)
    (row : callee.roots.params.find? (·.1 == index) = none) :
    admittedArgumentBound callee argumentRoots index = some (.roots actual) := by
  simp [admittedArgumentBound, parameter, known, row]

theorem admittedArgumentBound_unknown (callee : Func)
    (argumentRoots : Nat → Option (List RootRef)) (index : Nat)
    (unknown : argumentRoots index = none) :
    admittedArgumentBound callee argumentRoots index = none := by
  simp [admittedArgumentBound, unknown]

@[simp] theorem contentInputBound_nil (callee : Func)
    (argumentRoots : Nat → Option (List RootRef)) :
    contentInputBound callee argumentRoots [] = some (.roots []) := rfl

#print axioms admittedArgumentBound_generic
#print axioms admittedArgumentBound_fixed
#print axioms admittedArgumentBound_missing
#print axioms admittedArgumentBound_unknown
#print axioms ContentInputBound.covers_subset
#print axioms ContentInputBound.join_covers

end Goose.GIR.ReplacementContentFlow.Model
