import Goose.GIR.ReplacementContentFlow

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

@[simp] theorem ContentInputBound.covers_none (bound : ContentInputBound) :
    bound.covers none = false := rfl

@[simp] theorem ContentInputBound.callerStorage_covers (roots : List RootRef) :
    ContentInputBound.callerStorage.covers (some roots) = true := rfl

@[simp] theorem ContentInputBound.roots_covers (expected actual : List RootRef) :
    (ContentInputBound.roots expected).covers (some actual) = actual.all expected.contains := rfl

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

end Goose.GIR.ReplacementContentFlow.Model
