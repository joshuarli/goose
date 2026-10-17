import Goose.GIR.Effects

namespace Goose.GIR

open Goose.Core

def Func.rootWithin (f : Func) (ceiling : List RootRef) (root : RootRef) : Bool :=
  ceiling.contains root || match root with
    | .param parameter => (f.parameterRoots parameter).all ceiling.contains
    | _ => false

def RootsRefine (f : Func) (actual ceiling : List RootRef) : Prop :=
  ∀ root ∈ actual, root ∈ ceiling ∨
    ∀ concrete ∈ f.expandParameterRoot root, concrete ∈ ceiling

theorem Func.rootWithin_eq_true (f : Func) (ceiling : List RootRef) (root : RootRef) :
    f.rootWithin ceiling root = true ↔ root ∈ ceiling ∨
      ∀ concrete ∈ f.expandParameterRoot root, concrete ∈ ceiling := by
  cases root <;> simp [Func.rootWithin, Func.expandParameterRoot, List.all_eq_true,
    ]

def Func.rootsWithin (f : Func) (actual ceiling : List RootRef) : Bool :=
  actual.all (f.rootWithin ceiling)

theorem Func.rootsWithin_eq_true (f : Func) (actual ceiling : List RootRef) :
    f.rootsWithin actual ceiling = true ↔ RootsRefine f actual ceiling := by
  simp [Func.rootsWithin, RootsRefine, List.all_eq_true, Func.rootWithin_eq_true]

end Goose.GIR
