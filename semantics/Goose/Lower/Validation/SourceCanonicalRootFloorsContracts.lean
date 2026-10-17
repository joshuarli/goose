import Goose.Lower.Validation.SourceCanonicalRootFloorsSpecialDereferences
import Goose.Lower.Validation.SourceCanonicalRootFloorsForward
import Goose.Lower.Validation.SourceCanonicalRootFloorsControlRecipes
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ReplacementContentFlowSource

abbrev canonicalValueRoots (env : PEnv) (func : Func) (value : ValueId) : List RootRef :=
  rootsAt (func.provenance (resultRoots (lower env.mod) (lower env.mod).implTypes)
    (func.valueTypes (lower env.mod)) (lower env.mod).rootCount).vals value

def ExpressionFloor (nodeSyntax : Expr) : Prop :=
  ∀ {env : PEnv} {typing : TEnv} {func : Func} {root : DemandNode},
    SourceCanonicalTables env func → SourceRootTables typing env → SourceRootScopeValid root →
    ∀ {path : List Nat}, DemandNodeAt root path (.expression nodeSyntax) →
    ∀ {info : Ty} {start finish : Nat}, tyExpr typing nodeSyntax start = .ok (info, finish) →
    ∀ {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef},
      rpExpr env nodeSyntax rootsBefore = .ok (sourceRoots, rootsAfter) →
    ∀ {returnTypes : List Ty} {before after : LS} {value : ValueId},
      lowerExpr nodeSyntax (lowerEnv typing.mod typing.vars returnTypes) before = (value, after) →
      GeneratedBuilderState before → after.cur.isSome = true → NativeBuilderContinuation func after →
      RecipeMetadataProjects env root func after → sourceRoots ⊆ canonicalValueRoots env func value

def PlaceFloor (nodeSyntax : Place) : Prop :=
  ∀ {env : PEnv} {typing : TEnv} {func : Func} {root : DemandNode},
    SourceCanonicalTables env func → SourceRootTables typing env → SourceRootScopeValid root →
    ∀ {path : List Nat}, DemandNodeAt root path (.place nodeSyntax) →
    ∀ {info : PlaceInfo} {start finish : Nat}, tyPlace typing nodeSyntax start = .ok (info, finish) →
    ∀ {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef},
      rpPlace env nodeSyntax rootsBefore = .ok (sourceRoots, rootsAfter) →
    ∀ {returnTypes : List Ty} {before after : LS} {value : ValueId},
      lowerPlace nodeSyntax (lowerEnv typing.mod typing.vars returnTypes) before = (value, after) →
      GeneratedBuilderState before → after.cur.isSome = true → NativeBuilderContinuation func after →
      RecipeMetadataProjects env root func after → sourceRoots ⊆ canonicalValueRoots env func value

def ViewFloor (nodeSyntax : View) : Prop :=
  ∀ {env : PEnv} {typing : TEnv} {func : Func} {root : DemandNode},
    SourceCanonicalTables env func → SourceRootTables typing env → SourceRootScopeValid root →
    ∀ {path : List Nat}, DemandNodeAt root path (.view nodeSyntax) →
    ∀ {info : Ty × Bool} {start finish : Nat}, tyView typing nodeSyntax start = .ok (info, finish) →
    ∀ {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef},
      rpView env nodeSyntax rootsBefore = .ok (sourceRoots, rootsAfter) →
    ∀ {returnTypes : List Ty} {before after : LS} {value : ValueId},
      lowerView nodeSyntax (lowerEnv typing.mod typing.vars returnTypes) before = (value, after) →
      GeneratedBuilderState before → after.cur.isSome = true → NativeBuilderContinuation func after →
      RecipeMetadataProjects env root func after → sourceRoots ⊆ canonicalValueRoots env func value

def BlockFloor (body : Core.Block) : Prop :=
  ∀ {env : PEnv} {typing : TEnv} {func : Func} {root : DemandNode},
    SourceCanonicalTables env func → SourceRootTables typing env → SourceRootScopeValid root →
    ∀ {path : List Nat}, DemandNodeAt root path (.block body) →
    ∀ {info : Ty} {start finish : Nat}, tyBlock typing [] body start = .ok (info, finish) →
    ∀ {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef} {range : Nat × Nat},
      rpBlockValue env [] body rootsBefore = .ok ((sourceRoots, range), rootsAfter) →
    ∀ {returnTypes : List Ty} {before after : LS} {value : ValueId},
      lowerBlock none [] true body (lowerEnv typing.mod typing.vars returnTypes) before = (value, after) →
      GeneratedBuilderState before → after.cur.isSome = true → NativeBuilderContinuation func after →
      RecipeMetadataProjects env root func after → sourceRoots ⊆ canonicalValueRoots env func value

def argumentSourceNode : Arg → DemandNode
  | .byVal expression => .expression expression
  | .byRef _ place => .place place

def ArgumentsFloor (arguments : List Arg) : Prop :=
  ∀ {env : PEnv} {typing : TEnv} {func : Func} {root : DemandNode},
    SourceCanonicalTables env func → SourceRootTables typing env → SourceRootScopeValid root →
    (∀ (index : Nat) (argument : Arg), arguments[index]? = some argument →
      ∃ path, DemandNodeAt root path (argumentSourceNode argument)) →
    ∀ {callee : Core.Impl} {params : List Param} {start finish : Nat}, params.length = arguments.length →
      tyArgs typing callee params arguments start = .ok ((), finish) →
    ∀ {rootsBefore rootsAfter : RState} {argumentRoots : List (List RootRef)},
      rpArgs env arguments rootsBefore = .ok (argumentRoots, rootsAfter) →
    ∀ {returnTypes : List Ty} {before after : LS} {values : List ValueId},
      lowerArgs arguments (lowerEnv typing.mod typing.vars returnTypes) before = (values, after) →
      GeneratedBuilderState before → after.cur.isSome = true → NativeBuilderContinuation func after →
      RecipeMetadataProjects env root func after →
      ∀ (index : Nat) (roots : List RootRef), argumentRoots[index]? = some roots →
        ∃ value, values[index]? = some value ∧ roots ⊆ canonicalValueRoots env func value

end Goose.Lower.Validation.SourceCanonicalRootFloors
