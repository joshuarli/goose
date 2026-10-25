import Goose.Lower.Validation.SourceCanonicalRootFloorsControlRecords
import Goose.Lower.Validation.SourceCanonicalRootFloorsReadRecipes

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_ifE_typed_recipe {env : TEnv} {before after : LS}
    {condition : Expr} {yes no : Core.Block} {value : ValueId} {type : Ty}
    {start finish : Nat} {returnTypes : List Ty}
    (source : tyExpr env (.ifE condition yes no) start = .ok (type, finish))
    (run : lowerExpr (.ifE condition yes no) (lowerEnv env.mod env.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before) (refLike : type.isRefLike = true) :
    (value, .conditionalScope (sourceBlockScope yes)) ∈ after.valueRootRecipes :=
  lowerExpr_ifE_recipe run live (lowerExpr_generated_typed _ source run live generated) refLike

theorem RecipeMetadataProjects.ifE_actual_canonical_floor {env : PEnv} {root : DemandNode}
    {func : Func} {typing : TEnv} {before after : LS} {condition : Expr} {yes no : Core.Block}
    {value : ValueId} {type : Ty} {start finish : Nat} {returnTypes : List Ty}
    (projects : RecipeMetadataProjects env root func after) (valid : SourceRootScopeValid root)
    {path : List Nat} (location : DemandNodeAt root path (.expression (.ifE condition yes no)))
    {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef}
    (replayed : rpExpr env (.ifE condition yes no) rootsBefore = .ok (sourceRoots, rootsAfter))
    (source : tyExpr typing (.ifE condition yes no) start = .ok (type, finish))
    (run : lowerExpr (.ifE condition yes no) (lowerEnv typing.mod typing.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before) (refLike : type.isRefLike = true)
    (bounded : value < func.numValues)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    sourceRoots ⊆ rootsAt (func.provenance results types rootCount).vals value :=
  projects.ifE_canonical_floor valid condition yes no location replayed
    (lowerExpr_ifE_typed_recipe source run live generated refLike) bounded results types rootCount

theorem lowerContext_ifE_actual_canonical_floor {module : Core.Module} {context : Context} {impl : Impl}
    {env : PEnv} {root : DemandNode} {typing : TEnv} {before after : LS}
    {condition : Expr} {yes no : Core.Block} {value : ValueId} {type : Ty}
    {start finish : Nat} {returnTypes : List Ty}
    (projects : RecipeMetadataProjects env root (lowerContextAt module context impl) after)
    (valid : SourceRootScopeValid root)
    {path : List Nat} (location : DemandNodeAt root path (.expression (.ifE condition yes no)))
    {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef}
    (replayed : rpExpr env (.ifE condition yes no) rootsBefore = .ok (sourceRoots, rootsAfter))
    (source : tyExpr typing (.ifE condition yes no) start = .ok (type, finish))
    (run : lowerExpr (.ifE condition yes no) (lowerEnv typing.mod typing.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before) (refLike : type.isRefLike = true)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    sourceRoots ⊆ rootsAt ((lowerContextAt module context impl).provenance results types rootCount).vals value := by
  have recorded := lowerExpr_ifE_typed_recipe source run live generated refLike
  obtain ⟨roots, row⟩ := projects.covered (value, .conditionalScope (sourceBlockScope yes)) recorded
  have bounded := lowerContextAt_valueRoots_numValues module context impl
    (lowerContextAt_state_numValues module context impl) (Array.mem_toList_iff.mpr row)
  exact projects.ifE_canonical_floor valid condition yes no location replayed recorded
    bounded results types rootCount

theorem lowerGlobal_ifE_actual_canonical_floor {module : Core.Module} {global : Core.Global}
    {env : PEnv} {root : DemandNode} {typing : TEnv} {before after : LS}
    {condition : Expr} {yes no : Core.Block} {value : ValueId} {type : Ty}
    {start finish : Nat} {returnTypes : List Ty}
    (projects : RecipeMetadataProjects env root (lowerGlobal module global).init after)
    (valid : SourceRootScopeValid root)
    {path : List Nat} (location : DemandNodeAt root path (.expression (.ifE condition yes no)))
    {rootsBefore rootsAfter : RState} {sourceRoots : List RootRef}
    (replayed : rpExpr env (.ifE condition yes no) rootsBefore = .ok (sourceRoots, rootsAfter))
    (source : tyExpr typing (.ifE condition yes no) start = .ok (type, finish))
    (run : lowerExpr (.ifE condition yes no) (lowerEnv typing.mod typing.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before) (refLike : type.isRefLike = true)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    sourceRoots ⊆ rootsAt ((lowerGlobal module global).init.provenance results types rootCount).vals value := by
  have recorded := lowerExpr_ifE_typed_recipe source run live generated refLike
  obtain ⟨roots, row⟩ := projects.covered (value, .conditionalScope (sourceBlockScope yes)) recorded
  have bounded := lowerGlobal_valueRoots_numValues module global
    (lowerGlobal_state_numValues module global) (Array.mem_toList_iff.mpr row)
  exact projects.ifE_canonical_floor valid condition yes no location replayed recorded
    bounded results types rootCount

end Goose.Lower.Validation.SourceCanonicalRootFloors
