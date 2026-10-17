import Goose.Lower.Validation.SourceCanonicalRootFloorsReadRecords
import Goose.Lower.Validation.SourceCanonicalRootFloorsCanonicalValues
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_readVar_typed_recipe {env : TEnv} {before after : LS}
    {varId : VarId} {value : ValueId} {type : Ty} {start finish : Nat}
    {returnTypes : List Ty}
    (source : tyExpr env (.read (.var varId)) start = .ok (type, finish))
    (run : lowerExpr (.read (.var varId)) (lowerEnv env.mod env.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before)
    (reference : (env.vars[varId]?).any (·.ty.isRefSlice) = true)
    (refLike : type.isRefLike = true) :
    (value, .refSliceVar varId) ∈ after.valueRootRecipes :=
  lowerExpr_readVar_recipe run live reference
    (lowerExpr_generated_typed _ source run live generated) refLike

theorem RecipeMetadataProjects.readVar_canonical_floor {env : PEnv} {root : DemandNode}
    {func : Func} {typing : TEnv} {before after : LS} {varId : VarId} {value : ValueId}
    {type : Ty} {start finish : Nat} {returnTypes : List Ty}
    (projects : RecipeMetadataProjects env root func after)
    (source : tyExpr typing (.read (.var varId)) start = .ok (type, finish))
    (run : lowerExpr (.read (.var varId)) (lowerEnv typing.mod typing.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before)
    (reference : (typing.vars[varId]?).any (·.ty.isRefSlice) = true)
    (refLike : type.isRefLike = true) (bounded : value < func.numValues)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    ((env.ann varId).getD []) ⊆ rootsAt (func.provenance results types rootCount).vals value :=
  projects.refSliceVar_canonical_floor
    (lowerExpr_readVar_typed_recipe source run live generated reference refLike)
    bounded results types rootCount

theorem lowerContext_readVar_canonical_floor {module : Core.Module} {context : Context} {impl : Impl}
    {env : PEnv} {root : DemandNode} {typing : TEnv} {before after : LS}
    {varId : VarId} {value : ValueId} {type : Ty} {start finish : Nat} {returnTypes : List Ty}
    (projects : RecipeMetadataProjects env root (lowerContextAt module context impl) after)
    (source : tyExpr typing (.read (.var varId)) start = .ok (type, finish))
    (run : lowerExpr (.read (.var varId)) (lowerEnv typing.mod typing.vars returnTypes)
      before = (value, after)) (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before)
    (reference : (typing.vars[varId]?).any (·.ty.isRefSlice) = true)
    (refLike : type.isRefLike = true)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    ((env.ann varId).getD []) ⊆
      rootsAt ((lowerContextAt module context impl).provenance results types rootCount).vals value := by
  have recorded := lowerExpr_readVar_typed_recipe source run live generated reference refLike
  obtain ⟨roots, row⟩ := projects.covered (value, .refSliceVar varId) recorded
  have bounded := lowerContextAt_valueRoots_numValues module context impl
    (lowerContextAt_state_numValues module context impl) (Array.mem_toList_iff.mpr row)
  exact projects.refSliceVar_canonical_floor recorded bounded results types rootCount

end Goose.Lower.Validation.SourceCanonicalRootFloors
