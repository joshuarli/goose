import Goose.Lower.Validation.SourceCanonicalRootFloorsCheckpoints
import Goose.Lower.Validation.SourceCanonicalRootFloorsSeeds
import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR

theorem RecipeMetadataProjects.ifE_canonical_floor {env : PEnv} {root : DemandNode}
    {func : Func} {state : LS} (projects : RecipeMetadataProjects env root func state)
    (valid : SourceRootScopeValid root) (condition : Expr) (yes no : Core.Block)
    {path : List Nat} (location : DemandNodeAt root path (.expression (.ifE condition yes no)))
    {before after : RState} {sourceRoots : List RootRef}
    (checked : rpExpr env (.ifE condition yes no) before = .ok (sourceRoots, after))
    {value : ValueId} (recorded : (value, .conditionalScope (sourceBlockScope yes)) ∈ state.valueRootRecipes)
    (bounded : value < func.numValues) (results : Array (List RootRef))
    (types : Array (Option VTy)) (rootCount : Nat) :
    sourceRoots ⊆ rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨rowRoots, row⟩ := projects.covered (value, .conditionalScope (sourceBlockScope yes)) recorded
  have projected := projects.ifE_row valid condition yes no location checked recorded row
  intro root member
  apply canonical_value_metadata_floor results types func rootCount bounded row
  rw [projected]
  exact unionRoots_left _ _ _ member

theorem RecipeMetadataProjects.refSliceVar_canonical_floor {env : PEnv} {root : DemandNode}
    {func : Func} {state : LS} (projects : RecipeMetadataProjects env root func state)
    {value : ValueId} {varId : VarId} (recorded : (value, .refSliceVar varId) ∈ state.valueRootRecipes)
    (bounded : value < func.numValues) (results : Array (List RootRef))
    (types : Array (Option VTy)) (rootCount : Nat) :
    ((env.ann varId).getD []) ⊆ rootsAt (func.provenance results types rootCount).vals value := by
  obtain ⟨rowRoots, row⟩ := projects.covered (value, .refSliceVar varId) recorded
  intro root member
  exact canonical_value_metadata_floor results types func rootCount bounded row root
    (projects.refSliceVar_annotation_subset recorded row member)

theorem lowerContext_recipe_canonical_floor (module : Core.Module) (ctx : Context) (impl : Impl)
    {value : ValueId} {source : ValueRootSource}
    (recorded : (value, source) ∈ (lowerImplState module impl).valueRootRecipes)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    lowerValueRootCeiling ⟨module, impl, ctx, []⟩
      (sourceNodeRootTable ⟨module, impl, ctx, []⟩ (.block impl.body)) source ⊆
      rootsAt ((lowerContextAt module ctx impl).provenance results types rootCount).vals value := by
  have row : (value, lowerValueRootCeiling ⟨module, impl, ctx, []⟩
      (sourceNodeRootTable ⟨module, impl, ctx, []⟩ (.block impl.body)) source) ∈
      (lowerContextAt module ctx impl).roots.values.getD #[] :=
    lowerValueRootRows_contains ⟨module, impl, ctx, []⟩ _ _ recorded
  have bounded := lowerContextAt_valueRoots_numValues module ctx impl
    (lowerContextAt_state_numValues module ctx impl) (Array.mem_toList_iff.mpr row)
  exact canonical_value_metadata_floor results types _ rootCount bounded row

theorem lowerGlobal_recipe_canonical_floor (module : Core.Module) (global : Core.Global)
    {value : ValueId} {source : ValueRootSource}
    (recorded : (value, source) ∈ (globalRecipeState module global).valueRootRecipes)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    lowerValueRootCeiling ⟨module, initImpl, initContext, []⟩
      (sourceNodeRootTable ⟨module, initImpl, initContext, []⟩ (.expression global.init)) source ⊆
      rootsAt ((lowerGlobal module global).init.provenance results types rootCount).vals value := by
  have row : (value, lowerValueRootCeiling ⟨module, initImpl, initContext, []⟩
      (sourceNodeRootTable ⟨module, initImpl, initContext, []⟩ (.expression global.init)) source) ∈
      (lowerGlobal module global).init.roots.values.getD #[] :=
    lowerValueRootRows_contains ⟨module, initImpl, initContext, []⟩ _ _ recorded
  have bounded := lowerGlobal_valueRoots_numValues module global
    (lowerGlobal_state_numValues module global) (Array.mem_toList_iff.mpr row)
  exact canonical_value_metadata_floor results types _ rootCount bounded row

theorem lowerContext_ifE_canonical_floor (module : Core.Module) (ctx : Context) (impl : Impl)
    (scopes : List Nat) (valid : SourceRootScopeValid (.block impl.body))
    (condition : Expr) (yes no : Core.Block) {path : List Nat}
    (location : DemandNodeAt (.block impl.body) path (.expression (.ifE condition yes no)))
    {before after : RState} {sourceRoots : List RootRef}
    (checked : rpExpr ⟨module, impl, ctx, scopes⟩ (.ifE condition yes no) before = .ok (sourceRoots, after))
    {value : ValueId}
    (recorded : (value, .conditionalScope (sourceBlockScope yes)) ∈ (lowerImplState module impl).valueRootRecipes)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    sourceRoots ⊆ rootsAt ((lowerContextAt module ctx impl).provenance results types rootCount).vals value := by
  have found := sourceNodeRootTable_ifE_lookup ⟨module, impl, ctx, scopes⟩ valid condition yes no location checked
  rw [sourceNodeRootTable_scopes ⟨module, impl, ctx, []⟩ scopes (.block impl.body)] at found
  intro root member
  apply lowerContext_recipe_canonical_floor module ctx impl recorded results types rootCount
  simp only [lowerValueRootCeiling, found, Option.join_some, Option.getD_some]
  exact unionRoots_left _ _ _ member

theorem lowerGlobal_ifE_canonical_floor (module : Core.Module) (global : Core.Global)
    (scopes : List Nat) (valid : SourceRootScopeValid (.expression global.init))
    (condition : Expr) (yes no : Core.Block) {path : List Nat}
    (location : DemandNodeAt (.expression global.init) path (.expression (.ifE condition yes no)))
    {before after : RState} {sourceRoots : List RootRef}
    (checked : rpExpr ⟨module, initImpl, initContext, scopes⟩ (.ifE condition yes no) before = .ok (sourceRoots, after))
    {value : ValueId}
    (recorded : (value, .conditionalScope (sourceBlockScope yes)) ∈ (globalRecipeState module global).valueRootRecipes)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    sourceRoots ⊆ rootsAt ((lowerGlobal module global).init.provenance results types rootCount).vals value := by
  have found := sourceNodeRootTable_ifE_lookup ⟨module, initImpl, initContext, scopes⟩ valid condition yes no location checked
  rw [sourceNodeRootTable_scopes ⟨module, initImpl, initContext, []⟩ scopes (.expression global.init)] at found
  intro root member
  apply lowerGlobal_recipe_canonical_floor module global recorded results types rootCount
  simp only [lowerValueRootCeiling, found, Option.join_some, Option.getD_some]
  exact unionRoots_left _ _ _ member

theorem lowerContext_refSliceVar_canonical_floor (module : Core.Module) (ctx : Context) (impl : Impl)
    {value : ValueId} {varId : VarId}
    (recorded : (value, .refSliceVar varId) ∈ (lowerImplState module impl).valueRootRecipes)
    (results : Array (List RootRef)) (types : Array (Option VTy)) (rootCount : Nat) :
    ((PEnv.ann ⟨module, impl, ctx, []⟩ varId).getD []) ⊆
      rootsAt ((lowerContextAt module ctx impl).provenance results types rootCount).vals value := by
  intro root member
  apply lowerContext_recipe_canonical_floor module ctx impl recorded results types rootCount
  exact unionRoots_left _ _ _ member

end Goose.Lower.Validation.SourceCanonicalRootFloors
