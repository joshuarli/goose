import Goose.Lower.Validation.SourceCanonicalRootFloorsWriteNodes

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

theorem sourceIfE_root_write_agrees (env : PEnv) (condition : Expr) (yes no : Block)
    {before after : RState} {roots : List RootRef}
    (checked : rpExpr env (.ifE condition yes no) before = .ok (roots, after)) :
    unionRoots (collectSourceBlockRoots env yes #[]).1 (collectSourceBlockRoots env no #[]).1 = roots := by
  have projected := collectSourceExprRoots_agrees env (.ifE condition yes no) #[] checked
  change unionRoots
    (collectSourceBlockRoots env yes (collectSourceExprRoots env condition #[]).2).1
    (collectSourceBlockRoots env no
      (collectSourceBlockRoots env yes (collectSourceExprRoots env condition #[]).2).2).1 = roots at projected
  rw [collectSourceBlockRoots_independent env yes _ #[],
    collectSourceBlockRoots_independent env no _ #[]] at projected
  exact projected

theorem sourceNodeRootTable_ifE_lookup (env : PEnv) {root : DemandNode} {path : List Nat}
    (valid : SourceRootScopeValid root) (condition : Expr) (yes no : Block)
    (location : DemandNodeAt root path (.expression (.ifE condition yes no)))
    {before after : RState} {roots : List RootRef}
    (checked : rpExpr env (.ifE condition yes no) before = .ok (roots, after)) :
    (sourceNodeRootTable env root)[sourceBlockScope yes]? = some (some roots) := by
  apply sourceNodeRootTable_write_lookup env root valid.1 valid.2 (sourceBlockScope yes, roots)
  apply sourceNodeRootWrites_at env location
  rw [sourceNodeRootWrites_children]
  apply List.mem_append_right
  simpa only [sourceNodeOwnRootWrites, sourceIfE_root_write_agrees env condition yes no checked]
    using List.mem_singleton_self (sourceBlockScope yes, roots)

theorem RecipeMetadataProjects.ifE_row {env : PEnv} {root : DemandNode} {func : Goose.GIR.Func}
    {state : LS} (projects : RecipeMetadataProjects env root func state)
    (valid : SourceRootScopeValid root) (condition : Expr) (yes no : Block)
    {path : List Nat} (location : DemandNodeAt root path (.expression (.ifE condition yes no)))
    {before after : RState} {sourceRoots : List RootRef}
    (checked : rpExpr env (.ifE condition yes no) before = .ok (sourceRoots, after))
    {value : Goose.GIR.ValueId}
    (recorded : (value, .conditionalScope (sourceBlockScope yes)) ∈ state.valueRootRecipes)
    {rowRoots : List RootRef} (row : (value, rowRoots) ∈ func.roots.values.getD #[]) :
    rowRoots = lowerContextRootCeiling env.ctx env.impl sourceRoots := by
  have projected := projects.project (value, .conditionalScope (sourceBlockScope yes)) recorded rowRoots row
  change rowRoots = lowerContextRootCeiling env.ctx env.impl
    ((sourceNodeRootTable env root)[sourceBlockScope yes]?.join.getD []) at projected
  simpa only [sourceNodeRootTable_ifE_lookup env valid condition yes no location checked,
    Option.join_some, Option.getD_some] using projected

end Goose.Lower.Validation.SourceCanonicalRootFloors
