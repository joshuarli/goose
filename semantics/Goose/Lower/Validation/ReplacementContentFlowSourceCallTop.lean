import Goose.Lower.Validation.ReplacementContentFlowSourceCallAdmissions
import Goose.Lower.Validation.SourceRootBounds
import Goose.Lower.Validation.SymbolSourceTables
import Goose.GIR.ReplacementContentFlowProofsSupport

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem parameter_roots_supported {module : GIR.Module} {func : Func}
    (tables : SymbolTableFacts module func) {index : Nat} (bounded : index < func.params.length)
    {root : RootRef} (member : root ∈ func.parameterRoots index) :
    Atom.ofRootRef root ∈ atomUniverse module func := by
  cases found : func.roots.params.find? (·.1 == index) with
  | none =>
    have identity : root = .param index := by simpa [Func.parameterRoots, found] using member
    subst root
    exact (atomUniverse_param module func index).mpr bounded
  | some row =>
    have selected := tables.parameters row.1 row.2
      (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    have inRow : root ∈ row.2 := by simpa [Func.parameterRoots, found] using member
    have external := selected.2.2 root inRow
    cases root with
    | «local» slot => exact False.elim external
    | global global => exact (atomUniverse_global module func global).mpr external
    | param parameter =>
      have identity : parameter = row.1 := external
      subst parameter
      exact (atomUniverse_param module func row.1).mpr selected.1

theorem accepted_expanded_source_root_support {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {sourceRoots : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (sourceBound : SourceRootsWithin module impl sourceRoots) :
    ∀ root ∈ sourceRoots.flatMap (lowerContextAt module ctx impl).expandParameterRoot,
      Atom.ofRootRef root ∈ atomUniverse (lower module) (lowerContextAt module ctx impl) := by
  have tables := lowerContextAt_symbol_tables accepted contextRow implementationRow
  intro root member
  obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  have bounded := sourceBound sourceRoot sourceMember
  cases sourceRoot with
  | «local» slot =>
    have identity : root = .local slot := by simpa [Func.expandParameterRoot] using expanded
    subst root
    apply (atomUniverse_local _ _ slot).mpr
    change slot < (impl.vars.mapIdx (fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot))).size
    simpa only [SourceRootIndexWithin, Array.size_mapIdx] using bounded
  | global global =>
    have identity : root = .global global := by simpa [Func.expandParameterRoot] using expanded
    subst root
    apply (atomUniverse_global _ _ global).mpr
    simpa only [SourceRootIndexWithin, lower, Array.size_map] using bounded
  | param parameter =>
    apply parameter_roots_supported tables (index := parameter) ?_ expanded
    simpa only [SourceRootIndexWithin, lowerContextAt, lowerImpl, List.length_map, Array.length_toList] using bounded

#print axioms accepted_expanded_source_root_support

theorem source_expression_root_support (expression : Expr) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {context : ContextId} (contextRow : penv.mod.contexts[context]? = some penv.ctx)
    (implementationRow : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {type : Ty} {start finish : Nat} (typed : tyExpr env expression start = .ok (type, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpExpr penv expression before = .ok (roots, after)) :
    ∀ root ∈ roots.flatMap (lowerContextAt penv.mod penv.ctx penv.impl).expandParameterRoot,
      Atom.ofRootRef root ∈ atomUniverse (lower penv.mod) (lowerContextAt penv.mod penv.ctx penv.impl) := by
  exact accepted_expanded_source_root_support accepted contextRow implementationRow
    (source_expr_root_bounds expression tables accepted contextRow implementationRow typed replayed)

theorem source_place_root_support (place : Place) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {context : ContextId} (contextRow : penv.mod.contexts[context]? = some penv.ctx)
    (implementationRow : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : PlaceInfo} {start finish : Nat} (typed : tyPlace env place start = .ok (info, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpPlace penv place before = .ok (roots, after)) :
    ∀ root ∈ roots.flatMap (lowerContextAt penv.mod penv.ctx penv.impl).expandParameterRoot,
      Atom.ofRootRef root ∈ atomUniverse (lower penv.mod) (lowerContextAt penv.mod penv.ctx penv.impl) := by
  exact accepted_expanded_source_root_support accepted contextRow implementationRow
    (source_place_root_bounds place tables accepted contextRow implementationRow typed replayed)

#print axioms source_expression_root_support
#print axioms source_place_root_support

end Goose.Lower.Validation.ReplacementContentFlowSource
