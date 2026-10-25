import Goose.Lower.Validation.ReplacementSourceEntry
import Goose.Lower.Validation.ReplacementOwnerSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def IndependentReplacementSources (root : DemandNode) : Prop :=
  ∀ {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId},
    DemandNodeAt root path (.statement (.assignWhole place rhs origin)) → IndependentOwnerShape rhs

theorem ReplacementDemandSourceApart.of_owner_shapes
    {source : Core.Module} {planOwner : Nat} {root : DemandNode}
    {le : LEnv} {state : LS} {module : GIR.Module} {func : Func}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    (shapes : IndependentReplacementSources root) :
    ReplacementDemandSourceApart source planOwner root le state module func := by
  intro owner value origin site rootEq context
  have structural := site.structuralSource
  rw [rootEq] at structural
  obtain ⟨info, element, childStart, placeTyped, ownerShape, rhsTyped, rest⟩ :=
    tyStmt_assignWhole_children site.accepted
  exact lowerExpr_owner_shape_apart builder blocks slots globals sigs structs profile graphs
    rhsTyped (shapes structural) site.site.rhsRun site.captured_extension

theorem lowerContextAt_checkShrinkReplace_of_owner_shapes {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {context : Context}
    (contextAt : module.contexts[contextIndex]? = some context) {impl : Core.Impl}
    (implAt : module.impls[context.impl]? = some impl)
    (builder : EmittedBuilder (lowerEnv module impl.vars impl.results.toList) initState (cfg_implState module impl))
    (graphs : MutableSnapshotGraphs (lower module) (lowerContextAt module context impl) (cfg_implState module impl))
    (shapes : IndependentReplacementSources (.block impl.body)) (label : String) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module)) = .ok () :=
  lowerContextAt_checkShrinkReplace_of_source_apart accepted contextAt implAt builder graphs
    (ReplacementDemandSourceApart.of_owner_shapes builder (cfg_context_blocks module context impl) rfl
      (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs shapes) label

theorem lowerGlobal_checkShrinkReplace_of_owner_shapes {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {globalIndex : GlobalId} {global : Core.Global}
    (globalAt : module.globals[globalIndex]? = some global)
    (builder : EmittedBuilder (lowerEnv module #[] [global.ty]) initState (cfg_globalState module global))
    (graphs : MutableSnapshotGraphs (lower module) (lowerGlobal module global).init (cfg_globalState module global))
    (shapes : IndependentReplacementSources (.expression global.init)) (label : String) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) = .ok () :=
  lowerGlobal_checkShrinkReplace_of_source_apart accepted globalAt builder graphs
    (ReplacementDemandSourceApart.of_owner_shapes builder (cfg_global_blocks module global) rfl
      (lower_globalTypeTables module) (lower_signatureTables module) rfl rfl graphs shapes) label

#print axioms ReplacementDemandSourceApart.of_owner_shapes
#print axioms lowerContextAt_checkShrinkReplace_of_owner_shapes
#print axioms lowerGlobal_checkShrinkReplace_of_owner_shapes

end Goose.Lower.Validation
