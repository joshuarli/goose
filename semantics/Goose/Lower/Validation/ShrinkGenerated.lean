import Goose.Lower.Validation.ShrinkPropagation
import Goose.Lower.Validation.OperandFunctions
import Goose.Lower.Validation.CfgFunctionPaths

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerImpl_emptyFacts_known (module : Core.Module) (impl : Core.Impl)
    (types : Array (Option VTy)) (provenance : Prov) {block : BlockId}
    (bounded : block < (lowerImpl module impl).blocks.size) :
    EmptyStateKnown (emptyFactsAtBlocks (lower module) (lowerImpl module impl) types provenance) block :=
  emptyFactsAtBlocks_known_of_reachable _ _ _ _ (lowerImpl_blocks_nonempty module impl)
    (lowerImpl_operand_bounds module impl).1
    (Func.parameter_ids_bounded_of_dense (lowerImpl_dense_definitions module impl))
    (lowerImpl_paths module impl block bounded)

theorem lowerContextAt_emptyFacts_known (module : Core.Module) (context : Core.Context)
    (impl : Core.Impl) (types : Array (Option VTy)) (provenance : Prov) {block : BlockId}
    (bounded : block < (lowerContextAt module context impl).blocks.size) :
    EmptyStateKnown (emptyFactsAtBlocks (lower module) (lowerContextAt module context impl)
      types provenance) block :=
  emptyFactsAtBlocks_known_of_reachable (lower module) (lowerContextAt module context impl)
    types provenance (lowerImpl_blocks_nonempty module impl)
    (lowerContextAt_operand_bounds module context impl).1
    (Func.parameter_ids_bounded_of_dense (lowerImpl_dense_definitions module impl))
    (lowerContextAt_paths module context impl block bounded)

theorem lowerGlobal_emptyFacts_known (module : Core.Module) (global : Core.Global)
    (types : Array (Option VTy)) (provenance : Prov) {block : BlockId}
    (bounded : block < (lowerGlobal module global).init.blocks.size) :
    EmptyStateKnown (emptyFactsAtBlocks (lower module) (lowerGlobal module global).init
      types provenance) block :=
  emptyFactsAtBlocks_known_of_reachable _ _ _ _ (lowerGlobal_blocks_nonempty module global)
    (lowerGlobal_operand_bounds module global).1
    (Func.parameter_ids_bounded_of_dense (lowerGlobal_dense_definitions module global))
    (lowerGlobal_paths module global block bounded)

end Goose.Lower.Validation
