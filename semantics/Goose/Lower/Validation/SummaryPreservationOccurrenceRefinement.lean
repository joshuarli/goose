import Goose.Lower.Validation.SummaryPreservationRootRefinement
import Goose.Lower.Validation.SummaryPreservationProvenance

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def SourceOperandsRefine (func : Func) (upper : Prov) (operands : List ValueId)
    (source : List (List RootRef)) : Prop :=
  ∀ (index : Nat) (value : ValueId), operands[index]? = some value →
    ∃ roots, source[index]? = some roots ∧ RootsRefine func (rootsAt upper.vals value) roots

theorem SourceOperandsRefine.retained {func : Func} {before after : Prov}
    {operands : List ValueId} {source : List (List RootRef)}
    (refined : SourceOperandsRefine func before operands source)
    (bounds : ∀ value ∈ operands, value < before.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    SourceOperandsRefine func after operands source := by
  intro index value row
  obtain ⟨roots, sourceRow, valueRefined⟩ := refined index value row
  refine ⟨roots, sourceRow, ?_⟩
  rw [retained value (bounds value (List.mem_of_getElem? row))]
  exact valueRefined

theorem SourceOperandsRefine.below {func : Func} {actual upper : Prov}
    {operands : List ValueId} {source : List (List RootRef)}
    (refined : SourceOperandsRefine func upper operands source)
    (bounded : ProvenanceBelow actual upper) :
    SourceOperandsRefine func actual operands source := by
  intro index value row
  obtain ⟨roots, sourceRow, valueRefined⟩ := refined index value row
  exact ⟨roots, sourceRow, fun root member => valueRefined root (bounded.vals value root member)⟩

#print axioms SourceOperandsRefine.retained
#print axioms SourceOperandsRefine.below

end Goose.Lower.Validation.SummaryPreservation
