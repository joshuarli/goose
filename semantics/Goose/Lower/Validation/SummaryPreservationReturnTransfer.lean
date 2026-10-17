import Goose.Lower.Validation.SummaryPreservationReturnLedger

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def ReturnBoundsPreserved (expected : List RootRef) (before : LS) (oldUpper : Prov)
    (after : LS) (newUpper : Prov) : Prop :=
  ∀ declared, (∀ root ∈ expected, root ∈ declared) →
    BuilderReturnsBound oldUpper declared before → BuilderReturnsBound newUpper declared after

namespace ReturnBoundsPreserved

variable {expected : List RootRef} {before middle after : LS} {oldUpper middleUpper newUpper : Prov}

theorem refl (expected : List RootRef) (state : LS) (upper : Prov) :
    ReturnBoundsPreserved expected state upper state upper := fun _ _ prior => prior

theorem trans (first : ReturnBoundsPreserved expected before oldUpper middle middleUpper)
    (second : ReturnBoundsPreserved expected middle middleUpper after newUpper) :
    ReturnBoundsPreserved expected before oldUpper after newUpper :=
  fun declared subset prior => second declared subset (first declared subset prior)

theorem frame {le : LEnv} {scopeCount : Nat}
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index)
    (returns : ReturnMembershipFrame before after) :
    ReturnBoundsPreserved expected before oldUpper after newUpper :=
  fun _ _ prior => prior.frame symbols size retained returns

theorem expected_mono {larger : List RootRef}
    (preserved : ReturnBoundsPreserved expected before oldUpper after newUpper)
    (subset : ∀ root ∈ expected, root ∈ larger) :
    ReturnBoundsPreserved larger before oldUpper after newUpper :=
  fun declared declaredBound prior => preserved declared (fun root member => declaredBound root (subset root member)) prior

theorem emitTerm {state : LS} {upper : Prov} {le : LEnv}
    (current : state.CurrentBlocks) (term : Term)
    (added : ∀ value origin, term = .ret [value] origin →
      ∀ root ∈ rootsAt upper.vals value, root ∈ expected) :
    ReturnBoundsPreserved expected state upper (Goose.Lower.emitTerm term le state).2 upper := by
  intro declared subset prior
  exact prior.emitTerm current term (fun value origin same root member => subset root (added value origin same root member))

theorem apply_expected (preserved : ReturnBoundsPreserved expected before oldUpper after newUpper)
    (prior : BuilderReturnsBound oldUpper expected before) : BuilderReturnsBound newUpper expected after :=
  preserved expected (fun _ member => member) prior

#print axioms trans
#print axioms frame
#print axioms emitTerm

end ReturnBoundsPreserved

end Goose.Lower.Validation.SummaryPreservation
