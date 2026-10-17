import Goose.Lower.Validation.StorageWalkActions
import Goose.Lower.Validation.ScopeFlowFinish

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem storageWalk_initial_configuration (slots : Array Slot) (env : LEnv) (types : List VTy) :
    StorageWalkConfiguration slots (fun _ => []) (fun _ => []) (scopeInitialState env types) := by
  have old := scopeInitialState_configuration #[] env types
  refine ⟨⟨?_, old.builder.current⟩, old.openCurrent, old.bounded, old.edges⟩
  intro block body row
  have bound := (Array.getElem?_eq_some_iff.mp row).1
  have zero : block = 0 := by have size := scopeInitialState_size env types; nat_omega
  subst block
  have same : body = (scopeInitialState env types).blocks[0] :=
    (Array.getElem?_eq_some_iff.mp row).2.symm
  subst body
  exact StorageWalkTrace.nil []

#print axioms storageWalk_initial_configuration

end Goose.Lower.Validation
