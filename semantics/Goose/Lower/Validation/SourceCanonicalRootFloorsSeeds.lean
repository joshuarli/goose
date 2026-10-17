import Goose.Lower.Validation.ReplacementProvenance

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR

theorem canonical_start_value_floor (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat) (value : ValueId)
    (root : RootRef) (seed : root ∈ rootsAt (provStart types func).vals value) :
    root ∈ rootsAt (func.provenance results types rootCount).vals value :=
  (provFix_extends results types func _ (provStart types func)).2.2.2 value root seed

theorem canonical_slot_seed_floor (results : Array (List RootRef))
    (types : Array (Option VTy)) (func : Func) (rootCount : Nat) (slot : SlotId)
    (root : RootRef) (seed : root ∈ rootsAt func.slotRootSeeds slot) :
    root ∈ rootsAt (func.provenance results types rootCount).slots slot :=
  (provFix_extends results types func _ (provStart types func)).2.2.1 slot root seed

end Goose.Lower.Validation.SourceCanonicalRootFloors
