import Goose.Lower.Validation.Scopes
import Goose.Lower.Validation.SourceCanonicalRootFloorsScopeKeys

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

theorem scopeOrder_keys {pairs : List (Nat × Option Nat)} {start : Nat}
    (checked : scopeOrderError pairs start = none) :
    pairs.map Prod.fst = List.range' start pairs.length := by
  induction pairs generalizing start with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨same, _, checked⟩ := scopeOrderError_cons_success checked
      simp only [List.map_cons, List.length_cons, List.range'_succ, same, ih checked]

theorem scopeOrder_keys_nodup {pairs : List (Nat × Option Nat)} {start : Nat}
    (checked : scopeOrderError pairs start = none) : (pairs.map Prod.fst).Nodup := by
  rw [scopeOrder_keys checked]
  exact List.nodup_range' 1

theorem scopeOrder_key_bound {pairs : List (Nat × Option Nat)}
    (checked : scopeOrderError pairs 0 = none) {scope : Nat}
    (member : scope ∈ pairs.map Prod.fst) : scope < (scopeParents pairs).size := by
  rw [scopeOrder_keys checked] at member
  obtain ⟨index, bounded, same⟩ := List.mem_range'.mp member
  simpa [scopeParents, same] using bounded

end Goose.Lower.Validation.SourceCanonicalRootFloors
