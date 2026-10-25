import Goose.Lower.EachStatic
import Goose.Lower.TypedExpressionFamily
import Goose.Lower.TypedTransfers

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedStatementLoopSimulation_each (n : Nat) (cfg : Cfg) (results : List Ty)
    (expressions : ∀ fuel, fuel < n → TypedExpressionFamily fuel cfg)
    (blocks : ∀ fuel, fuel < n → ∀ loop pre pre' body,
      TypedBlockLoopSimulation fuel cfg results (some loop) pre pre' false body)
    (shapes : ∀ place, PlaceOwnerShape cfg results place)
    (loop : Option LoopCtx) (x : VarId) (index : Option VarId) (view : View)
    (byRef : Bool) (body : Core.Block) (origin : OriginId) :
    TypedStatementLoopSimulation n cfg results loop (.forEach x index view byRef body origin) := by
  cases n with
  | zero => exact typedStatementLoopSimulation_zero cfg results loop _
  | succ n =>
    cases n with
    | zero => exact typedStatementLoopSimulation_each_one cfg results loop x index view byRef body origin
    | succ fuel =>
      cases view with
      | of place =>
        apply typedStatementLoopSimulation_each_place
          ((expressions fuel (by omega)).place results place) (shapes place)
        intro k bound context pre pre'
        exact blocks k (by omega) context pre pre' body
      | val expr =>
        apply typedStatementLoopSimulation_each_value
          ((expressions fuel (by omega)).expr results expr)
        intro k bound context pre pre'
        exact blocks k (by omega) context pre pre' body

end Goose.Lower
