import Goose.Lower.DemandCallSliceSequenceStage
import Goose.Lower.DemandCallFuel
import Goose.Lower.DemandCallArgumentCells
import Goose.Lower.DemandCallSplitBooleanStage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive LocalSliceArguments (access : AccessEnv) : List Arg → Prop
  | nil : LocalSliceArguments access []
  | cons {borrow : Mutability} {slot : VarId} {mutability : Mutability} {element : Ty} {rest : List Arg}
      (type : access.placeType? (.var slot) = some (.slice mutability element))
      (tail : LocalSliceArguments access rest) : LocalSliceArguments access (.byRef borrow (.var slot) :: rest)


inductive LocalSliceBooleanArguments (access : AccessEnv) : List Arg → Prop
  | nil : LocalSliceBooleanArguments access []
  | boolean (boolean : Bool) {rest : List Arg} (tail : LocalSliceBooleanArguments access rest) :
      LocalSliceBooleanArguments access (.byVal (.bool boolean) :: rest)
  | reference {borrow : Mutability} {slot : VarId} {mutability : Mutability} {element : Ty} {rest : List Arg}
      (type : access.placeType? (.var slot) = some (.slice mutability element))
      (tail : LocalSliceBooleanArguments access rest) : LocalSliceBooleanArguments access (.byRef borrow (.var slot) :: rest)


theorem LocalSliceArguments.toBoolean {access : AccessEnv} {arguments : List Arg}
    (form : LocalSliceArguments access arguments) : LocalSliceBooleanArguments access arguments := by
  induction form with
  | nil => exact .nil
  | cons type tail ih => exact .reference type ih

theorem LocalSliceArguments.noBoolean {access : AccessEnv} {arguments : List Arg}
    (form : LocalSliceArguments access arguments) (boolean : Bool) : .byVal (.bool boolean) ∉ arguments := by
  induction form with
  | nil => simp
  | cons type tail ih => simp [ih]

#print axioms LocalSliceArguments.toBoolean
#print axioms LocalSliceArguments.noBoolean
end Goose.Lower
