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


inductive LocalSliceScalarArguments (access : AccessEnv) : List Arg → Prop
  | nil : LocalSliceScalarArguments access []
  | literal {expression : Expr} {value : Val} {operation : Op} {rest : List Arg}
      (literal : CallScalarLiteral expression value operation) (tail : LocalSliceScalarArguments access rest) :
      LocalSliceScalarArguments access (.byVal expression :: rest)
  | reference {borrow : Mutability} {slot : VarId} {mutability : Mutability} {element : Ty} {rest : List Arg}
      (type : access.placeType? (.var slot) = some (.slice mutability element))
      (tail : LocalSliceScalarArguments access rest) : LocalSliceScalarArguments access (.byRef borrow (.var slot) :: rest)

theorem LocalSliceBooleanArguments.toScalar {access : AccessEnv} {arguments : List Arg}
    (form : LocalSliceBooleanArguments access arguments) : LocalSliceScalarArguments access arguments := by
  induction form with
  | nil => exact .nil
  | boolean boolean tail ih => exact .literal (.boolean boolean) ih
  | reference type tail ih => exact .reference type ih

theorem LocalSliceBooleanArguments.noInteger {access : AccessEnv} {arguments : List Arg}
    (form : LocalSliceBooleanArguments access arguments) (type : IntTy) (number : Int) : .byVal (.lit type number) ∉ arguments := by
  induction form with
  | nil => simp
  | boolean boolean tail ih => simp [ih]
  | reference type tail ih => simp [ih]

#print axioms LocalSliceBooleanArguments.toScalar
#print axioms LocalSliceBooleanArguments.noInteger

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
