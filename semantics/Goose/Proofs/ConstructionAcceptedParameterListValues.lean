import Goose.Proofs.ConstructionAcceptedParameterListDescriptors
import Goose.Proofs.ConstructionAcceptedStatefulArgumentList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

inductive ScalarTypesRepresented : List Ty → List Value → Prop
  | nil : ScalarTypesRepresented [] []
  | cons {ty : Ty} {value : Value} {types : List Ty} {values : List Value}
      (represented : ValueRepresentation ty value) (tail : ScalarTypesRepresented types values) :
      ScalarTypesRepresented (ty :: types) (value :: values)

theorem StatefulScalarValues.types {specifications : List (Expr × Ty)} {values : List Value}
    (valid : StatefulScalarValues specifications values) : ScalarTypesRepresented (specifications.map Prod.snd) values := by
  induction valid with
  | nil => exact .nil
  | cons represented tail ih => exact .cons represented ih

theorem ScalarParameterDescriptors.bindValues {implementation : Impl} {index : Nat}
    {parameters : List Param} {types : List Ty} (descriptors : ScalarParameterDescriptors implementation index parameters types)
    {values : List Value} (represented : ScalarTypesRepresented types values) :
    ScalarParameterValues implementation index parameters values := by
  induction descriptors generalizing values with
  | nil index =>
    cases represented
    exact .nil index
  | cons parameterAt descriptor declared mode scalar tail ih =>
    cases represented with
    | cons head rest => exact .cons parameterAt descriptor declared scalar head (ih rest)

theorem ScalarParameterDescriptors.lengths {implementation : Impl} {index : Nat} {parameters : List Param} {types : List Ty}
    (descriptors : ScalarParameterDescriptors implementation index parameters types) : parameters.length = types.length := by
  induction descriptors with
  | nil => rfl
  | cons parameterAt descriptor declared mode scalar tail ih => simpa using ih

#print axioms ScalarParameterDescriptors.lengths
#print axioms StatefulScalarValues.types
#print axioms ScalarParameterDescriptors.bindValues
end Goose.Proofs.ConstructionAcceptedExecution
