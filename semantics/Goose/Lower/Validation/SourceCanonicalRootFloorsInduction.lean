import Goose.Lower.Validation.SourceCanonicalRootFloorsAccess
import Goose.Lower.Validation.SourceCanonicalRootFloorsExpressions
import Goose.Lower.Validation.SourceCanonicalRootFloorsBlocks
import Goose.Lower.Validation.SourceCanonicalRootFloorsArguments
import Goose.Lower.Validation.SourceCanonicalRootFloorsCalls

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

mutual

theorem expression_canonical_floor (expression : Expr) : ExpressionFloor expression := by
  cases expression with
  | read place => exact read_floor place
  | ref mode place => exact reference_floor mode place (place_canonical_floor place)
  | slice mode view low high origin => exact slice_floor mode view low high origin (view_canonical_floor view)
  | push place expression origin => exact push_floor place expression origin (place_canonical_floor place)
  | ifE condition yes no => exact conditional_floor condition yes no
  | blockE body => exact block_expression_floor body (block_canonical_floor body)
  | call callee arguments origin => exact call_floor callee arguments origin (arguments_canonical_floor arguments)
  | _ => exact scalar_floor _ trivial
termination_by sizeOf expression

theorem place_canonical_floor (place : Place) : PlaceFloor place := by
  cases place with
  | var slot => exact variable_floor slot
  | global index => exact global_floor index
  | field owner index => exact field_floor owner index (place_canonical_floor owner)
  | deref expression => exact dereference_floor expression (expression_canonical_floor expression)
  | elem view index origin => exact element_floor view index origin (view_canonical_floor view)
termination_by sizeOf place

theorem view_canonical_floor (view : View) : ViewFloor view := by
  cases view with
  | of place => exact owner_view_floor place (place_canonical_floor place)
  | val expression => exact value_view_floor expression (expression_canonical_floor expression)
termination_by sizeOf view

theorem block_canonical_floor (body : Block) : BlockFloor body := by
  cases body with
  | mk scope statements tail =>
    apply block_floor scope statements tail
    cases tail with
    | none => trivial
    | some expression => exact expression_canonical_floor expression
termination_by sizeOf body

theorem arguments_canonical_floor (arguments : List Arg) : ArgumentsFloor arguments := by
  cases arguments with
  | nil => exact arguments_nil_floor
  | cons argument rest =>
    cases argument with
    | byVal expression =>
        exact arguments_byValue_floor expression rest (expression_canonical_floor expression) (arguments_canonical_floor rest)
    | byRef mode place =>
        exact arguments_byReference_floor mode place rest (place_canonical_floor place) (arguments_canonical_floor rest)
termination_by sizeOf arguments

end

end Goose.Lower.Validation.SourceCanonicalRootFloors
