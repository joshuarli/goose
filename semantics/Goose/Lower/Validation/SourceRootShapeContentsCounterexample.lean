import Goose.Lower.Validation.SourceRootShapeCounterexample
import Goose.Lower.CoreToGir
import Goose.GIR.Validate

namespace Goose.Lower.Validation.SourceRootShapeContentsCounterexample

#guard match Core.validate SourceRootShapeCounterexample.module with | .ok () => true | .error _ => false

#guard match GIR.validate (Lower.lower SourceRootShapeCounterexample.module) with
  | .ok () => false
  | .error rejection => rejection.code == .v050 && rejection.message ==
      "function global_reference content root info for parameter 0 omits a root passed at a call site"

end Goose.Lower.Validation.SourceRootShapeContentsCounterexample
