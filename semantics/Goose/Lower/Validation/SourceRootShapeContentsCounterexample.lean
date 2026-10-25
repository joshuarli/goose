import Goose.Lower.Validation.SourceRootShapeCounterexample
import Goose.Lower.CoreToGir
import Goose.GIR.Validate

namespace Goose.Lower.Validation.SourceRootShapeContentsCounterexample

#guard match Core.validate SourceRootShapeCounterexample.module with | .ok () => true | .error _ => false

#guard match GIR.validate (Lower.lower SourceRootShapeCounterexample.module) with
  | .ok () => true
  | .error _ => false

end Goose.Lower.Validation.SourceRootShapeContentsCounterexample
