import Goose.Lower.Validation.EmittedTypingSourceResults
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_source_results (env : Core.TEnv) (results : List Ty) :
    EmittedSourceResults env results := by
  constructor
  · intro expr type start finish source before after value generated run live
    exact lowerExpr_generated_typed expr source run live generated
  · intro place info start finish source before after value generated run live
    exact lowerPlace_generated_typed place source run live generated
  · intro view element writable start finish source before after value generated run live
    exact lowerView_generated_typed view source run live generated

end Goose.Lower.Validation
