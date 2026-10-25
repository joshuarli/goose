import Goose.Lower.Validation.StorageSourceOutputs
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem storageSourceOutputs (env : Core.TEnv) (results : List Ty) : StorageSourceOutputs env results := by
  constructor
  · intro place info first last source before after value generated run live
    exact lowerPlace_generated_typed place source run live generated
  · intro view element writable first last source before after value generated run live
    exact lowerView_generated_typed view source run live generated
  · intro place info first last source writable before after value generated run live
    exact lowerPlace_generated_writable_typed place source writable run live generated

end Goose.Lower.Validation
