import Goose.Core.Demand

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core

def argumentDemandNode : Arg → DemandNode
  | .byVal expression => .expression expression
  | .byRef _ place => .place place

end Goose.Lower.Validation.ReplacementContentFlowSource
