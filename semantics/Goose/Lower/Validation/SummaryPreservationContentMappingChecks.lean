import Goose.GIR.Effects

namespace Goose.Lower.Validation.SummaryPreservation.ContentMappingChecks

open Goose.Core Goose.GIR

private def refSlice : Ty := .ref .mutable (.slice .mutable (.int .i64))

private def caller : Func :=
  { name := "cross-parameter-contents"
    params := [refSlice, refSlice]
    results := []
    slots := #[]
    scopes := #[]
    blocks := #[]
    roots := { params := #[(0, [.param 0]), (1, [.param 1])], contents := #[(0, [.param 1]), (1, [])] }
    summary := .unknown
    org := none }

private def provenance : Prov := ⟨#[], #[[.param 0], [.param 1]]⟩

#guard argumentContents caller provenance 0 == [.param 1]
#guard argumentContents caller provenance 1 == []
#guard mapContentRoots caller provenance [0, 1] [.param 1] == [.param 1]
#guard mapContentRoots caller provenance [0, 1] [.param 0] == [.param 0]
#guard mapContentRoots caller provenance [0, 1] [.global 2] == [.global 2]
#guard mapContentRoots { caller with roots := { params := #[(1, [])] } }
  provenance [0, 1] [.param 1] == []

end Goose.Lower.Validation.SummaryPreservation.ContentMappingChecks
