import Goose.Core.Syntax

namespace Goose.Lower.Validation

open Goose.Core

def BindingTarget (profile : ArtifactProfile) : Ty → Prop
  | .grow _ | .growshrink _ | .limited _ _ => profile = .shrink
  | _ => True

end Goose.Lower.Validation
