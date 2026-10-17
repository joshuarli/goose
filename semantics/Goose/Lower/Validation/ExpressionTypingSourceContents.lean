import Goose.Core.Typing

namespace Goose.Lower.Validation

open Goose.Core

def ContentsTarget : Ty → Prop
  | .arr .. | .grow .. | .growshrink .. | .limited .. | .structT .. => True
  | _ => False

end Goose.Lower.Validation
