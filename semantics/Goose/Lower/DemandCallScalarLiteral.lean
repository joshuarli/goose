import Goose.Lower.DemandCallBodyReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive CallScalarLiteral : Expr → Val → Op → Prop
  | boolean (value : Bool) : CallScalarLiteral (.bool value) (.bool value) (.constBool value)
  | integer (type : IntTy) (value : Int) : CallScalarLiteral (.lit type value) (.int type value) (.constInt type value)

end Goose.Lower
