import Goose.Construct.GIR.Typing

namespace Goose.Construct.GIR.FillTypeChecks

private def environment (element : Ty) : TyEnv := {
  slots := #[]
  globals := #[]
  sigs := #[]
  vals := #[some (.data element)] }
private def acceptsFill (element : Ty) : Bool :=
  (Op.resultTy (environment element) (.arrFill (.arr element 1) 0)).isOk
private def acceptsLiteral (element : Ty) : Bool :=
  (Op.resultTy (environment element) (.arrLit (.arr element 1) [0])).isOk

#guard !acceptsFill (.grow (.int .u8))
#guard !acceptsLiteral (.grow (.int .u8))
#guard !acceptsFill (.varr (.int .u8))
#guard !acceptsLiteral (.varr (.int .u8))
#guard acceptsFill (.int .u8)
#guard acceptsLiteral (.int .u8)

end Goose.Construct.GIR.FillTypeChecks
