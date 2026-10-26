import Goose.Construct.Validate

namespace Goose.Construct.FillTypeChecks

private def invalid : Ty := .arr (.grow (.int .u8)) 1
private def expression : Expr := .fill invalid (.bytes (.arr (.int .u8) 1) [65] 0) 0
private def module : Module :=
  ⟨#["fill.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[], .mk 0 [.expr expression 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "expr"⟩], #[], #[]⟩
private def environment : TypingEnv :=
  ⟨module, none, #[], [], 0, 0, .ordinary, .value, [], none, 0⟩

#guard !(validate module).isOk
#guard !(typeExpr 32 environment expression 0).isOk
#guard (typeExpr 32 environment (.fill (.arr (.int .u8) 2) (.lit .u8 65) 0) 0).isOk
#guard (typeExpr 32 environment
  (.fill (.arr (.varr (.int .u8)) 1) (.bytes (.arr (.int .u8) 1) [65] 0) 0) 0).isOk

end Goose.Construct.FillTypeChecks
