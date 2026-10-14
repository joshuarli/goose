import Goose.Construct.Typing

namespace Goose.Construct.TypingChecks
open Goose.Core (Rule)

private def variables : Array LocalVar :=
  #[⟨"array", .grow (.int .u8), .immutable, 0, 0⟩,
    ⟨"scalar", .int .i64, .immutable, 0, 0⟩]

private def implementation : Impl :=
  ⟨"builder", #[], #[⟨.varr (.int .u8), .value, none⟩], variables,
    .mk 0 [] none, .unknown⟩

private def module : Module :=
  ⟨#[], #[.int .u8, .varr (.int .u8)], #[], #[implementation],
    #[⟨0, "builder", [], [[]], []⟩], 0, #[], #[], #[⟨0, []⟩]⟩

private def env : TypingEnv :=
  { module := module, implementation := some implementation,
    variables := variables, visible := [0, 1], scope := 0, loops := 0, globalLimit := 0 }

private def expressionAccepts (expression : Expr) (expected : List Ty) : Bool :=
  match (typeExpr 256 env expression).run 2 with
  | .ok (types, _) => types == expected
  | .error _ => false

private def statementRejects (statement : Stmt) (rule : Rule) : Bool :=
  match (typeStatement 256 env statement).run 2 with
  | .ok _ => false
  | .error rejection => rejection.rule == rule

#guard !expressionAccepts (.read (.var 0)) [.grow (.int .u8)]
#guard expressionAccepts (.copy (.varr (.int .u8)) (.var 0) 0) [.varr (.int .u8)]
#guard expressionAccepts (.bytes (.varr (.int .u8)) [0, 255] 0) [.varr (.int .u8)]
#guard !expressionAccepts (.bytes (.arr (.int .u8) 3) [0, 255] 0) [.arr (.int .u8) 3]
#guard !expressionAccepts (.values [.lit .u8 1, .lit .u8 2]) [.int .u8, .int .u8]
#guard !expressionAccepts (.resultLocal 0 0) [.grow (.int .u8)]
#guard statementRejects (.assign (.var 1) (.lit .i64 2) 0) .mut
#guard !statementRejects (.expr (.push (.var 0) (.lit .u8 2)) 0) .mut
#guard statementRejects (.expr (.bytes (.varr (.int .u8)) [] 0) 0) .type
#guard statementRejects (.appendValue (.var 0) (.bytes (.varr (.int .u8)) [2] 0) 0) .type
#guard statementRejects (.appendConstruct (.var 0) (.arrLit (.arr (.int .u8) 1) [.lit .u8 2]) 0) .type
#guard statementRejects (.expr (.call 0 [] 0) 0) .type
#guard match (typeExpr 256 { env with request := .elementRun } (.call 0 [] 0)).run 2 with
  | .error rejection => rejection.rule == .call
  | .ok _ => false
#guard match checkType module (.limited (.varr (.int .u8)) 2) with
  | .error rejection => rejection.rule == .type
  | .ok _ => false
#guard match checkType module (.growshrink (.varr (.int .u8))) with
  | .error rejection => rejection.rule == .type
  | .ok _ => false
#guard !(Ty.arr (.int .u8) 1).adaptsTo (.arr (.int .u8) 2)
#guard !(Ty.arr (.int .u8) 1).adaptsTo (.arr (.int .i8) 1)

#guard expressionAccepts (.push (.var 0) (.lit .u8 2)) [.ref .mutable (.int .u8)]
#guard expressionAccepts (.cmp .eq (.bool true) (.bool false)) [.bool]
#guard !expressionAccepts (.cmp .lt (.bool true) (.bool false)) [.bool]
#guard !expressionAccepts (.un .neg (.lit .u8 2) 0) [.int .u8]
#guard !expressionAccepts (.conv .widen (.int .i8) (.lit .i64 2) 0) [.int .i8]
#guard expressionAccepts (.conv .widen (.int .i64) (.lit .i8 2) 0) [.int .i64]

end Goose.Construct.TypingChecks
