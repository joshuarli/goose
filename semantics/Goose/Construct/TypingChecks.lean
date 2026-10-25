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
#guard statementRejects (.appendConstruct (.var 0) (.arrLit (.arr (.int .u8) 1) [.lit .u8 2] 0) 0) .type
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


private def sliceReferenceEnv : TypingEnv := { env with
  variables := #[⟨"slice-ref",.ref .mutable (.slice .readOnly (.int .u8)),.immutable,0,0⟩]
  visible := [0] }
#guard match (typePlace 256 sliceReferenceEnv (.deref (.read (.var 0)))).run 1 with
  | .ok ((.slice .readOnly (.int .u8), true, true), _) => true
  | _ => false
#guard match (typeExpr 256 sliceReferenceEnv (.read (.var 0))).run 1 with
  | .error rejection => rejection.rule == .type
  | _ => false


#guard match checkType module (.limited (.int .u8) 0) with
  | .error rejection => rejection.rule == .type
  | .ok _ => false


private def readonlySliceEnv : TypingEnv := { env with
  variables := #[⟨"view",.slice .readOnly (.int .u8),.immutable,0,0⟩]
  visible := [0] }
#guard match (typeExpr 256 readonlySliceEnv
    (.ref .mutable (.elem (.val (.read (.var 0))) (.lit .i64 0) 0))).run 1 with
  | .error rejection => rejection.rule == .mut
  | _ => false


#guard expressionAccepts (.ref .mutable (.var 0)) [.ref .mutable (.grow (.int .u8))]
private def splitFields : TyList := .cons (.arr (.int .u8) 1) .nil
private def splitFieldEnv : TypingEnv := { env with
  module := { module with structs := #[⟨1,#[⟨.arr (.int .u8) 1,.mutable,.readOnly,0⟩],"Box"⟩] }
  variables := #[⟨"record",.structT 0 splitFields,.mutable,0,0⟩]
  visible := [0] }
#guard match (typeExpr 256 splitFieldEnv (.ref .mutable (.field (.var 0) 0))).run 1 with
  | .error rejection => rejection.rule == .type
  | _ => false


#guard !(Ty.varr (.int .u8)).adaptsTo (.arr (.int .u8) 2)
private def fixedCopyEnv : TypingEnv := { env with
  variables := #[⟨"source",.arr (.int .u8) 2,.immutable,0,0⟩]
  visible := [0] }
#guard match (typeExpr 256 fixedCopyEnv (.copy (.arr (.int .u8) 3) (.var 0) 0)).run 1 with
  | .error rejection => rejection.rule == .type
  | _ => false
#guard match (typeExpr 256 fixedCopyEnv (.copy (.slice .readOnly (.int .u8)) (.var 0) 0)).run 1 with
  | .error rejection => rejection.rule == .type
  | _ => false


#guard !expressionAccepts (.str (.arr (.int .u8) 2) [.text "x"] 0) [.arr (.int .u8) 2]
#guard expressionAccepts (.str (.arr (.int .u8) 3) [.text "箱"] 0) [.arr (.int .u8) 3]
#guard !expressionAccepts (.str (.arr (.int .u8) 1) [.expr (.lit .u8 1)] 0) [.arr (.int .u8) 1]


#guard match (typeView 256 readonlySliceEnv (.of (.var 0))).run 1 with
  | .error rejection => rejection.rule == .type
  | _ => false

private def valueBlock (statements : List Stmt) (tail : Option Expr := none) : Expr :=
  .blockE (.mk 1 statements tail) 0
#guard expressionAccepts (valueBlock [.breakValue (.lit .u8 7) 0]) [.int .u8]
#guard expressionAccepts (valueBlock [.breakValue (.lit .u8 7) 0] (some (.lit .u8 9))) [.int .u8]
#guard !expressionAccepts (valueBlock [.breakValue (.bool true) 0] (some (.lit .u8 9))) [.int .u8]
#guard !expressionAccepts (valueBlock [.ifS (.bool true)
  (.mk 2 [.breakValue (.lit .u8 7) 0] none) none 0]) [.int .u8]
#guard expressionAccepts (valueBlock [.while (.bool true)
  (.mk 2 [.breakValue (.lit .u8 7) 0] none) 0]) [.int .u8]
#guard !expressionAccepts (valueBlock [.while (.bool true)
  (.mk 2 [.brk 0,.breakValue (.lit .u8 7) 0] none) 0]) [.int .u8]
#guard match (typeStatement 256 env (.while (.bool true)
  (.mk 1 [.breakValue (.lit .u8 7) 0] none) 0)).run 1 with
  | .error rejection => rejection.rule == .block
  | _ => false
#guard expressionAccepts (.ifE (.bool true)
  (.mk 1 [.abort "stop" 0] none) (.mk 2 [] (some (.lit .u8 7))) 0) [.int .u8]

#guard expressionAccepts (valueBlock [] (some (.ifE (.bool true)
  (.mk 2 [.breakValue (.lit .u8 1) 0] none)
  (.mk 3 [.breakValue (.lit .u8 2) 0] none) 0))) [.int .u8]

#guard !expressionAccepts (valueBlock [.breakValue (.resultLocal 0 0) 0]) [.grow (.int .u8)]
#guard match (typeExpr 256 { env with use := .result }
    (valueBlock [.breakValue (.resultLocal 0 0) 0])).run 2 with
  | .ok (types, _) => types == [.grow (.int .u8)]
  | _ => false

end Goose.Construct.TypingChecks

namespace Goose.Construct.TypingChecks

private def receiverTypingEnv (types : List Ty) (requests : List Goose.Core.Request) : TypingEnv :=
  let callee := { implementation with
    params := #[], vars := #[], results := ((types.zip requests).map fun (ty,request) => ⟨ty,request,none⟩).toArray }
  { env with
    module := { module with impls := #[callee] }, variables := (types.map fun ty => ⟨"received",ty,.immutable,0,0⟩).toArray, visible := [], request := .elementRun, resultRequests := [.register] }

private def receiveCallAccepts (types : List Ty) (requests : List Goose.Core.Request) : Bool :=
  match (typeStatement 256 (receiverTypingEnv types requests)
      (.receive [0,1] (.call 0 [] 0) 0)).run 0 with
  | .ok (next,2) => next.visible == [0,1]
  | _ => false

#guard receiveCallAccepts [.int .i64,.bool] [.register,.register]
#guard receiveCallAccepts [.varr (.int .u8),.ref .readOnly (.grow (.int .u8))] [.value,.register]

#guard match (typeStatement 256
    (receiverTypingEnv [.varr (.int .u8),.bool] [.elementRun,.register])
    (.receive [0,1] (.call 0 [] 0) 0)).run 0 with
  | .error rejection => rejection.rule == .call
  | _ => false

private def receivedValuesEnv : TypingEnv :=
  let callee := { implementation with params := #[], vars := #[], results := #[⟨.varr (.int .u8),.value,none⟩] }
  { (receiverTypingEnv [.varr (.int .u8),.bool] [.value,.register]) with
    module := { module with impls := #[callee] } }

#guard match (typeStatement 256 receivedValuesEnv
    (.receive [0,1] (.values [.call 0 [] 0,.bool true]) 0)).run 0 with
  | .ok (next,2) => next.visible == [0,1]
  | _ => false

#guard match (typeStatement 256 receivedValuesEnv
    (.receive [0,1] (.values [.call 0 [] 0,.lit .i64 1]) 0)).run 0 with
  | .error rejection => rejection.rule == .result
  | _ => false

end Goose.Construct.TypingChecks
