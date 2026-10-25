import Goose.Construct.Validate

namespace Goose.Construct.ValidationChecks
open Goose.Core (Rule)

private def emptySummary : Summary := {
  reads := []
  writes := []
  grows := []
  shrinks := []
  rebinds := []
  constructs := []
  needs := []
  escapes := []
  aborts := false
  outputs := false }

private def implementation (body : Block := .mk 0 [] none)
    (variables : Array LocalVar := #[]) (results : Array ResultDescriptor := #[])
    (summary : SummaryAnn := .known emptySummary) : Impl := {
  name := "main"
  params := #[]
  results := results
  vars := variables
  body := body
  summary := summary }

private def mainImpl : Impl := implementation

private def context (impl : Nat := 0) (resultRoots : List (List RootRef) := []) : Context :=
  ⟨impl, "main", [], resultRoots, []⟩

private def baseModule (main : Impl := mainImpl) (impls : Array Impl := #[]) : Module := {
  files := #["test.goose"]
  types := #[]
  globals := #[]
  impls := if impls.isEmpty then #[main] else impls
  contexts := #[context]
  entry := 0
  origins := #[⟨0, 1, "global"⟩]
  structs := #[]
  targets := #[] }

private def accepts (module : Module) : Bool :=
  match validate module with
  | .ok _ => true
  | .error _ => false

private def rejectsWith (module : Module) (rule : Rule) : Bool :=
  match validate module with
  | .error rejection => rejection.rule == rule
  | .ok _ => false

#guard accepts baseModule

private def namedStructModule : Module := {
  (baseModule mainImpl) with
  types := #[.structT 0 .nil]
  structs := #[⟨1, #[], "箱"⟩] }

#guard accepts namedStructModule
#guard rejectsWith { namedStructModule with structs := #[⟨1, #[], ""⟩] } .type

private def expressionModule (expression : Expr) : Module := {
  (baseModule (implementation (.mk 0 [.expr expression 0] none))) with
  origins := #[⟨0, 1, "global"⟩, ⟨0, 2, "global"⟩] }

private def arrayLiteralOrigin : Module :=
  expressionModule (.arrLit (.arr (.int .u8) 1) [.lit .u8 7] 1)
#guard accepts arrayLiteralOrigin
#guard rejectsWith { arrayLiteralOrigin with origins := #[⟨0, 1, "global"⟩] } .type

private def fillOrigin : Module :=
  expressionModule (.fill (.arr (.int .u8) 1) (.lit .u8 7) 1)
#guard accepts fillOrigin
#guard rejectsWith { fillOrigin with origins := #[⟨0, 1, "global"⟩] } .type

private def conditionalOrigin : Module :=
  expressionModule (.ifE (.bool true) (.mk 1 [] (some (.lit .i64 1)))
    (.mk 2 [] (some (.lit .i64 2))) 1)
#guard accepts conditionalOrigin
#guard rejectsWith { conditionalOrigin with origins := #[⟨0, 1, "global"⟩] } .type

private def valueBlockOrigin : Module :=
  expressionModule (.blockE (.mk 1 [] (some (.lit .i64 1))) 1)
#guard accepts valueBlockOrigin
#guard rejectsWith { valueBlockOrigin with origins := #[⟨0, 1, "global"⟩] } .type

private def workerModule (worker : Impl) (resultRoots : List (List RootRef)) : Module := {
  (baseModule mainImpl #[mainImpl, worker]) with
  contexts := #[context, ⟨1, worker.name, [], resultRoots, []⟩] }

private def valueBreakWorker (body : Block) (results : Array ResultDescriptor)
    (variables : Array LocalVar := #[]) : Impl := {
  (implementation body variables results) with name := "value-worker" }

private def referenceSlice : Ty := .ref .mutable (.slice .readOnly (.int .u8))

private def referenceSliceParameterWorker : Impl := {
  (valueBreakWorker (.mk 0 [] none) #[]) with
  params := #[⟨0, .byRef⟩]
  vars := #[⟨"view", referenceSlice, .immutable, 0, 0⟩] }

private def referenceSliceParameterModule : Module := {
  (workerModule referenceSliceParameterWorker []) with
  types := #[referenceSlice]
  contexts := #[context, ⟨1, "value-worker", [(0, [.param 0])], [], []⟩] }

#guard accepts referenceSliceParameterModule

private def referenceSliceLocalWorker : Impl :=
  valueBreakWorker (.mk 0 [] none) #[] #[⟨"view", referenceSlice, .immutable, 0, 0⟩]

#guard rejectsWith (workerModule referenceSliceLocalWorker []) .type

private def noTailValueBreakWorker : Impl := valueBreakWorker
  (.mk 0 [] (some (.blockE
    (.mk 1 [.breakValue (.lit .i64 7) 0] none) 0)))
  #[⟨.int .i64, .register, none⟩]

#guard accepts (workerModule noTailValueBreakWorker [[]])

private def whileValueBreakWorker : Impl := valueBreakWorker
  (.mk 0 [] (some (.blockE (.mk 1 [
    .while (.bool true) (.mk 2 [.breakValue (.lit .i64 7) 0] none) 0] none) 0)))
  #[⟨.int .i64, .register, none⟩]

#guard accepts (workerModule whileValueBreakWorker [[]])

private def multiChannelValueBreakWorker : Impl := valueBreakWorker
  (.mk 0 [] (some (.blockE
    (.mk 1 [.breakValue (.values [.lit .i64 7, .lit .i64 8]) 0] none) 0)))
  #[⟨.int .i64, .register, none⟩, ⟨.int .i64, .register, none⟩]

#guard accepts (workerModule multiChannelValueBreakWorker [[], []])

private def localReferenceValueBreakWorker : Impl := valueBreakWorker
  (.mk 0 [] (some (.blockE (.mk 1 [
    .letS 0 (.lit .i64 7) 0,
    .breakValue (.ref .mutable (.var 0)) 0] none) 0)))
  #[⟨.ref .mutable (.int .i64), .register, none⟩]
  #[⟨"local", .int .i64, .mutable, 1, 0⟩]

#guard rejectsWith (workerModule localReferenceValueBreakWorker [[]]) .block

private def orphan : Impl := { mainImpl with name := "orphan" }
#guard rejectsWith (baseModule mainImpl #[mainImpl, orphan]) .root

private def outOfRangeScope : Impl :=
  implementation (.mk 0 [] none) #[⟨"unused", .int .i64, .immutable, 1, 0⟩]
#guard rejectsWith (baseModule outOfRangeScope) .type

private def incompleteResult : Impl :=
  implementation (.mk 0 [] none) #[] #[⟨.int .i64, .register, none⟩]

private def incompleteModule : Module := {
  (baseModule mainImpl #[mainImpl, incompleteResult]) with
  contexts := #[context, context 1 [[]]] }

#guard rejectsWith incompleteModule .type

private def missingPushOrigin : Impl :=
  implementation
    (.mk 0 [
      .letS 0 (.arrLit (.grow (.int .u8)) [] 0) 0,
      .expr (.push (.var 0) (.lit .u8 1) none) 0] none)
    #[⟨"items", .grow (.int .u8), .mutable, 0, 0⟩]

#guard rejectsWith (baseModule missingPushOrigin) .type

private def missingOrigin : Module := {
  baseModule (implementation (.mk 0 [.expr (.lit .i64 7) 1] none)) with
  origins := #[⟨0, 1, "global"⟩] }

#guard rejectsWith missingOrigin .type

private def nestedScopeGap : Module :=
  baseModule (implementation (.mk 0 [
    .ifS (.bool true) (.mk 2 [] none) none 0] none))

#guard rejectsWith nestedScopeGap .type

private def forgedSummary : Module := {
  baseModule mainImpl #[
    implementation (.mk 0 [.assign (.global 0) (.lit .i64 1) 0] none)] with
  globals := #[⟨"counter", .int .i64, .mutable, .lit .i64 0, 0⟩]
  contexts := #[context, context 1] }

#guard rejectsWith forgedSummary .summary

private def targetSummary : Summary := { emptySummary with needs := [0], escapes := [0] }

private def inactiveTargetModule : Module := {
  (baseModule mainImpl #[
    implementation (.mk 0 [.returnFrom 0 [.lit .i64 7] 0] none) #[] #[] (.known targetSummary),
    implementation (.mk 0 [.retValues [.lit .i64 9] 0] none) #[] #[⟨.int .i64, .register, none⟩]]) with
  contexts := #[context, context 1 [[]]]
  targets := #[⟨1, []⟩] }

#guard rejectsWith inactiveTargetModule .call

private def bytes : Ty := .varr (.int .u8)
private def arrays : Ty := .grow bytes

private def mutatingProducer (owner : Nat) : Expr :=
  .blockE (.mk 1 [.expr (.push (.var owner) (.bytes bytes [10] 0) (some 0)) 0]
    (some (.bytes bytes [20] 0))) 0

private def ownerImplementation (statement : Stmt) : Impl :=
  implementation (.mk 0 [
    .letS 0 (.arrLit arrays [] 0) 0,
    .letS 1 (.arrLit arrays [] 0) 0,
    statement] none)
    #[⟨"owner", arrays, .mutable, 0, 0⟩, ⟨"other", arrays, .mutable, 0, 0⟩]

private def growingConstructor : Module :=
  baseModule (ownerImplementation
    (.expr (.push (.var 0) (mutatingProducer 0) (some 0)) 0))

#guard rejectsWith growingConstructor .call

private def aliasedWholeReplacement : Module :=
  baseModule (ownerImplementation
    (.assignWhole (.var 0) (.copy arrays (.var 0) 0) 0))

#guard rejectsWith aliasedWholeReplacement .whole

private def exitSlice : Ty := .slice .readOnly (.int .u8)

private def exitRootCaller : Impl :=
  ⟨"target-caller", #[⟨0, .byValue⟩, ⟨1, .byValue⟩],
    #[⟨exitSlice, .register, none⟩],
    #[⟨"first", exitSlice, .immutable, 0, 0⟩, ⟨"second", exitSlice, .immutable, 0, 0⟩],
    .mk 0 [.expr (.call 2 [.byVal (.read (.var 1))] 0) 0] none, .unknown⟩

private def exitRootHelper : Impl :=
  ⟨"helper", #[⟨0, .byValue⟩], #[], #[⟨"source", exitSlice, .immutable, 0, 0⟩],
    .mk 0 [.returnFrom 0 [.read (.var 0)] 0] none, .unknown⟩

private def exitRootCallerContext : Context :=
  ⟨1, "target-caller", [(0, [.param 0]), (1, [.param 1])], [[.param 0]], []⟩

private def exitRootHelperContext : Context :=
  ⟨2, "helper", [(0, [.param 0])], [], []⟩

private def missingExitRoot : Module := {
  (baseModule mainImpl #[mainImpl, exitRootCaller, exitRootHelper]) with
  contexts := #[context, exitRootCallerContext, exitRootHelperContext]
  targets := #[⟨1, []⟩] }

#guard missingExitRoot.contexts.toList.all fun context =>
  match checkContext missingExitRoot context with
  | .ok _ => true
  | .error _ => false

#guard match checkModuleExitRoots missingExitRoot with
  | .error rejection => rejection.rule == .result
  | .ok _ => false

#guard rejectsWith missingExitRoot .result

end Goose.Construct.ValidationChecks
