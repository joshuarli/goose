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
      .letS 0 (.arrLit (.grow (.int .u8)) []) 0,
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
    (some (.bytes bytes [20] 0)))

private def ownerImplementation (statement : Stmt) : Impl :=
  implementation (.mk 0 [
    .letS 0 (.arrLit arrays []) 0,
    .letS 1 (.arrLit arrays []) 0,
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
