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

namespace Goose.Construct.ValidationChecks

private def clearedOwner (owner : Ty) (aliasValue : Option (Ty × Expr) := none) : Module :=
  let aliasVariables := aliasValue.toList.map fun (ty,_) => (⟨"alias",ty,.immutable,0,0⟩ : LocalVar)
  let bindings := aliasValue.toList.map fun (_,expression) => Stmt.letS 1 expression 0
  let uses := aliasValue.toList.map fun (ty,_) => Stmt.print [.expr (match ty with
    | .ref .. => .read (.deref (.read (.var 1)))
    | _ => .read (.var 1))] 0
  let body := Block.mk 0 ([.letS 0 (.arrLit owner [.lit .i64 7] 0) 0] ++ bindings ++ [.clear (.var 0) 0] ++ uses) none
  let main := implementation body (#[⟨"owner",owner,.mutable,0,0⟩] ++ aliasVariables.toArray) #[] .unknown
  { (baseModule main) with contexts := #[⟨0,"main",if aliasValue.isSome then [(1,[.local 0])] else [],[],[]⟩] }

private def elementAlias : Ty × Expr :=
  ⟨.ref .readOnly (.int .i64),.ref .readOnly (.elem (.of (.var 0)) (.lit .i64 0) 0)⟩

private def sliceAlias : Ty × Expr :=
  ⟨.slice .readOnly (.int .i64),.slice .readOnly (.of (.var 0)) .omitted .omitted 0⟩

#guard accepts (clearedOwner (.grow (.int .i64)))
#guard accepts (clearedOwner (.growshrink (.int .i64)))
#guard rejectsWith (clearedOwner (.growshrink (.int .i64)) (some elementAlias)) .shrink
#guard rejectsWith (clearedOwner (.growshrink (.int .i64)) (some sliceAlias)) .shrink
#guard rejectsWith (clearedOwner (.grow (.int .i64)) (some elementAlias)) .shrink

private def clearedThroughCall : Module :=
  let owner := Ty.growshrink (.int .i64)
  let module := clearedOwner owner (some elementAlias)
  let main := module.impls[0]
  let main := { main with body := .mk 0 [
    .letS 0 (.arrLit owner [.lit .i64 7] 0) 0,
    .letS 1 elementAlias.2 0,
    .expr (.call 1 [.byRef .mutable (.var 0)] 0) 0] none }
  let helper : Impl := ⟨"clear",#[⟨0,.byRef⟩],#[],
    #[⟨"owner",.ref .mutable owner,.immutable,0,0⟩],
    .mk 0 [.clear (.deref (.read (.var 0))) 0] none,
    .known { emptySummary with reads := [.param 0], shrinks := [.param 0] }⟩
  { module with impls := #[main,helper], contexts := #[module.contexts[0],⟨1,"clear",[(0,[.param 0])],[],[]⟩] }

#guard rejectsWith clearedThroughCall .shrink

private def clearAfterAliasScope : Module :=
  let owner := Ty.growshrink (.int .i64)
  let main := implementation (.mk 0 [
    .letS 0 (.arrLit owner [.lit .i64 7] 0) 0,
    .ifS (.bool true) (.mk 1 [.letS 1 elementAlias.2 0] none) none 0,
    .clear (.var 0) 0] none)
    #[⟨"owner",owner,.mutable,0,0⟩,⟨"alias",elementAlias.1,.immutable,1,0⟩] #[] .unknown
  { (baseModule main) with contexts := #[⟨0,"main",[(1,[.local 0])],[],[]⟩] }

#guard accepts clearAfterAliasScope

end Goose.Construct.ValidationChecks

namespace Goose.Construct.ValidationChecks

private def retainedShrink (body : Stmt) : Module :=
  let owner := Ty.growshrink (.int .i64)
  let original := clearedThroughCall
  let main := { original.impls[0] with
    vars := #[⟨"owner",owner,.mutable,0,0⟩]
    body := .mk 0 [.letS 0 (.arrLit owner [.lit .i64 7] 0) 0,body] none }
  let helper := { original.impls[1] with
    results := #[⟨.int .i64,.register,none⟩]
    body := .mk 0 [.clear (.deref (.read (.var 0))) 0,.retValues [.lit .i64 0] 0] none }
  let sink : Impl := ⟨"sink",#[⟨0,.byRef⟩,⟨1,.byValue⟩],#[],
    #[⟨"element",.ref .readOnly (.int .i64),.immutable,0,0⟩,⟨"scalar",.int .i64,.immutable,0,0⟩],
    .mk 0 [] none,.known emptySummary⟩
  { original with
    impls := #[main,helper,sink], contexts := #[context,⟨1,"clear",[(0,[.param 0])],[[]],[]⟩,⟨2,"sink",[(0,[.param 0])],[],[]⟩] }

private def clearCall : Expr := .call 1 [.byRef .mutable (.var 0)] 0
private def firstElement : Place := .elem (.of (.var 0)) (.lit .i64 0) 0

#guard rejectsWith (retainedShrink (.expr
  (.call 2 [.byRef .readOnly firstElement,.byVal clearCall] 0) 0)) .shrink
#guard rejectsWith (retainedShrink (.assign firstElement clearCall 0)) .shrink
#guard rejectsWith (retainedShrink (.print
  [.expr (.read (.elem (.of (.var 0)) clearCall 0))] 0)) .shrink

end Goose.Construct.ValidationChecks

namespace Goose.Construct.ValidationChecks

private def clearIterationSource : Module :=
  let owner := Ty.growshrink (.int .i64)
  let main := implementation (.mk 0 [
    .letS 0 (.arrLit owner [.lit .i64 7,.lit .i64 8] 0) 0,
    .forEach 1 none (.of (.var 0)) false (.mk 1 [.clear (.var 0) 0] none) 0] none)
    #[⟨"owner",owner,.mutable,0,0⟩,⟨"element",.int .i64,.immutable,1,0⟩] #[] .unknown
  baseModule main

#guard rejectsWith clearIterationSource .shrink

end Goose.Construct.ValidationChecks

namespace Goose.Construct.ValidationChecks

private def viewAfterInitializerShrink (prior : Bool) (nested : Bool := false) : Module :=
  let owner := Ty.growshrink (.int .i64)
  let view := Ty.slice .readOnly (.int .i64)
  let sampled := Expr.slice .readOnly (.of (.var 0)) .omitted .omitted 0
  let id := if prior then 2 else 1
  let initialBindings := if prior then [Stmt.letS 1 sampled 0] else []
  let nestedBindings := if nested then [Stmt.letS 2 sampled 0] else []
  let initializer := Expr.blockE (.mk 1 (nestedBindings ++ [.clear (.var 0) 0]) (some sampled)) 0
  let variables := #[⟨"owner",owner,.mutable,0,0⟩] ++
    (if prior then #[⟨"prior",view,.immutable,0,0⟩] else #[]) ++
    #[⟨"received",view,.immutable,0,0⟩] ++
    (if nested then #[⟨"nested",view,.immutable,1,0⟩] else #[])
  let body := Block.mk 0 ([.letS 0 (.arrLit owner [.lit .i64 7] 0) 0] ++ initialBindings ++
    [.letS id initializer 0,.print [.expr (.read (.var id))] 0]) none
  let main := implementation body variables #[] .unknown
  let annotations := [(1,[RootRef.local 0])] ++ (if prior || nested then [(2,[.local 0])] else [])
  { (baseModule main) with contexts := #[⟨0,"main",annotations,[],[]⟩] }

#guard accepts (viewAfterInitializerShrink false)
#guard rejectsWith (viewAfterInitializerShrink true) .shrink
#guard rejectsWith (viewAfterInitializerShrink false true) .shrink

private def nestedInitializersShrink : Module :=
  let owner := Ty.growshrink (.int .i64)
  let view := Ty.slice .readOnly (.int .i64)
  let sampled := Expr.slice .readOnly (.of (.var 0)) .omitted .omitted 0
  let inner := Expr.blockE (.mk 2 [.clear (.var 0) 0] (some sampled)) 0
  let outer := Expr.blockE (.mk 1 [.letS 2 inner 0] (some (.read (.var 2)))) 0
  let main := implementation (.mk 0 [
    .letS 0 (.arrLit owner [.lit .i64 7] 0) 0,.letS 1 outer 0,
    .print [.expr (.read (.var 1))] 0] none)
    #[⟨"owner",owner,.mutable,0,0⟩,⟨"outer",view,.immutable,0,0⟩,⟨"inner",view,.immutable,1,0⟩] #[] .unknown
  { (baseModule main) with contexts := #[⟨0,"main",[(1,[.local 0]),(2,[.local 0])],[],[]⟩] }

#guard accepts nestedInitializersShrink

end Goose.Construct.ValidationChecks
