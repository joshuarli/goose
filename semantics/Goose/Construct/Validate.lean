import Goose.Construct.Named
import Goose.Construct.Roots
import Goose.Construct.Layout

namespace Goose.Construct
open Goose.Core (ContextId GlobalId ImplId Mode OriginId Param Request Rule RootRef V VarId reject forAll)

private structure ValidationFacts where
  scopes : List (Nat × Option Nat) := []
  origins : List OriginId := []
  missingPushOrigin : Bool := false

private def ValidationFacts.join (left right : ValidationFacts) : ValidationFacts :=
  { scopes := left.scopes ++ right.scopes, origins := left.origins ++ right.origins,
    missingPushOrigin := left.missingPushOrigin || right.missingPushOrigin }

private def joinFacts (facts : List ValidationFacts) : ValidationFacts :=
  facts.foldl ValidationFacts.join {}

mutual
private def exprFacts (parent : Option Nat) : Expr → ValidationFacts
  | .lit .. | .bool _ => {}
  | .resultLocal _ org => { origins := [org] }
  | .read place | .ref _ place => placeFacts parent place
  | .slice _ view low high org =>
      let children := (viewFacts parent view).join ((boundFacts parent low).join (boundFacts parent high))
      { children with origins := org :: children.origins }
  | .len view => viewFacts parent view
  | .un _ expression org | .conv _ _ expression org =>
      let child := exprFacts parent expression
      { child with origins := org :: child.origins }
  | .copy _ place org =>
      let child := placeFacts parent place
      { child with origins := org :: child.origins }
  | .bin _ left right org =>
      let children := (exprFacts parent left).join (exprFacts parent right)
      { children with origins := org :: children.origins }
  | .cmp _ left right | .and left right | .or left right =>
      (exprFacts parent left).join (exprFacts parent right)
  | .not expression => exprFacts parent expression
  | .call _ arguments org =>
      let children := argsFacts parent arguments
      { children with origins := org :: children.origins }
  | .push owner expression org =>
      let children := (placeFacts parent owner).join (exprFacts parent expression)
      { scopes := children.scopes
        origins := org.toList ++ children.origins
        missingPushOrigin := children.missingPushOrigin || org.isNone }
  | .pop owner org =>
      let children := placeFacts parent owner
      { children with origins := org :: children.origins }
  | .ifE condition left right org =>
      let children := (exprFacts parent condition).join ((blockFacts parent left).join (blockFacts parent right))
      { children with origins := org :: children.origins }
  | .blockE block org =>
      let children := blockFacts parent block
      { children with origins := org :: children.origins }
  | .arrLit _ elements org =>
      let children := joinFacts (elements.map (exprFacts parent))
      { children with origins := org :: children.origins }
  | .structLit _ elements | .values elements =>
      joinFacts (elements.map (exprFacts parent))
  | .fill _ expression org =>
      let children := exprFacts parent expression
      { children with origins := org :: children.origins }
  | .bytes _ _ org => { origins := [org] }
  | .str _ arguments org =>
      let children := printFacts parent arguments
      { children with origins := org :: children.origins }

private def placeFacts (parent : Option Nat) : Place → ValidationFacts
  | .var _ | .global _ => {}
  | .deref expression => exprFacts parent expression
  | .elem view index org =>
      let children := (viewFacts parent view).join (exprFacts parent index)
      { children with origins := org :: children.origins }
  | .field owner _ => placeFacts parent owner

private def viewFacts (parent : Option Nat) : View → ValidationFacts
  | .of place => placeFacts parent place
  | .val expression => exprFacts parent expression

private def boundFacts (parent : Option Nat) : Bound → ValidationFacts
  | .omitted => {}
  | .expr expression | .fromEnd expression => exprFacts parent expression

private def argsFacts (parent : Option Nat) : List Arg → ValidationFacts
  | [] => {}
  | .byVal expression :: rest | .construct expression :: rest =>
      (exprFacts parent expression).join (argsFacts parent rest)
  | .byRef _ place :: rest => (placeFacts parent place).join (argsFacts parent rest)

private def printFacts (parent : Option Nat) : List PrintArg → ValidationFacts
  | [] => {}
  | .text _ :: rest => printFacts parent rest
  | .expr expression :: rest => (exprFacts parent expression).join (printFacts parent rest)
  | .view view :: rest => (viewFacts parent view).join (printFacts parent rest)

private def blockFacts (parent : Option Nat) : Block → ValidationFacts
  | .mk scope statements tail =>
      { (joinFacts [stmtFacts (some scope) statements,
          match tail with | none => {} | some expression => exprFacts (some scope) expression]) with
        scopes := (scope, parent) :: (stmtFacts (some scope) statements).scopes ++
          (match tail with | none => [] | some expression => (exprFacts (some scope) expression).scopes) }

private def stmtFacts (parent : Option Nat) : List Stmt → ValidationFacts
  | [] => {}
  | statement :: rest => (stmtFact parent statement).join (stmtFacts parent rest)

private def stmtFact (parent : Option Nat) : Stmt → ValidationFacts
  | .letS _ expression org | .rebind _ expression org | .expr expression org |
      .assertS expression org | .exit expression org | .receive _ expression org |
      .retForward expression org | .breakValue expression org |
      .returnFromForward _ expression org =>
      let child := exprFacts parent expression
      { child with origins := org :: child.origins }
  | .assign owner expression org | .assignOp _ owner expression org |
      .assignWhole owner expression org | .appendValue owner expression org |
      .appendConstruct owner expression org =>
      let children := (placeFacts parent owner).join (exprFacts parent expression)
      { children with origins := org :: children.origins }
  | .append owner view org =>
      let children := (placeFacts parent owner).join (viewFacts parent view)
      { children with origins := org :: children.origins }
  | .popN owner count org =>
      let children := (placeFacts parent owner).join (exprFacts parent count)
      { children with origins := org :: children.origins }
  | .resize owner count fill org =>
      let children := (placeFacts parent owner).join ((exprFacts parent count).join
        (match fill with | none => {} | some expression => exprFacts parent expression))
      { children with origins := org :: children.origins }
  | .clear owner org =>
      let children := placeFacts parent owner
      { children with origins := org :: children.origins }
  | .ifS condition left right org =>
      let children := (exprFacts parent condition).join ((blockFacts parent left).join
        (match right with | none => {} | some block => blockFacts parent block))
      { children with origins := org :: children.origins }
  | .while condition body org =>
      let children := (exprFacts parent condition).join (blockFacts parent body)
      { children with origins := org :: children.origins }
  | .forRange _ low high body org =>
      let children := (exprFacts parent low).join ((exprFacts parent high).join (blockFacts parent body))
      { children with origins := org :: children.origins }
  | .forEach _ _ view _ body org =>
      let children := (viewFacts parent view).join (blockFacts parent body)
      { children with origins := org :: children.origins }
  | .retValues operands org | .returnFrom _ operands org =>
      let children := joinFacts (operands.map (exprFacts parent))
      { children with origins := org :: children.origins }
  | .ret value org =>
      let children := match value with
        | none => ({} : ValidationFacts)
        | some expression => exprFacts parent expression
      { children with origins := org :: children.origins }
  | .brk org | .cont org | .abort _ org => { origins := [org] }
  | .print arguments org =>
      let children := printFacts parent arguments
      { children with origins := org :: children.origins }
end

private def scopeOrderError : List (Nat × Option Nat) → Nat → Option String
  | [], _ => none
  | (scope, parent) :: rest, expected =>
      if scope != expected then some s!"block scope {scope} is not the next scope {expected}"
      else if let some parent := parent then
        if parent < scope then scopeOrderError rest (expected + 1)
        else some s!"block scope {scope} has a parent that is not earlier"
      else scopeOrderError rest (expected + 1)

private def originInTable (module : Module) (origin : OriginId) : Bool := origin < module.origins.size

private def checkOrigins (module : Module) (facts : ValidationFacts) : V Unit := do
  if facts.missingPushOrigin then reject .type "push is missing its required origin"
  for origin in facts.origins do
    unless originInTable module origin do
      reject .type s!"origin {origin} is outside the origin table"

private def checkOriginTable (module : Module) : V Unit :=
  for origin in module.origins do
    unless origin.file < module.files.size && origin.line > 0 && Goose.Core.originKinds.contains origin.kind do
      reject .type "origin table entry is invalid"

private def targetKey : Target → Nat × Nat
  | .param i => (0, i)
  | .global g => (1, g)

private def lessTarget (left right : Target) : Bool :=
  let (leftKind, leftIndex) := targetKey left
  let (rightKind, rightIndex) := targetKey right
  leftKind < rightKind || (leftKind == rightKind && leftIndex < rightIndex)

private def sortedTargets : List Target → Bool
  | first :: second :: rest => lessTarget first second && sortedTargets (second :: rest)
  | _ => true

private def sortedNats : List Nat → Bool
  | first :: second :: rest => first < second && sortedNats (second :: rest)
  | _ => true

private def checkContextTables (context : Context) : V Unit := do
  unless sortedNats (context.varRoots.map Prod.fst) do
    reject .root "context root annotations are unsorted or repeated"
  unless sortedNats (context.contentRoots.map Prod.fst) do
    reject .root "context content roots are unsorted or repeated"

private def checkSummaryShape (implementation : Impl) : V Unit := do
  match implementation.summary with
  | .unknown => pure ()
  | .known summary =>
      unless [summary.reads, summary.writes, summary.grows, summary.shrinks, summary.rebinds].all sortedTargets &&
          sortedNats summary.constructs && sortedNats summary.needs && sortedNats summary.escapes do
        reject .summary s!"{implementation.name}: summary lists are unsorted or repeated"

private def checkModuleType (module : Module) (ty : Ty) : V Unit := do
  if ty.isRefSlice && module.impls.any fun implementation =>
      implementation.params.any fun parameter =>
        parameter.mode == .byRef && (implementation.vars[parameter.var]?).any (·.ty == ty) then
    match ty with
    | .ref _ target => checkType module target
    | _ => checkType module ty
  else checkType module ty

private def checkStructTables (module : Module) : V Unit := do
  let layout := LayoutEnv.ofModule module
  for h : structId in [0:module.structs.size] do
    let definition := module.structs[structId]
    if definition.displayName.isEmpty then reject .type "struct display name must be nonempty"
    unless definition.byteSize > 0 do reject .type "struct byte size must be positive"
    let mut endOffset := 0
    for field in definition.fields do
      checkType module field.ty
      unless field.ty.flat do reject .type "struct fields must be flat fixed values"
      let some byteSize := fixedByteSize? layout field.ty | reject .type "struct field has no fixed byte size"
      unless byteSize > 0 && field.byteOffset >= endOffset do
        reject .type "struct fields overlap or are out of order"
      let fieldEnd := field.byteOffset + byteSize
      unless fieldEnd <= definition.byteSize do reject .type "struct field extends beyond its byte size"
      endOffset := fieldEnd
  for ty in module.types do checkModuleType module ty

private def checkParameter (module : Module) (implementation : Impl) (position : Nat) : V Unit := do
  let some parameter := implementation.params[position]? | pure ()
  unless parameter.var == position do
    reject .type s!"parameter {position} names variable {parameter.var}"
  let some localVar := implementation.vars[position]? | reject .type s!"parameter {position} has no variable row"
  unless localVar.scope == 0 do reject .type s!"parameter {position} is not declared in the body block"
  match parameter.mode, localVar.ty with
  | .byRef, .ref _ (.slice _ _) =>
      checkType module (match localVar.ty with | .ref _ target => target | _ => .unit)
  | .byRef, .ref _ target =>
      unless target.storageType do reject .type s!"parameter {position} refers to a type with no storage"
      checkType module target
  | .byRef, _ => reject .type s!"by-reference parameter {position} is not of reference type"
  | .byValue, .ref _ _ => reject .type s!"by-value parameter {position} is of reference type"
  | .byValue, ty =>
      checkType module ty
      unless ty.storable do reject .type s!"parameter {position} has a type no variable may have"

private def arrayResult (ty : Ty) : Bool :=
  match ty with
  | .arr .. | .varr .. | .grow .. | .growshrink .. | .limited .. => true
  | _ => false

private def checkResultDescriptor (module : Module) (implementation : Impl)
    (descriptor : ResultDescriptor) : V Unit := do
  checkModuleType module descriptor.ty
  unless descriptor.ty.storable && descriptor.ty != .unit do
    reject .type s!"{implementation.name} has a result of a type no function may return"
  if descriptor.ty.nonfixed then
    unless descriptor.request == .value || descriptor.request == .elementRun do
      reject .result s!"{implementation.name} has a nonfixed result with a register request"
    if descriptor.request == .elementRun && !arrayResult descriptor.ty then
      reject .result s!"{implementation.name} requests an element run for a non-array result"
  else
    unless descriptor.request == .register do
      reject .result s!"{implementation.name} has a fixed result without a register request"
  if descriptor.namedLocal.isSome && (!descriptor.ty.nonfixed || descriptor.request != .value) then
    reject .result s!"{implementation.name} names a local for an ineligible result"

private def checkResultValues (implementation : Impl) (actual : List Ty) : V Unit := do
  unless actual.length == implementation.results.size do
    reject .result s!"{implementation.name}: body result count mismatch"
  for (source, target) in actual.zip implementation.results.toList do
    unless source.passesTo target.ty do
      reject .result s!"{implementation.name}: body value has another type than its result"

mutual
private def hasBreak (block : Block) : Bool :=
  match block with
  | .mk _ statements _ => statementsHaveBreak statements
termination_by sizeOf block

private def stmtHasBreak (statement : Stmt) : Bool :=
  match statement with
  | .brk _ | .breakValue .. => true
  | .ifS _ left none _ => hasBreak left
  | .ifS _ left (some right) _ => hasBreak left || hasBreak right
  | .while _ body _ | .forRange _ _ _ body _ | .forEach _ _ _ _ body _ => hasBreak body
  | _ => false
termination_by sizeOf statement

private def statementsHaveBreak (statements : List Stmt) : Bool :=
  match statements with
  | [] => false
  | statement :: rest => stmtHasBreak statement || statementsHaveBreak rest
termination_by sizeOf statements
end

mutual
private def stmtNeverCompletes (module : Module) (implementation : ImplId)
    (neverReturns : ContextId → Bool) : Stmt → Bool
  | .ret .. | .retValues .. | .retForward .. | .returnFrom .. | .returnFromForward .. |
      .abort .. | .exit .. => true
  | .expr (.call context _ _) _ => neverReturns context
  | .ifS _ left (some right) _ => blockNeverCompletes module implementation neverReturns left &&
      blockNeverCompletes module implementation neverReturns right
  | .while (.bool true) body _ => !hasBreak body
  | _ => false

private def blockNeverCompletes (module : Module) (implementation : ImplId)
    (neverReturns : ContextId → Bool) : Block → Bool
  | .mk _ statements _ => statementsNeverComplete module implementation neverReturns statements

private def statementsNeverComplete (module : Module) (implementation : ImplId)
    (neverReturns : ContextId → Bool) : List Stmt → Bool
  | [] => false
  | statement :: rest => stmtNeverCompletes module implementation neverReturns statement ||
      statementsNeverComplete module implementation neverReturns rest

private def stmtNeverReturns (module : Module) (implementation : ImplId)
    (neverReturns : ContextId → Bool) : Stmt → Bool
  | .abort .. | .exit .. => true
  | .expr (.call context _ _) _ => neverReturns context
  | .retForward (.call context _ _) _ => neverReturns context
  | .returnFrom target _ _ => (module.targets[target]?).any fun members => !members.contains implementation
  | .returnFromForward target (.call context _ _) _ =>
      (module.targets[target]?).any fun members => !members.contains implementation || neverReturns context
  | .ifS _ left (some right) _ => blockNeverReturns module implementation neverReturns left &&
      blockNeverReturns module implementation neverReturns right
  | _ => false

private def blockNeverReturns (module : Module) (implementation : ImplId)
    (neverReturns : ContextId → Bool) : Block → Bool
  | .mk _ statements _ => stmtsNeverReturns module implementation neverReturns statements

private def stmtPlain : Stmt → Bool
  | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append .. | .popN .. |
      .resize .. | .clear .. | .assignWhole .. | .appendValue .. | .appendConstruct .. |
      .print .. | .assertS .. => true
  | _ => false

private def stmtsNeverReturns (module : Module) (implementation : ImplId)
    (neverReturns : ContextId → Bool) : List Stmt → Bool
  | [] => false
  | statement :: rest => stmtNeverReturns module implementation neverReturns statement ||
      (stmtPlain statement && stmtsNeverReturns module implementation neverReturns rest)
end

private def neverReturnsAt (module : Module) : Nat → ContextId → Bool
  | 0, _ => false
  | rounds + 1, context =>
      match module.contexts[context]? with
      | none => false
      | some contextInfo =>
          match module.impls[contextInfo.impl]? with
          | none => false
          | some implementation => blockNeverReturns module contextInfo.impl (neverReturnsAt module rounds)
              implementation.body

private def checkImplementation (module : Module) (implementationId : ImplId) (implementation : Impl) : V Unit := do
  for position in List.range implementation.params.size do
    checkParameter module implementation position
  for h : localId in [0:implementation.vars.size] do
    let localVar := implementation.vars[localId]
    unless localVar.org < module.origins.size do
      reject .type s!"{implementation.name}: origin of variable {localVar.name} is outside the origin table"
    let isSliceReferenceParameter := (implementation.params[localId]?).any fun parameter =>
      parameter.var == localId && parameter.mode == .byRef && localVar.ty.isRefSlice
    unless isSliceReferenceParameter do
      checkModuleType module localVar.ty
      unless localVar.ty.storable do reject .type s!"{implementation.name}: local {localVar.name} has no storage type"
  for descriptor in implementation.results do checkResultDescriptor module implementation descriptor
  let facts := blockFacts none implementation.body
  unless implementation.body.scope == 0 do
    reject .type s!"{implementation.name}: the body block is not scope 0"
  if let some message := scopeOrderError facts.scopes 0 then
    reject .type s!"{implementation.name}: {message}"
  for localVar in implementation.vars do
    unless localVar.scope < facts.scopes.length do
      reject .type s!"{implementation.name}: scope of variable {localVar.name} is outside the body scope table"
  checkOrigins module facts
  let fuel := 4096
  let env : TypingEnv := {
    module := module
    implementation := some implementation
    variables := implementation.vars
    visible := List.range implementation.params.size
    scope := implementation.body.scope
    loops := 0
    use := if implementation.results.isEmpty then .ordinary else .result
    request := .value
    resultRequests := implementation.results.toList.map (·.request)
    globalLimit := module.globals.size }
  let (bodyTypes, declared) ← (typeBlock fuel env implementation.body).run implementation.params.size
  unless declared == implementation.vars.size do
    reject .type s!"{implementation.name}: local variable table has an undeclared row"
  if implementation.results.isEmpty then
    unless bodyTypes == [.unit] do reject .type s!"{implementation.name} has no result but its body yields a value"
  else if implementation.body.value.isSome then
    checkResultValues implementation bodyTypes
  else
    unless blockNeverCompletes module implementationId (neverReturnsAt module module.contexts.size)
        implementation.body do
      reject .type s!"{implementation.name} can fall off its end without returning a value"
  checkSummaryShape implementation

private def checkGlobal (module : Module) (globalId : GlobalId) (global : Global) : V Unit := do
  checkModuleType module global.ty
  unless global.ty.storageType && global.ty != .unit do
    reject .type s!"global {global.name} has a type no variable may have"
  unless global.org < module.origins.size do
    reject .type s!"global {global.name}: origin outside the origin table"
  let facts := exprFacts none global.init
  if let some message := scopeOrderError facts.scopes 0 then
    reject .type s!"global {global.name}: {message}"
  checkOrigins module facts
  let env : TypingEnv := {
    module := module
    implementation := none
    variables := #[]
    visible := []
    scope := 0
    loops := 0
    globalLimit := globalId }
  let (types, _) ← (typeExpr 4096 env global.init).run 0
  match types with
  | [ty] => unless ty.adaptsTo global.ty do reject .type s!"initializer of global {global.name} has another type than the global"
  | _ => reject .type s!"initializer of global {global.name} must produce one value"

private def checkEntry (module : Module) : V Unit := do
  let some context := module.contexts[module.entry]? | reject .type "entry context is outside the context table"
  let some implementation := module.impls[context.impl]? | reject .type "entry context names a missing implementation"
  unless implementation.params.isEmpty && implementation.results.isEmpty do
    reject .type s!"the entry {implementation.name} must take no parameters and return nothing"

private def checkImplementationContexts (module : Module) : V Unit :=
  for implementation in List.range module.impls.size do
    unless module.contexts.toList.any (fun context => context.impl == implementation) do
      reject .root s!"implementation {implementation} has no context"

private def checkTargetTables (module : Module) : V Unit := do
  for target in module.targets do
    let members := target.members
    unless sortedNats members && members.all (· < module.impls.size) do
      reject .call "nonlocal target members are outside the implementation table or unsorted"

private def checkTargetAvailabilityV (module : Module) : V Unit :=
  match checkTargetAvailability module with
  | .ok _ => pure ()
  | .error message =>
      let rule := if message.startsWith "V-RESULT:" then .result
        else if message.startsWith "V-SUMMARY:" then .summary
        else .call
      reject rule message

private def checkNamedResultsV (module : Module) : V Unit :=
  match checkNamedResults module with
  | .ok _ => pure ()
  | .error message => reject .result message

def validate (module : Module) : V Unit := do
  checkOriginTable module
  checkStructTables module
  for global in module.globals do checkModuleType module global.ty
  for implementation in module.impls do
    for localVar in implementation.vars do checkModuleType module localVar.ty
    for result in implementation.results do checkModuleType module result.ty
  for context in module.contexts do checkContextTables context
  checkEntry module
  checkImplementationContexts module
  checkTargetTables module
  for implementation in List.range module.impls.size do
    match module.impls[implementation]? with
    | some function => checkImplementation module implementation function
    | none => reject .type s!"implementation {implementation} is outside the implementation table"
  for global in List.range module.globals.size do
    match module.globals[global]? with
    | some value => checkGlobal module global value
    | none => reject .type s!"global {global} is outside the global table"
  checkTargetAvailabilityV module
  checkNamedResultsV module
  for context in module.contexts do checkContext module context
  for global in List.range module.globals.size do checkInitRoots module global
  checkModuleExitRoots module

end Goose.Construct
