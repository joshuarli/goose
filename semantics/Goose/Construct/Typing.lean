import Goose.Construct.Syntax
import Goose.Core.Typing

namespace Goose.Construct
open Goose.Core (Request V Rule Rejection reject forAll Mutability VarKind Mode Param VarId OriginId)

mutual
def checkType (module : Module) : Ty → V Unit
  | .int _ | .bool | .unit => pure ()
  | .varr element | .grow element => do
      if !(element.flat || element.variableElement) then reject .type "invalid localVar-array element"
      checkType module element
  | .arr element count => do
      if count == 0 || !(element.flat || element.variableElement) then reject .type "invalid fixed-array element or count"
      checkType module element
  | .growshrink element => do
      if !element.flat then reject .type "growshrink requires flat fixed elements"
      checkType module element
  | .limited element capacity => do
      if capacity == 0 || !element.flat then reject .type "limited requires positive capacity and flat fixed elements"
      checkType module element
  | .ref _ target => do
      if !target.storageType then reject .type "reference target is not storage"
      checkType module target
  | .slice _ element => do
      if !(element.flat || element.variableElement) then reject .type "slice element is not supported"
      checkType module element
  | .structT id fields => do
      if module.structType? id != some (.structT id fields) || !fields.flat then
        reject .type "struct fields or nominal descriptor mismatch"
      checkTypes module fields
  | .tuple fields => checkTypes module fields

def checkTypes (module : Module) : TyList → V Unit
  | .nil => pure ()
  | .cons ty rest => do checkType module ty; checkTypes module rest

def Ty.storageType : Ty → Bool
  | .int _ | .bool => true
  | .arr element _ | .varr element | .grow element => element.flat || element.variableElement
  | .growshrink element | .limited element _ => element.flat
  | .structT _ fields => fields.flat
  | _ => false
end

def Ty.storable (ty : Ty) : Bool :=
  match ty with
  | .ref _ target => target.storageType
  | .slice _ element => element.flat || element.variableElement
  | _ => ty.storageType

def Ty.element? : Ty → Option Ty
  | .arr element _ | .varr element | .grow element | .growshrink element |
      .limited element _ | .slice _ element => some element
  | _ => none

def Ty.growing : Ty → Bool
  | .grow _ | .growshrink _ | .limited _ _ => true
  | _ => false

def Ty.adaptsTo (source target : Ty) : Bool :=
  source == target || match source, target with
    | .arr a countA, .arr b countB => a == b && countA == countB
    | _, _ => match source.element?, target.element? with
      | some a, some b => a == b && source.storageType && target.storageType
      | _, _ => false

def Ty.passesTo (source target : Ty) : Bool :=
  match source, target with
  | .ref sourceMut a, .ref targetMut b | .slice sourceMut a, .slice targetMut b =>
      a == b && (sourceMut == .mutable || targetMut == .readOnly)
  | _, _ => source.adaptsTo target

inductive ExpressionUse
  | ordinary
  | result
  deriving DecidableEq

structure TypingEnv where
  module : Module
  implementation : Option Impl
  variables : Array LocalVar
  visible : List VarId
  scope : Nat
  loops : Nat
  use : ExpressionUse := .ordinary
  request : Request := .value
  resultRequests : List Request := []
  globalLimit : Nat

abbrev TypingM := StateT Nat V

private def fail (rule : Rule) (message : String) : TypingM α := throw ⟨rule, message⟩

private def ordinary (env : TypingEnv) : TypingEnv := { env with use := .ordinary, request := .value, resultRequests := [] }

private def lookupVariable (env : TypingEnv) (id : VarId) : TypingM LocalVar := do
  if !env.visible.contains id then fail .type "localVar is not visible"
  let some localVar := env.variables[id]? | fail .type "localVar outside table"
  pure localVar

private def declare (env : TypingEnv) (id : VarId) : TypingM LocalVar := do
  let expected ← get
  if id != expected then fail .type "variables must be declared once in ascending order"
  let some localVar := env.variables[id]? | fail .type "declared localVar outside table"
  if localVar.scope != env.scope || !localVar.ty.storable then fail .type "localVar scope or type mismatch"
  set (expected + 1)
  pure localVar

private def require (condition : Bool) (rule : Rule) (message : String) : TypingM Unit :=
  if condition then pure () else fail rule message

private def one (types : List Ty) : TypingM Ty :=
  match types with
  | [ty] => pure ty
  | _ => fail .type "single-result expression required"

private def resultTypes (env : TypingEnv) : TypingM (List ResultDescriptor) := do
  let some implementation := env.implementation | fail .result "return outside implementation"
  pure implementation.results.toList

private def targetResults (env : TypingEnv) (id : Nat) : TypingM (List ResultDescriptor) := do
  let some target := env.module.targets[id]? | fail .call "target outside table"
  let some implementation := env.module.impls[target.first]? | fail .call "target member outside table"
  pure implementation.results.toList

private def expectBool (ty : Ty) : TypingM Unit := require (ty == .bool) .type "boolean required"

private def expectInt (ty : Ty) : TypingM Unit :=
  match ty with | .int _ => pure () | _ => fail .type "integer required"

private def canRender (ty : Ty) : Bool := ty.storable

mutual
def typePlace : Nat → TypingEnv → Place → TypingM (Ty × Bool × Bool)
  | 0, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, env, .var id => do
      let localVar ← lookupVariable env id
      pure (localVar.ty, localVar.kind == .mutable, true)
  | _fuel + 1, env, .global id => do
      if id ≥ env.globalLimit then fail .root "global is not initialized at this point"
      let some global := env.module.globals[id]? | fail .type "global outside table"
      pure (global.ty, global.kind == .mutable, true)
  | fuel + 1, env, .deref expression => do
      let ty ← match expression with
        | .read (.var id) => do
            let localVar ← lookupVariable env id
            match localVar.ty with
            | .ref _ (.slice ..) => pure localVar.ty
            | _ => one (← typeExpr fuel (ordinary env) expression)
        | _ => one (← typeExpr fuel (ordinary env) expression)
      match ty with
      | .ref mutability target => pure (target, mutability == .mutable, mutability == .mutable)
      | _ => fail .type "dereference requires reference"
  | fuel + 1, env, .elem view index _ => do
      let (element, writable) ← typeView fuel env view
      expectInt (← one (← typeExpr fuel (ordinary env) index))
      pure (element, writable, writable)
  | fuel + 1, env, .field owner index => do
      let (ty, _, writable) ← typePlace fuel env owner
      match ty with
      | .structT id _ =>
          let some definition := env.module.structs[id]? | fail .type "struct outside table"
          let some field := definition.fields[index]? | fail .type "field outside struct"
          pure (field.ty, writable && field.binding == .mutable, writable && field.contents == .mutable)
      | _ => fail .type "field requires struct"

def typeView : Nat → TypingEnv → View → TypingM (Ty × Bool)
  | 0, _, _ => fail .type "validation nesting limit"
  | fuel + 1, env, .of place => do
      let (ty, _, writable) ← typePlace fuel env place
      match ty.element? with
      | some element => pure (element, writable)
      | none => fail .type "view requires array storage"
  | fuel + 1, env, .val expression => do
      match (← one (← typeExpr fuel (ordinary env) expression)) with
      | .slice mutability element => pure (element, mutability == .mutable)
      | _ => fail .type "view value requires slice"

def typeBound : Nat → TypingEnv → Bound → TypingM Unit
  | 0, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, .omitted => pure ()
  | fuel + 1, env, .expr expression | fuel + 1, env, .fromEnd expression => do expectInt (← one (← typeExpr fuel (ordinary env) expression))

def typeExpr : Nat → TypingEnv → Expr → TypingM (List Ty)
  | 0, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, .lit ty _ => pure [.int ty]
  | _fuel + 1, _env, .bool _ => pure [.bool]
  | fuel + 1, env, .read place => do
      let (ty, _, _) ← typePlace fuel env place
      require (ty.storable && !ty.nonfixed) .type "read requires an ordinary storable value"
      pure [ty]
  | fuel + 1, env, .ref mutability place => do
      let (ty, writable, _) ← typePlace fuel env place
      require ty.storageType .type "reference target is not storage"
      require (mutability == .readOnly || writable) .mut "mutable reference to read-only place"
      pure [.ref mutability ty]
  | fuel + 1, env, .slice mutability view low high _ => do
      let (element, writable) ← typeView fuel env view
      typeBound fuel env low
      typeBound fuel env high
      require (mutability == .readOnly || writable) .mut "mutable slice of read-only view"
      pure [.slice mutability element]
  | fuel + 1, env, .len view => do let _ ← typeView fuel env view; pure [.int .i64]
  | fuel + 1, env, .un op expression _ => do
      let ty ← one (← typeExpr fuel (ordinary env) expression)
      expectInt ty
      match op, ty with
      | .neg, .int integer => require integer.signed .type "unsigned integer negation is not allowed"
      | _, _ => pure ()
      pure [ty]
  | fuel + 1, env, .bin _ left right _ => do
      let a ← one (← typeExpr fuel (ordinary env) left)
      let b ← one (← typeExpr fuel (ordinary env) right)
      expectInt a
      require (a == b) .type "binary operand type mismatch"
      pure [a]
  | fuel + 1, env, .cmp op left right => do
      let a ← one (← typeExpr fuel (ordinary env) left)
      let b ← one (← typeExpr fuel (ordinary env) right)
      match a, b with
      | .int _, .int _ => require (a == b) .type "comparison operand type mismatch"
      | .bool, .bool => match op with
        | .eq | .ne => pure ()
        | _ => fail .type "booleans support equality comparison only"
      | _, _ => fail .type "unsupported comparison operands"
      pure [.bool]
  | fuel + 1, env, .and left right | fuel + 1, env, .or left right => do
      expectBool (← one (← typeExpr fuel (ordinary env) left))
      expectBool (← one (← typeExpr fuel (ordinary env) right))
      pure [.bool]
  | fuel + 1, env, .not expression => do expectBool (← one (← typeExpr fuel (ordinary env) expression)); pure [.bool]
  | fuel + 1, env, .conv kind target expression _ => do
      let source ← one (← typeExpr fuel (ordinary env) expression)
      expectInt target
      expectInt source
      match kind with
      | .widen => match source, target with
        | .int fromType, .int toType =>
            require (decide (toType.minVal ≤ fromType.minVal ∧ fromType.maxVal ≤ toType.maxVal))
              .type "widening conversion does not preserve the source range"
        | _, _ => fail .type "widening requires integer types"
      | .as | .asUnchecked => pure ()
      pure [target]
  | fuel + 1, env, .call contextId arguments _ => do
      let some context := env.module.contexts[contextId]? | fail .call "call context outside table"
      let some callee := env.module.impls[context.impl]? | fail .call "callee outside table"
      typeArguments fuel env callee callee.params.toList arguments
      if callee.results.size > 1 && env.use != .result then fail .type "multiple call results require result channels"
      if !env.resultRequests.isEmpty then
        require (env.resultRequests.length == callee.results.size) .result "result request channel count mismatch"
      for h : position in [0:callee.results.size] do
        let descriptor := callee.results[position]
        let request ← if env.resultRequests.isEmpty then pure env.request else do
          let some request := env.resultRequests[position]? | fail .result "result request channel missing"
          pure request
        if descriptor.ty.nonfixed then
          require (descriptor.request == request) .call "constructor request does not match destination"
      pure (if callee.results.isEmpty then [.unit] else callee.results.toList.map (·.ty))
  | fuel + 1, env, .push owner expression _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      require (ty.growing && (writable)) .mut "push requires writable growing array"
      let some element := ty.element? | fail .type "push array element missing"
      require ((← one (← typeExpr fuel (ordinary env) expression)).adaptsTo element) .type "pushed element type mismatch"
      pure [.ref .mutable element]
  | fuel + 1, env, .pop owner _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      require (writable && match ty with | .growshrink _ | .limited _ _ => true | _ => false)
        .mut "pop requires writable shrinkable array"
      let some element := ty.element? | fail .type "pop array element missing"
      pure [element]
  | fuel + 1, env, .ifE condition left right => do
      expectBool (← one (← typeExpr fuel (ordinary env) condition))
      let a ← typeBlock fuel env left
      let b ← typeBlock fuel env right
      require (a == b) .type "branch result type mismatch"
      pure a
  | fuel + 1, env, .blockE block => typeBlock fuel env block
  | fuel + 1, env, .arrLit ty elements => do
      require ty.constructible .type "array literal type is not constructible"
      let some element := ty.element? | fail .type "array literal requires array type"
      match ty with
      | .arr _ count => require (count == elements.length) .type "fixed array initializer count mismatch"
      | _ => pure ()
      for expression in elements do
        require ((← one (← typeExpr fuel (ordinary env) expression)).adaptsTo element) .type "array initializer type mismatch"
      pure [ty]
  | fuel + 1, env, .fill ty expression => do
      match ty with
      | .arr element _ =>
          require ((← one (← typeExpr fuel (ordinary env) expression)).adaptsTo element) .type "fill element type mismatch"
          pure [ty]
      | _ => fail .type "fill requires fixed-count array"
  | fuel + 1, env, .structLit ty fields => do
      match ty with
      | .structT id types =>
          require ((env.module.structType? id) == some ty && types.flat) .type "invalid nominal struct"
          typeFields fuel env types.toList fields
          pure [ty]
      | _ => fail .type "struct initializer requires struct type"
  | _fuel + 1, _env, .bytes ty data _ => do
      match ty with
      | .slice .readOnly (.int .u8) => pure [ty]
      | .arr (.int .u8) count => require (count == data.length) .type "literal byte count mismatch"; pure [ty]
      | .varr (.int .u8) | .grow (.int .u8) | .growshrink (.int .u8) | .limited (.int .u8) _ => pure [ty]
      | _ => fail .type "literal bytes require u8 array or immutable slice"
  | fuel + 1, env, .str ty arguments _ => do
      require (ty.storageType && ty.element? == some (.int .u8)) .type "constructed text requires u8 array"
      typePrint fuel env arguments
      pure [ty]
  | fuel + 1, env, .copy ty source _ => do
      let (sourceTy, _, _) ← typePlace fuel env source
      require (sourceTy.adaptsTo ty || (sourceTy.element? == ty.element? && sourceTy.element?.isSome))
        .type "copy source and destination layout mismatch"
      pure [ty]
  | _fuel + 1, env, .resultLocal id _ => do
      require (env.use == .result) .result "returned local outside result position"
      let localVar ← lookupVariable env id
      require localVar.ty.nonfixed .result "returned local is fixed"
      let some implementation := env.implementation | fail .result "returned local outside function"
      require (!(implementation.params.toList.any (fun parameter => parameter.var == id)))
        .result "returned local cannot be parameter storage"
      pure [localVar.ty]
  | fuel + 1, env, .values operands => do
      require (env.use == .result && operands.length ≥ 2) .result "multiple values require result position"
      typeValueOperands fuel env env.resultRequests operands

def typeValueOperands : Nat → TypingEnv → List Request → List Expr → TypingM (List Ty)
  | 0, _, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, [], [] => pure []
  | fuel + 1, env, requests, operand :: operands => do
      let (request, remaining) := match requests with
        | [] => (env.request, [])
        | first :: rest => (first, rest)
      let ty ← one (← typeExpr fuel { env with request := request, resultRequests := [] } operand)
      let rest ← typeValueOperands fuel env remaining operands
      pure (ty :: rest)
  | _fuel + 1, _env, _ :: _, [] => fail .result "result request channel count mismatch"

def typeArguments : Nat → TypingEnv → Impl → List Param → List Arg → TypingM Unit
  | 0, _, _, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, _callee, [], [] => pure ()
  | fuel + 1, env, callee, parameter :: parameters, argument :: arguments => do
      let some localVar := callee.vars[parameter.var]? | fail .call "callee parameter outside localVar table"
      match parameter.mode, argument with
      | .byValue, .byVal expression =>
          require (!localVar.ty.nonfixed) .call "nonfixed parameter requires a_construct"
          require ((← one (← typeExpr fuel (ordinary env) expression)).passesTo localVar.ty) .call "argument type mismatch"
      | .byValue, .construct expression =>
          require localVar.ty.nonfixed .call "a_construct requires nonfixed by-value parameter"
          require ((← one (← typeExpr fuel (ordinary env) expression)).adaptsTo localVar.ty) .call "constructed argument type mismatch"
      | .byRef, .byRef mutability place =>
          let (ty, writable, _) ← typePlace fuel env place
          require (mutability == .readOnly || writable) .mut "mutable argument requires writable storage"
          require ((Ty.ref mutability ty).passesTo localVar.ty) .call "reference argument type mismatch"
      | _, _ => fail .call "argument mode mismatch"
      typeArguments fuel env callee parameters arguments
  | _fuel + 1, _env, _callee, _, _ => fail .call "argument count mismatch"

def typeFields : Nat → TypingEnv → List Ty → List Expr → TypingM Unit
  | 0, _, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, [], [] => pure ()
  | fuel + 1, env, ty :: types, expression :: fields => do
      require ((← one (← typeExpr fuel (ordinary env) expression)) == ty) .type "struct field type mismatch"
      typeFields fuel env types fields
  | _fuel + 1, _env, _, _ => fail .type "struct initializer count mismatch"

def typePrint : Nat → TypingEnv → List PrintArg → TypingM Unit
  | 0, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, [] => pure ()
  | fuel + 1, env, .text _ :: rest => typePrint fuel env rest
  | fuel + 1, env, .expr expression :: rest => do
      let ty ← one (← typeExpr fuel (ordinary env) expression)
      require (canRender ty && !ty.nonfixed) .type "nonfixed print operand requires sampled view"
      typePrint fuel env rest
  | fuel + 1, env, .view view :: rest => do let _ ← typeView fuel env view; typePrint fuel env rest

def typeResults : Nat → TypingEnv → List ResultDescriptor → List Expr → TypingM Unit
  | 0, _, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, _env, [], [] => pure ()
  | fuel + 1, env, descriptor :: descriptors, operand :: operands => do
      let ty ← one (← typeExpr fuel { env with use := .result, request := descriptor.request, resultRequests := [] } operand)
      require (ty.passesTo descriptor.ty) .result "returned operand type mismatch"
      typeResults fuel env descriptors operands
  | _fuel + 1, _env, _, _ => fail .result "result operand count mismatch"

def typeBlock : Nat → TypingEnv → Block → TypingM (List Ty)
  | 0, _, _ => fail .type "validation nesting limit"
  | fuel + 1, env, .mk scope statements tail => do
      let env' ← typeStatements fuel { env with scope := scope } statements
      match tail with
      | none => pure [.unit]
      | some expression => typeExpr fuel env' expression

def typeStatements : Nat → TypingEnv → List Stmt → TypingM TypingEnv
  | 0, _, _ => fail .type "validation nesting limit"
  | _fuel + 1, env, [] => pure env
  | fuel + 1, env, statement :: rest => do
      let next ← typeStatement fuel env statement
      typeStatements fuel next rest

def typeStatement : Nat → TypingEnv → Stmt → TypingM TypingEnv
  | 0, _, _ => fail .type "validation nesting limit"
  | fuel + 1, env, .letS id expression _ => do
      let localVar ← declare env id
      let ty ← one (← typeExpr fuel (ordinary env) expression)
      require (ty.passesTo localVar.ty) .type "initializer type mismatch"
      pure { env with visible := id :: env.visible }
  | fuel + 1, env, .receive ids producer _ => do
      let mut types := []
      for id in ids do
        let localVar ← declare env id
        types := types ++ [localVar.ty]
      require (ids.length ≥ 2 && ids.eraseDups == ids) .type "receive needs distinct receiver variables"
      match producer with
      | .call .. | .values _ => pure ()
      | _ => fail .type "receive requires call or values producer"
      let results ← typeExpr fuel { env with use := .result } producer
      require (results.length == types.length && (results.zip types).all (fun (a,b) => a.passesTo b))
        .result "receive result type mismatch"
      pure { env with visible := ids ++ env.visible }
  | fuel + 1, env, .assign place expression _ => do
      let (ty, writable, _) ← typePlace fuel env place
      let value ← one (← typeExpr fuel (ordinary env) expression)
      require (ty.flat && ty == value && writable) .mut "assignment type or permission mismatch"
      pure env
  | fuel + 1, env, .assignWhole place expression _ => do
      let (ty, _, writable) ← typePlace fuel env place
      let value ← one (← typeExpr fuel (ordinary env) expression)
      require (ty.nonfixed && value.adaptsTo ty &&
        (writable))
        .mut "whole assignment type or permission mismatch"
      pure env
  | fuel + 1, env, .assignOp _ place expression _ => do
      let (ty, writable, _) ← typePlace fuel env place
      expectInt ty
      require (writable && (← one (← typeExpr fuel (ordinary env) expression)) == ty) .mut "compound assignment mismatch"
      pure env
  | fuel + 1, env, .rebind id expression _ => do
      let localVar ← lookupVariable env id
      require (localVar.kind == .mutable) .mut "rebind requires mutable localVar"
      match localVar.ty with
      | .ref .. | .slice .. => pure ()
      | _ => fail .type "rebind requires reference or slice localVar"
      require ((← one (← typeExpr fuel (ordinary env) expression)).passesTo localVar.ty) .type "rebind type mismatch"
      pure env
  | fuel + 1, env, .expr expression _ => do
      let types ← typeExpr fuel (ordinary env) expression
      require (types.all fun ty => !ty.nonfixed) .type "nonfixed expression needs receiving storage"
      pure env
  | fuel + 1, env, .append owner view _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      let (element, _) ← typeView fuel env view
      require (ty.growing && (writable) && ty.element? == some element) .mut "append type or permission mismatch"
      pure env
  | fuel + 1, env, .appendValue owner expression _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      let value ← one (← typeExpr fuel (ordinary env) expression)
      require (match value with | .arr element _ => element.flat | _ => false)
        .type "append_value requires fixed array snapshot"
      require (ty.growing && (writable) &&
        ty.element? == value.element?) .mut "appended fixed producer mismatch"
      pure env
  | fuel + 1, env, .appendConstruct owner expression _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      let value ← one (← typeExpr fuel { (ordinary env) with request := .elementRun } expression)
      require (value.nonfixed && value.element?.isSome) .type "append_construct requires nonfixed array"
      require (ty.growing && (writable) &&
        ty.element? == value.element?) .mut "appended constructing producer mismatch"
      pure env
  | fuel + 1, env, .popN owner count _ | fuel + 1, env, .resize owner count none _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      expectInt (← one (← typeExpr fuel (ordinary env) count))
      require (writable && match ty with | .growshrink _ | .limited _ _ => true | _ => false)
        .mut "shrinking requires writable shrinkable owner"
      pure env
  | fuel + 1, env, .resize owner count (some fill) _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      expectInt (← one (← typeExpr fuel (ordinary env) count))
      require (ty.growing && (writable) && ty.element? == some (← one (← typeExpr fuel (ordinary env) fill)))
        .mut "resize type or permission mismatch"
      pure env
  | fuel + 1, env, .clear owner _ => do
      let (ty, _, writable) ← typePlace fuel env owner
      require (writable && match ty with | .growshrink _ | .limited _ _ => true | _ => false)
        .mut "clear requires writable shrinkable owner"
      pure env
  | fuel + 1, env, .ifS condition left right _ => do
      expectBool (← one (← typeExpr fuel (ordinary env) condition))
      let _ ← typeBlock fuel (ordinary env) left
      if let some block := right then let _ ← typeBlock fuel (ordinary env) block
      pure env
  | fuel + 1, env, .while condition body _ => do
      expectBool (← one (← typeExpr fuel (ordinary env) condition))
      let _ ← typeBlock fuel { (ordinary env) with loops := env.loops + 1 } body
      pure env
  | fuel + 1, env, .forRange id low high body _ => do
      let lo ← one (← typeExpr fuel (ordinary env) low)
      let hi ← one (← typeExpr fuel (ordinary env) high)
      expectInt lo
      require (lo == hi) .type "range bound type mismatch"
      let loopEnv := { (ordinary env) with scope := body.scope, loops := env.loops + 1 }
      let localVar ← declare loopEnv id
      require (localVar.ty == lo) .type "range localVar type mismatch"
      let _ ← typeBlock fuel { loopEnv with visible := id :: loopEnv.visible } body
      pure env
  | fuel + 1, env, .forEach id index view byRef body _ => do
      let (element, writable) ← typeView fuel env view
      require (byRef || !element.nonfixed) .type "localVar-width foreach element requires reference binding"
      let loopEnv := { (ordinary env) with scope := body.scope, loops := env.loops + 1 }
      let localVar ← declare loopEnv id
      require (localVar.ty == if byRef then .ref (if writable then .mutable else .readOnly) element else element)
        .type "foreach localVar type mismatch"
      let mut visible := id :: env.visible
      if let some indexId := index then
        let indexVariable ← declare loopEnv indexId
        require (indexVariable.ty == .int .i64) .type "foreach index type mismatch"
        visible := indexId :: visible
      let _ ← typeBlock fuel { loopEnv with visible := visible } body
      pure env
  | fuel + 1, env, .ret value _ => do
      typeResults fuel env (← resultTypes env) value.toList
      pure env
  | fuel + 1, env, .retValues operands _ => do typeResults fuel env (← resultTypes env) operands; pure env
  | fuel + 1, env, .returnFrom target operands _ => do typeResults fuel env (← targetResults env target) operands; pure env
  | fuel + 1, env, .retForward producer _ => do
      match producer with | .call .. => pure () | _ => fail .result "forwarding return requires call"
      let descriptors ← resultTypes env
      let results ← typeExpr fuel { env with use := .result, resultRequests := descriptors.map (·.request) } producer
      require (results.length == descriptors.length &&
        (results.zip descriptors).all (fun (source,target) => source.passesTo target.ty))
        .result "forwarded result type mismatch"
      pure env
  | fuel + 1, env, .returnFromForward target producer _ => do
      match producer with | .call .. => pure () | _ => fail .result "forwarding return requires call"
      let descriptors ← targetResults env target
      let results ← typeExpr fuel { env with use := .result, resultRequests := descriptors.map (·.request) } producer
      require (results.length == descriptors.length &&
        (results.zip descriptors).all (fun (source,target) => source.passesTo target.ty))
        .result "target-forwarded result type mismatch"
      pure env
  | fuel + 1, env, .breakValue expression _ => do
      require (env.loops > 0) .block "value break outside loop"
      let _ ← typeExpr fuel env expression
      pure env
  | _fuel + 1, env, .brk _ | _fuel + 1, env, .cont _ => do require (env.loops > 0) .block "loop control outside loop"; pure env
  | fuel + 1, env, .print arguments _ => do typePrint fuel env arguments; pure env
  | fuel + 1, env, .assertS expression _ => do expectBool (← one (← typeExpr fuel (ordinary env) expression)); pure env
  | _fuel + 1, env, .abort .. => pure env
  | fuel + 1, env, .exit expression _ => do expectInt (← one (← typeExpr fuel (ordinary env) expression)); pure env
end

end Goose.Construct
