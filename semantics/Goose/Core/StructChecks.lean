import Goose.Core.Run
import Goose.Core.Writer
import Goose.Core.Guarantees

namespace Goose.Core.StructChecks

def localStruct : String := include_str "../../../test/semantics/golden/struct_local.core.json"
def localOutput : String := include_str "../../../test/semantics/golden/struct_local.out"
def localResult : String := "[\"done\",[\"returned\"]," ++ Run.quote localOutput ++ "]"

#guard (Run.validateBytes localStruct.toUTF8).1 = "[\"ok\"]"
#guard (Run.runBytes { profile := .release, fuel := 200 } localStruct.toUTF8).1 =
  localResult
#guard (Run.runBytes { profile := .debug, fuel := 200 } localStruct.toUTF8).1 =
  localResult

def checkChange (change : Module → Module) (expected : String) : Bool :=
  match Decode.decodeBytes localStruct.toUTF8 with
  | .error _ => false
  | .ok m =>
    match validate (change m) with
    | .ok () => expected == "ok"
    | .error r => r.rule.tag == expected

def withBody (m : Module) (stmts : List Stmt) : Module :=
  { m with impls := m.impls.modify 0 fun impl => { impl with body := .mk 0 stmts none } }

def initialization (m : Module) : List Stmt :=
  match m.impls[0]? with
  | some impl => impl.body.stmts.take 1
  | none => []

def writeField (m : Module) (i : Nat) (t : IntTy) : Module :=
  withBody m (initialization m ++ [.assign (.field (.var 0) i) (.lit t 8) 1])

#guard checkChange (fun m => writeField m 2 .i16) "V-MUT"
#guard checkChange (fun m => writeField m 3 .i64) "V-TYPE"
#guard checkChange (fun m => writeField m 1 .i16) "V-TYPE"

#guard checkChange (fun m => { m with structs := m.structs.modify 0 fun d =>
  { d with fields := d.fields.modify 1 fun f => { f with byteOffset := 0 } } }) "V-TYPE"
#guard checkChange (fun m => { m with structs := m.structs.modify 0 fun d =>
  { d with byteSize := 10 } }) "V-TYPE"
#guard checkChange (fun m => { m with profile := .pilot }) "V-TYPE"

#guard match Decode.decodeBytes localStruct.toUTF8 with
  | .error _ => false
  | .ok m =>
    let invalid := { m with structs := m.structs.modify 0 fun d => { d with byteSize := 10 } }
    (stageRejections invalid).any (fun r => r.rule == .type)

def constructorChange (m : Module) (type : Ty) (values : List Expr) : Module :=
  withBody m [.letS 0 (.structLit type values) 0]

#guard checkChange (fun m => match m.structType? 0 with
  | some t => constructorChange m t [.lit .u8 1, .lit .i64 40]
  | none => m) "V-TYPE"
#guard checkChange (fun m => match m.structType? 0 with
  | some t => constructorChange m t [.lit .i64 1, .lit .i64 40, .lit .i16 7]
  | none => m) "V-TYPE"

/-- Equal fields and layouts do not make two declarations the same nominal type. -/
def wrongNominalConstructor (m : Module) : Module :=
  match m.structs[0]? with
  | none => m
  | some d =>
    let other := Ty.structT 1 (TyList.ofList (d.fields.toList.map (·.ty)))
    let m' := { m with structs := m.structs.push d, types := m.types.push other }
    constructorChange m' other [.lit .u8 1, .lit .i64 40, .lit .i16 7]

#guard checkChange wrongNominalConstructor "V-TYPE"

def copied (m : Module) : Module :=
  match m.structType? 0 with
  | none => m
  | some t =>
    let m' := { m with impls := m.impls.modify 0 fun impl =>
      { impl with vars := impl.vars.push ⟨"q", t, .immutable, 0, 0⟩ } }
    withBody m' (initialization m ++ [
      .letS 1 (.read (.var 0)) 0,
      .assignOp .add (.field (.var 0) 1) (.lit .i64 2) 1,
      .print [.expr (.read (.field (.var 1) 1)), .text " ",
        .expr (.read (.field (.var 0) 1)), .text " ",
        .expr (.read (.field (.var 0) 0)), .text " ",
        .expr (.read (.field (.var 1) 2))] 2])

def runChange (change : Module → Module) (profile : NumProfile) (expected : String) : Bool :=
  match Decode.decodeBytes localStruct.toUTF8 with
  | .error _ => false
  | .ok m =>
    let m' := change m
    match validate m' with
    | .error _ => false
    | .ok () => (Run.render m' (eval 200 profile m')).1 == expected

#guard runChange copied .release "[\"done\",[\"returned\"],\"40 42 1 7\\n\"]"
#guard runChange copied .debug "[\"done\",[\"returned\"],\"40 42 1 7\\n\"]"

def initializerOrder (abortMiddle : Bool) (m : Module) : Module :=
  match m.structType? 0 with
  | none => m
  | some t =>
    let first := Expr.blockE (.mk 1 [.print [.text "first"] 2] (some (.lit .u8 1)))
    let second := Expr.blockE (.mk 2
      (if abortMiddle then [.abort "stop" 2] else [.print [.text "second"] 2])
      (some (.lit .i64 40)))
    let third := Expr.blockE (.mk 3 [.print [.text "third"] 2] (some (.lit .i16 7)))
    constructorChange m t [first, second, third]

#guard runChange (initializerOrder false) .release
  "[\"done\",[\"returned\"],\"first\\nsecond\\nthird\\n\"]"
#guard runChange (initializerOrder true) .release
  "[\"done\",[\"aborted\",\"user_abort\",6],\"first\\n\"]"

def roundtrip (bytes : ByteArray) : Bool :=
  match Decode.decodeBytes bytes with
  | .error _ => false
  | .ok m => (Writer.module m ++ "\n").toUTF8 == bytes

#guard roundtrip localStruct.toUTF8
def pilotFirst : String := include_str "../../../test/semantics/golden/first.core.json"
#guard roundtrip pilotFirst.toUTF8
#guard (Run.validateBytes pilotFirst.toUTF8).1 = "[\"ok\"]"
#guard (Run.runBytes { profile := .release, fuel := 200 } pilotFirst.toUTF8).1 =
  "[\"done\",[\"returned\"],\"33\\n\"]"
#guard (Run.runBytes { profile := .debug, fuel := 200 } pilotFirst.toUTF8).1 =
  "[\"done\",[\"returned\"],\"33\\n\"]"

/- Record traversal never gives array operations a run of fields. -/
#guard (Val.record 0 #[.int .i64 1]).elems?.isNone
#guard (Val.record 0 #[.int .i64 1]).get? [0] |>.isSome

def nestedOwner (contents : Mutability) (m : Module) : Module :=
  let scalar := Ty.int .i64
  let inner := Ty.structT 0 (.cons scalar .nil)
  let outer := Ty.structT 1 (.cons inner .nil)
  let innerDef : StructDef := ⟨8, #[⟨scalar, .mutable, .mutable, 0⟩]⟩
  let outerDef : StructDef := ⟨8, #[⟨inner, .immutable, contents, 0⟩]⟩
  let m' := { m with
    types := #[scalar, inner, outer]
    structs := #[innerDef, outerDef]
    impls := m.impls.modify 0 fun impl => { impl with vars := #[⟨"p", outer, .immutable, 0, 0⟩] } }
  withBody m' [
    .letS 0 (.structLit outer [.structLit inner [.lit .i64 1]]) 0,
    .assign (.field (.field (.var 0) 0) 0) (.lit .i64 9) 1,
    .print [.expr (.read (.field (.field (.var 0) 0) 0))] 2]

#guard runChange (nestedOwner .mutable) .release "[\"done\",[\"returned\"],\"9\\n\"]"
#guard checkChange (nestedOwner .readOnly) "V-MUT"

def contentsAlias (m : Module) : Module :=
  let m' := nestedOwner .readOnly m
  let m'' := { m' with structs := m'.structs.modify 1 fun d =>
    { d with fields := d.fields.modify 0 fun f => { f with binding := .mutable } } }
  withBody m'' (initialization m'' ++ [
    .assign (.field (.deref (.ref .mutable (.field (.var 0) 0))) 0) (.lit .i64 9) 1])

#guard checkChange contentsAlias "V-TYPE"

def referenceArgument (contents : Mutability) (m : Module) : Module :=
  let base := nestedOwner contents m
  let base' := { base with structs := base.structs.modify 1 fun d =>
    { d with fields := d.fields.modify 0 fun f => { f with binding := .mutable } } }
  match base'.structType? 0 with
  | none => base'
  | some inner =>
    let callee : Impl := {
      name := "write"
      params := #[⟨0, .byRef⟩]
      results := #[]
      vars := #[⟨"value", .ref .mutable inner, .immutable, 0, 0⟩]
      body := .mk 0 [.assign (.field (.deref (.read (.var 0))) 0) (.lit .i64 9) 1] none
      summary := .unknown }
    let m' := { base' with
      impls := base'.impls.push callee
      contexts := base'.contexts.push ⟨1, "write", [(0, [.param 0])], [], []⟩ }
    withBody m' (initialization base' ++ [
      .expr (.call 1 [.byRef .mutable (.field (.var 0) 0)] 2) 2,
      .print [.expr (.read (.field (.field (.var 0) 0) 0))] 2])

#guard runChange (referenceArgument .mutable) .release "[\"done\",[\"returned\"],\"9\\n\"]"
#guard checkChange (referenceArgument .readOnly) "V-TYPE"

def effectfulOwner (m : Module) : Module :=
  let m' := { m with impls := m.impls.modify 0 fun impl =>
    { impl with vars := impl.vars.push ⟨"temporary", .int .i64, .immutable, 1, 0⟩ } }
  let reference := Expr.blockE (.mk 1 [.letS 1 (.lit .i64 0) 0] (some (.ref .readOnly (.var 0))))
  withBody m' (initialization m ++ [.print [.expr (.read (.field (.deref reference) 1))] 2])

#guard runChange effectfulOwner .release "[\"done\",[\"returned\"],\"40\\n\"]"

def arrayOwner (contents : Mutability) (m : Module) : Module :=
  let scalar := Ty.int .i64
  let array := Ty.arr scalar 2
  let owner := Ty.structT 0 (.cons array .nil)
  let d : StructDef := ⟨16, #[⟨array, .immutable, contents, 0⟩]⟩
  let elem := Place.elem (.of (.field (.var 0) 0)) (.lit .i64 0) 1
  let m' := { m with
    types := #[scalar, array, owner]
    structs := #[d]
    impls := m.impls.modify 0 fun impl => { impl with vars := #[⟨"p", owner, .immutable, 0, 0⟩] } }
  withBody m' [
    .letS 0 (.structLit owner [.arrLit array [.lit .i64 1, .lit .i64 2]]) 0,
    .assign elem (.lit .i64 9) 1,
    .print [.expr (.read elem)] 2]

#guard runChange (arrayOwner .mutable) .release "[\"done\",[\"returned\"],\"9\\n\"]"
#guard checkChange (arrayOwner .readOnly) "V-MUT"

def reencodedChange (change : Module → Module) : Bool :=
  match Decode.decodeBytes localStruct.toUTF8 with
  | .error _ => false
  | .ok m =>
    let m' := change m
    let bytes := (Writer.module m' ++ "\n").toUTF8
    match Decode.decodeBytes bytes with
    | .error _ => false
    | .ok m'' => match validate m'' with
      | .error _ => false
      | .ok () => Writer.module m'' == Writer.module m'

#guard reencodedChange (nestedOwner .mutable)
#guard reencodedChange (arrayOwner .mutable)

def malformed (s : String) : Bool := (Run.validateBytes s.toUTF8).2 == 2

#guard malformed (include_str "../../../test/semantics/malformed/struct_pilot_shape.core.json")
#guard malformed (include_str "../../../test/semantics/malformed/struct_forward_type.core.json")
#guard malformed (include_str "../../../test/semantics/malformed/struct_duplicate_type.core.json")
#guard malformed (include_str "../../../test/semantics/malformed/struct_missing_type.core.json")
#guard malformed (include_str "../../../test/semantics/malformed/struct_binding.core.json")
#guard malformed (include_str "../../../test/semantics/malformed/struct_zero_size.core.json")

/-- Address formation in a called initializer does not read later global storage. -/
def laterGlobalFieldAddress (m : Module) : Module :=
  match m.structType? 0 with
  | none => m
  | some t =>
    let addressOnly : Impl :=
      { name := "address_only"
        params := #[]
        results := #[.int .i64]
        vars := #[]
        body := .mk 0 [.expr (.ref .mutable (.field (.global 1) 1)) 0,
        .ret (some (.lit .i64 0)) 0] none,
        summary := .known ⟨[], [], [], [], false, false⟩ }
    { m with
      globals := #[⟨"first", .int .i64, .immutable, .call 1 [] 0, 0⟩,
        ⟨"later", t, .immutable, .structLit t [.lit .u8 1, .lit .i64 40, .lit .i16 7], 0⟩]
      impls := m.impls.push addressOnly
      contexts := m.contexts.push ⟨1, "address_only()", [], [[]], []⟩ }

#guard checkChange laterGlobalFieldAddress "ok"
#guard runChange laterGlobalFieldAddress .release localResult
#guard runChange laterGlobalFieldAddress .debug localResult

end Goose.Core.StructChecks
