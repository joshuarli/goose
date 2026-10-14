import Goose.Construct.Syntax
import Goose.Core.Json

namespace Goose.Construct.Decode
open Lean (Json)
open Goose.Core (Mutability VarKind originKinds IntTy OriginId VarId GlobalId ContextId Param NonlocalTarget Request)
open Goose.Core.Decode

def tyList : List Ty → TyList
  | [] => .nil
  | t :: ts => .cons t (tyList ts)


structure RawStructField where
  typeIndex : Nat
  binding : VarKind
  contents : Mutability
  byteOffset : Nat

structure RawStructDef where
  byteSize : Nat
  fields : Array RawStructField

def decStructDefs (j : Json) : Except String (Array RawStructDef) := do
  (← asArr j "structs").mapM fun entry => do
    let (tag, fs) ← record entry "struct descriptor"
    unless tag == "struct_def" do fail "expected a struct_def"
    arity tag fs 2
    let byteSize ← asNat fs[0]! "struct byte size"
    if byteSize == 0 then fail "struct byte size must be positive"
    let fields ← (← asArr fs[1]! "struct fields").mapM fun entry => do
      let (tag, fs) ← record entry "struct field"
      unless tag == "field" do fail "expected a field"
      arity tag fs 4
      let typeIndex ← asNat fs[0]! "field type"
      let binding ← decVarKind (← asStr fs[1]! "field binding")
      let contents ← decMut (← asStr fs[2]! "field contents")
      let byteOffset ← asNat fs[3]! "field byte offset"
      pure ({ typeIndex, binding, contents, byteOffset } : RawStructField)
    pure { byteSize, fields }

def resolveStruct (types : Array Ty) (sizes : Array Nat) (d : RawStructDef) :
    Except String (StructDef × Nat) := do
  let mut fields := #[]
  let mut treeSize := 1
  for f in d.fields do
    let i ← checkIndex f.typeIndex types.size "struct field type component"
    let some t := types[i]? | fail "struct field type"
    let some z := sizes[i]? | fail "struct field type size"
    treeSize := treeSize + z
    fields := fields.push { ty := t, binding := f.binding, contents := f.contents, byteOffset := f.byteOffset }
  pure ({ byteSize := d.byteSize, fields }, treeSize)


def decTypeEntry (types : Array Ty) (sizes : Array Nat) (j : Json)
    (structs : Array RawStructDef := #[]) :
    Except String (Ty × Nat) := do
  let (tag, fs) ← record j "type"
  let comp (x : Json) : Except String (Ty × Nat) := do
    let i ← checkIndex (← asNat x s!"{tag} component") types.size "type component"
    match types[i]?, sizes[i]? with
    | some t, some z => pure (t, z)
    | _, _ => fail "type component"
  match tag with
  | "int" => do
    arity tag fs 1
    pure (.int (← decIntTy (← asStr fs[0]! "int type")), 1)
  | "bool" => do arity tag fs 0; pure (.bool, 1)
  | "unit" => do arity tag fs 0; pure (.unit, 1)
  | "arr" => do
    arity tag fs 2
    let (t, z) ← comp fs[0]!
    let k ← asNat fs[1]! "arr count"
    if k < 1 then fail "arr: count below 1"
    pure (.arr t k, z + 1)
  | "varr" => do
    arity tag fs 1
    let (e, z) ← comp fs[0]!
    pure (.varr e, z + 1)
  | "grow" => do
    arity tag fs 1
    let (t, z) ← comp fs[0]!
    pure (.grow t, z + 1)
  | "ref" => do
    arity tag fs 2
    let m ← decMut (← asStr fs[0]! "ref mutability")
    let (t, z) ← comp fs[1]!
    pure (.ref m t, z + 1)
  | "slice" => do
    arity tag fs 2
    let m ← decMut (← asStr fs[0]! "slice mutability")
    let (t, z) ← comp fs[1]!
    pure (.slice m t, z + 1)
  | "tuple" => do
    arity tag fs 1
    let parts ← (← asArr fs[0]! "tuple components").toList.mapM comp
    if parts.length < 2 then fail "tuple: fewer than two components"
    pure (.tuple (tyList (parts.map (·.1))), 1 + (parts.map (·.2)).foldl (· + ·) 0)
  | "struct" => do
    arity tag fs 1
    let sid ← checkIndex (← asNat fs[0]! "struct id") structs.size "struct"
    let some raw := structs[sid]? | fail "struct id"
    let (d, z) ← resolveStruct types sizes raw
    pure (.structT sid (TyList.ofList (d.fields.toList.map (·.ty))), z)
  | "growshrink" => do

    arity tag fs 1
    let (e, z) ← comp fs[0]!
    pure (.growshrink e, z + 1)
  | "limited" => do

    arity tag fs 2
    let (e, z) ← comp fs[0]!
    let capacity ← asNat fs[1]! "limited capacity"
    if capacity == 0 then fail "limited capacity must be positive"
    pure (.limited e capacity, z + 1)
  | _ => fail s!"unknown type tag {tag.quote}"

def decTypesWithStructs (j : Json) (rawStructs : Array RawStructDef) :
    Except String (Array Ty × Array StructDef) := do
  let entries ← asArr j "types"
  let mut types : Array Ty := #[]
  let mut sizes : Array Nat := #[]
  let mut definitions : Array (Option StructDef) := Array.replicate rawStructs.size none
  for h : i in [0:entries.size] do
    let (t, z) ← match decTypeEntry types sizes entries[i] rawStructs with
      | .ok r => pure r
      | .error e => fail s!"type {i}: {e}"
    if z > maxTypeTreeSize then fail s!"type {i}: tree size over {maxTypeTreeSize}"
    match t with
    | .structT sid _ =>
      if (definitions[sid]?).any (·.isSome) then fail "a struct descriptor has more than one type entry"
      let some raw := rawStructs[sid]? | fail "struct id"
      let (d, _) ← resolveStruct types sizes raw
      definitions := definitions.set! sid (some d)
    | _ => pure ()
    types := types.push t
    sizes := sizes.push z
  let structs ← definitions.mapM fun
    | some d => pure d
    | none => fail "a struct descriptor has no type entry"
  pure (types, structs)




structure Ctx where
  types : Array Ty
  nGlobals : Nat
  nContexts : Nat
  nOrigins : Nat
  nVars : Nat
  nTargets : Nat


structure Count where
  nodes : Nat
  blocks : Nat

abbrev R := StateT Count (Except String)

def liftE (e : Except String α) : R α := e


def openRecord (j : Json) (what : String) : R (String × Array Json) := do
  let c ← get
  if c.nodes ≥ maxNodesPerFunction then
    throw s!"more than {maxNodesPerFunction} nodes in one function"
  set { c with nodes := c.nodes + 1 }
  liftE (record j what)

def decTyRef (cx : Ctx) (j : Json) : Except String Ty := do
  let i ← checkIndex (← asNat j "type") cx.types.size "type"
  match cx.types[i]? with
  | some t => pure t
  | none => fail "type"

def decOrg (cx : Ctx) (j : Json) : Except String OriginId := do
  checkIndex (← asNat j "origin") cx.nOrigins "origin"

def decVar (cx : Ctx) (j : Json) : Except String VarId := do
  checkIndex (← asNat j "variable") cx.nVars "variable"

def decGlob (cx : Ctx) (j : Json) : Except String GlobalId := do
  checkIndex (← asNat j "global") cx.nGlobals "global"

def decCtxRef (cx : Ctx) (j : Json) : Except String ContextId := do
  checkIndex (← asNat j "context") cx.nContexts "context"

def intRange (t : IntTy) (n : Int) : Except String Unit :=
  if t.inRange n then pure () else fail s!"constant {n} out of range for its integer type"

mutual

def decPlace : Nat → Ctx → Json → R Place
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "place"
    match tag with
    | "p_local" => do liftE (arity tag fs 1); pure (.var (← liftE (decVar cx fs[0]!)))
    | "p_global" => do liftE (arity tag fs 1); pure (.global (← liftE (decGlob cx fs[0]!)))
    | "p_deref" => do liftE (arity tag fs 1); pure (.deref (← decExpr f cx fs[0]!))
    | "p_elem" => do
      liftE (arity tag fs 3)
      let v ← decView f cx fs[0]!
      let i ← decExpr f cx fs[1]!
      pure (.elem v i (← liftE (decOrg cx fs[2]!)))
    | "p_field" => do

      liftE (arity tag fs 2)
      let p ← decPlace f cx fs[0]!
      pure (.field p (← liftE (asNat fs[1]! "real field index")))
    | _ => throw s!"unknown place tag {tag.quote}"

def decView : Nat → Ctx → Json → R View
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "view"
    match tag with
    | "v_of" => do liftE (arity tag fs 1); pure (.of (← decPlace f cx fs[0]!))
    | "v_val" => do liftE (arity tag fs 1); pure (.val (← decExpr f cx fs[0]!))
    | _ => throw s!"unknown view tag {tag.quote}"

def decBound : Nat → Ctx → Json → R Bound
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "bound"
    match tag with
    | "b_expr" => do liftE (arity tag fs 1); pure (.expr (← decExpr f cx fs[0]!))
    | "b_end" => do liftE (arity tag fs 1); pure (.fromEnd (← decExpr f cx fs[0]!))
    | "b_none" => do liftE (arity tag fs 0); pure .omitted
    | _ => throw s!"unknown bound tag {tag.quote}"

def decArg : Nat → Ctx → Json → R Arg
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "argument"
    match tag with
    | "a_val" => do liftE (arity tag fs 1); pure (.byVal (← decExpr f cx fs[0]!))
    | "a_construct" => do
      liftE (arity tag fs 1)
      pure (.construct (← decExpr f cx fs[0]!))
    | "a_ref" => do
      liftE (arity tag fs 2)
      let m ← liftE (decMut (← asStr fs[0]! "a_ref mutability"))
      pure (.byRef m (← decPlace f cx fs[1]!))
    | _ => throw s!"unknown argument tag {tag.quote}"

def decExprs : Nat → Ctx → Json → R (List Expr)
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let a ← liftE (asArr j "expression list")
    a.toList.mapM (decExpr f cx)

def decExpr : Nat → Ctx → Json → R Expr
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "expression"
    match tag with
    | "e_lit" => do
      liftE (arity tag fs 2)
      match (← liftE (decTyRef cx fs[0]!)) with
      | .int t =>
        let n ← liftE (asInt fs[1]! "e_lit")
        liftE (intRange t n)
        pure (.lit t n)
      | _ => throw "e_lit: type is not an integer type"
    | "e_bool" => do liftE (arity tag fs 1); pure (.bool (← liftE (asFlag fs[0]! "e_bool")))
    | "e_read" => do liftE (arity tag fs 1); pure (.read (← decPlace f cx fs[0]!))
    | "e_ref" => do
      liftE (arity tag fs 2)
      let m ← liftE (decMut (← asStr fs[0]! "e_ref mutability"))
      pure (.ref m (← decPlace f cx fs[1]!))
    | "e_slice" => do
      liftE (arity tag fs 5)
      let m ← liftE (decMut (← asStr fs[0]! "e_slice mutability"))
      let v ← decView f cx fs[1]!
      let lo ← decBound f cx fs[2]!
      let hi ← decBound f cx fs[3]!
      pure (.slice m v lo hi (← liftE (decOrg cx fs[4]!)))
    | "e_len" => do liftE (arity tag fs 1); pure (.len (← decView f cx fs[0]!))
    | "e_un" => do
      liftE (arity tag fs 3)
      let op ← liftE (decUnOp (← asStr fs[0]! "e_un operator"))
      let e ← decExpr f cx fs[1]!
      pure (.un op e (← liftE (decOrg cx fs[2]!)))
    | "e_bin" => do
      liftE (arity tag fs 4)
      let op ← liftE (decBinOp (← asStr fs[0]! "e_bin operator"))
      let a ← decExpr f cx fs[1]!
      let b ← decExpr f cx fs[2]!
      pure (.bin op a b (← liftE (decOrg cx fs[3]!)))
    | "e_cmp" => do
      liftE (arity tag fs 3)
      let op ← liftE (decCmpOp (← asStr fs[0]! "e_cmp comparison"))
      let a ← decExpr f cx fs[1]!
      pure (.cmp op a (← decExpr f cx fs[2]!))
    | "e_and" => do
      liftE (arity tag fs 2)
      let a ← decExpr f cx fs[0]!
      pure (.and a (← decExpr f cx fs[1]!))
    | "e_or" => do
      liftE (arity tag fs 2)
      let a ← decExpr f cx fs[0]!
      pure (.or a (← decExpr f cx fs[1]!))
    | "e_not" => do liftE (arity tag fs 1); pure (.not (← decExpr f cx fs[0]!))
    | "e_conv" => do
      liftE (arity tag fs 4)
      let k ← liftE (decConvKind (← asStr fs[0]! "e_conv kind"))
      let t ← liftE (decTyRef cx fs[1]!)
      let e ← decExpr f cx fs[2]!
      pure (.conv k t e (← liftE (decOrg cx fs[3]!)))
    | "e_call" => do
      liftE (arity tag fs 3)
      let c ← liftE (decCtxRef cx fs[0]!)
      let args ← (← liftE (asArr fs[1]! "e_call arguments")).toList.mapM (decArg f cx)
      pure (.call c args (← liftE (decOrg cx fs[2]!)))
    | "e_push" => do
      liftE (arity tag fs 3)
      let p ← decPlace f cx fs[0]!
      let e ← decExpr f cx fs[1]!
      let org := some (← liftE (decOrg cx fs[2]!))
      pure (.push p e org)
    | "e_pop" => do

      liftE (arity tag fs 2)
      let p ← decPlace f cx fs[0]!
      pure (.pop p (← liftE (decOrg cx fs[1]!)))
    | "e_if" => do
      liftE (arity tag fs 3)
      let c ← decExpr f cx fs[0]!
      let t ← decBlock f cx fs[1]!
      pure (.ifE c t (← decBlock f cx fs[2]!))
    | "e_block" => do liftE (arity tag fs 1); pure (.blockE (← decBlock f cx fs[0]!))
    | "e_arr" => do
      liftE (arity tag fs 2)
      let t ← liftE (decTyRef cx fs[0]!)
      pure (.arrLit t (← decExprs f cx fs[1]!))
    | "e_fill" => do
      liftE (arity tag fs 2)
      let t ← liftE (decTyRef cx fs[0]!)
      pure (.fill t (← decExpr f cx fs[1]!))
    | "e_struct" => do

      liftE (arity tag fs 2)
      let t ← liftE (decTyRef cx fs[0]!)
      let es ← (← liftE (asArr fs[1]! "struct initializers")).toList.mapM (decExpr f cx)
      pure (.structLit t es)
    | "e_bytes" => do
      liftE (arity tag fs 3)
      let t ← liftE (decTyRef cx fs[0]!)
      let data ← liftE (list fs[1]! "literal bytes" fun byte => do
        let n ← asNat byte "literal byte"
        if n > 255 then fail "literal byte exceeds 255"
        pure (UInt8.ofNat n))
      pure (.bytes t data (← liftE (decOrg cx fs[2]!)))
    | "e_str" => do
      liftE (arity tag fs 3)
      let t ← liftE (decTyRef cx fs[0]!)
      let args ← (← liftE (asArr fs[1]! "string arguments")).toList.mapM (decPrintArg f cx)
      pure (.str t args (← liftE (decOrg cx fs[2]!)))
    | "e_copy" => do
      liftE (arity tag fs 3)
      let t ← liftE (decTyRef cx fs[0]!)
      let source ← decPlace f cx fs[1]!
      pure (.copy t source (← liftE (decOrg cx fs[2]!)))
    | "e_result_local" => do
      liftE (arity tag fs 2)
      pure (.resultLocal (← liftE (decVar cx fs[0]!)) (← liftE (decOrg cx fs[1]!)))
    | "e_values" => do
      liftE (arity tag fs 1)
      let operands ← decExprs f cx fs[0]!
      if operands.length < 2 then throw "e_values: fewer than two operands"
      pure (.values operands)
    | _ => throw s!"unknown expression tag {tag.quote}"


def decBlock : Nat → Ctx → Json → R Block
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "block"
    unless tag == "block" do throw s!"expected a block, found tag {tag.quote}"
    liftE (arity tag fs 3)
    let sc ← liftE (asNat fs[0]! "block scope")
    let c ← get
    unless sc = c.blocks do
      throw s!"block scope {sc}: {c.blocks} blocks were opened before it"
    set { c with blocks := c.blocks + 1 }
    let stmts ← (← liftE (asArr fs[1]! "block statements")).toList.mapM (decStmt f cx)
    let value ← match (← liftE (asArr fs[2]! "block value")).toList with
      | [] => pure none
      | [e] => do pure (some (← decExpr f cx e))
      | _ => throw "block value: at most one expression"
    pure (.mk sc stmts value)

def decPrintArg : Nat → Ctx → Json → R PrintArg
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "print argument"
    match tag with
    | "pa_text" => do liftE (arity tag fs 1); pure (.text (← liftE (asStr fs[0]! "pa_text")))
    | "pa_expr" => do liftE (arity tag fs 1); pure (.expr (← decExpr f cx fs[0]!))
    | "pa_view" => do
      liftE (arity tag fs 1)
      pure (.view (← decView f cx fs[0]!))
    | _ => throw s!"unknown print argument tag {tag.quote}"

def decStmt : Nat → Ctx → Json → R Stmt
  | 0, _, _ => throw "nesting too deep"
  | f + 1, cx, j => do
    let (tag, fs) ← openRecord j "statement"
    match tag with
    | "s_let" => do
      liftE (arity tag fs 3)
      let x ← liftE (decVar cx fs[0]!)
      let e ← decExpr f cx fs[1]!
      pure (.letS x e (← liftE (decOrg cx fs[2]!)))
    | "s_assign" => do
      liftE (arity tag fs 3)
      let p ← decPlace f cx fs[0]!
      let e ← decExpr f cx fs[1]!
      pure (.assign p e (← liftE (decOrg cx fs[2]!)))
    | "s_assign_op" => do
      liftE (arity tag fs 4)
      let op ← liftE (decBinOp (← asStr fs[0]! "s_assign_op operator"))
      let p ← decPlace f cx fs[1]!
      let e ← decExpr f cx fs[2]!
      pure (.assignOp op p e (← liftE (decOrg cx fs[3]!)))
    | "s_rebind" => do
      liftE (arity tag fs 3)
      let x ← liftE (decVar cx fs[0]!)
      let e ← decExpr f cx fs[1]!
      pure (.rebind x e (← liftE (decOrg cx fs[2]!)))
    | "s_expr" => do
      liftE (arity tag fs 2)
      let e ← decExpr f cx fs[0]!
      pure (.expr e (← liftE (decOrg cx fs[1]!)))
    | "s_append" => do
      liftE (arity tag fs 3)
      let p ← decPlace f cx fs[0]!
      let v ← decView f cx fs[1]!
      pure (.append p v (← liftE (decOrg cx fs[2]!)))
    | "s_pop_n" => do

      liftE (arity tag fs 3)
      let p ← decPlace f cx fs[0]!
      let e ← decExpr f cx fs[1]!
      pure (.popN p e (← liftE (decOrg cx fs[2]!)))
    | "s_resize" => do

      liftE (arity tag fs 4)
      let p ← decPlace f cx fs[0]!
      let size ← decExpr f cx fs[1]!
      let fill ← match (← liftE (asArr fs[2]! "s_resize fill")).toList with
        | [] => pure none
        | [e] => do pure (some (← decExpr f cx e))
        | _ => throw "s_resize: at most one fill"
      pure (.resize p size fill (← liftE (decOrg cx fs[3]!)))
    | "s_clear" => do

      liftE (arity tag fs 2)
      let p ← decPlace f cx fs[0]!
      pure (.clear p (← liftE (decOrg cx fs[1]!)))
    | "s_assign_whole" => do

      liftE (arity tag fs 3)
      let p ← decPlace f cx fs[0]!
      let e ← decExpr f cx fs[1]!
      pure (.assignWhole p e (← liftE (decOrg cx fs[2]!)))
    | "s_if" => do
      liftE (arity tag fs 4)
      let c ← decExpr f cx fs[0]!
      let t ← decBlock f cx fs[1]!
      let e ← match (← liftE (asArr fs[2]! "s_if else")).toList with
        | [] => pure none
        | [b] => do pure (some (← decBlock f cx b))
        | _ => throw "s_if else: at most one block"
      pure (.ifS c t e (← liftE (decOrg cx fs[3]!)))
    | "s_while" => do
      liftE (arity tag fs 3)
      let c ← decExpr f cx fs[0]!
      let b ← decBlock f cx fs[1]!
      pure (.while c b (← liftE (decOrg cx fs[2]!)))
    | "s_for_range" => do
      liftE (arity tag fs 5)
      let x ← liftE (decVar cx fs[0]!)
      let lo ← decExpr f cx fs[1]!
      let hi ← decExpr f cx fs[2]!
      let b ← decBlock f cx fs[3]!
      pure (.forRange x lo hi b (← liftE (decOrg cx fs[4]!)))
    | "s_for_each" => do
      liftE (arity tag fs 6)
      let x ← liftE (decVar cx fs[0]!)
      let idx ← liftE (optional fs[1]! "s_for_each index" (decVar cx))
      let v ← decView f cx fs[2]!
      let byRef ← liftE (asFlag fs[3]! "s_for_each by_ref")
      let b ← decBlock f cx fs[4]!
      pure (.forEach x idx v byRef b (← liftE (decOrg cx fs[5]!)))
    | "s_ret" => do
      liftE (arity tag fs 2)
      let e ← match (← liftE (asArr fs[0]! "s_ret value")).toList with
        | [] => pure none
        | [e] => do pure (some (← decExpr f cx e))
        | _ => throw "s_ret: at most one value"
      pure (.ret e (← liftE (decOrg cx fs[1]!)))
    | "s_break" => do liftE (arity tag fs 1); pure (.brk (← liftE (decOrg cx fs[0]!)))
    | "s_continue" => do liftE (arity tag fs 1); pure (.cont (← liftE (decOrg cx fs[0]!)))
    | "s_print" => do
      liftE (arity tag fs 2)
      let args ← (← liftE (asArr fs[0]! "s_print arguments")).toList.mapM (decPrintArg f cx)
      pure (.print args (← liftE (decOrg cx fs[1]!)))
    | "s_assert" => do
      liftE (arity tag fs 2)
      let e ← decExpr f cx fs[0]!
      pure (.assertS e (← liftE (decOrg cx fs[1]!)))
    | "s_abort" => do
      liftE (arity tag fs 2)
      let msg ← liftE (asStr fs[0]! "s_abort message")
      pure (.abort msg (← liftE (decOrg cx fs[1]!)))
    | "s_exit" => do
      liftE (arity tag fs 2)
      let e ← decExpr f cx fs[0]!
      pure (.exit e (← liftE (decOrg cx fs[1]!)))
    | "s_receive" => do
      liftE (arity tag fs 3)
      let vars ← liftE (list fs[0]! "received variables" (decVar cx))
      if vars.length < 2 then throw "s_receive: fewer than two variables"
      let producer ← decExpr f cx fs[1]!
      pure (.receive vars producer (← liftE (decOrg cx fs[2]!)))
    | "s_append_value" | "s_append_construct" => do
      liftE (arity tag fs 3)
      let owner ← decPlace f cx fs[0]!
      let producer ← decExpr f cx fs[1]!
      let org ← liftE (decOrg cx fs[2]!)
      pure (if tag == "s_append_value" then .appendValue owner producer org
        else .appendConstruct owner producer org)
    | "s_ret_values" => do
      liftE (arity tag fs 2)
      let operands ← decExprs f cx fs[0]!
      pure (.retValues operands (← liftE (decOrg cx fs[1]!)))
    | "s_ret_forward" => do
      liftE (arity tag fs 2)
      let producer ← decExpr f cx fs[0]!
      pure (.retForward producer (← liftE (decOrg cx fs[1]!)))
    | "s_return_from" => do
      liftE (arity tag fs 3)
      let target ← liftE (checkIndex (← asNat fs[0]! "return target") cx.nTargets "target")
      let operands ← decExprs f cx fs[1]!
      pure (.returnFrom target operands (← liftE (decOrg cx fs[2]!)))
    | "s_return_from_forward" => do
      liftE (arity tag fs 3)
      let target ← liftE (checkIndex (← asNat fs[0]! "return target") cx.nTargets "target")
      let producer ← decExpr f cx fs[1]!
      pure (.returnFromForward target producer (← liftE (decOrg cx fs[2]!)))
    | "s_break_value" => do
      liftE (arity tag fs 2)
      pure (.breakValue (← decExpr f cx fs[0]!) (← liftE (decOrg cx fs[1]!)))
    | _ => throw s!"unknown statement tag {tag.quote}"

end



def decTarget (nGlobals nParams : Nat) (j : Json) : Except String Target := do
  let (tag, fs) ← record j "effect target"
  arity tag fs 1
  match tag with
  | "t_param" => pure (.param (← checkIndex (← asNat fs[0]! "t_param") nParams "parameter"))
  | "t_global" => pure (.global (← checkIndex (← asNat fs[0]! "t_global") nGlobals "global"))
  | _ => fail s!"unknown target tag {tag.quote}"

def targetKey : Target → Nat × Nat
  | .param i => (0, i)
  | .global g => (1, g)


def targetsSorted : List Target → Bool
  | a :: b :: rest => ((targetKey a).1 < (targetKey b).1 || ((targetKey a).1 == (targetKey b).1 && (targetKey a).2 < (targetKey b).2)) && targetsSorted (b :: rest)
  | _ => true

def decTargets (nGlobals nParams : Nat) (j : Json) (what : String) : Except String (List Target) := do
  let ts ← list j what (decTarget nGlobals nParams)
  unless targetsSorted ts do fail s!"{what}: targets unsorted or repeated"
  pure ts

private def sortedNats (values : List Nat) : Bool :=
  match values with
  | first :: second :: rest => first < second && sortedNats (second :: rest)
  | _ => true

private def naturalList (j : Json) (what : String) (bound : Nat) : Except String (List Nat) := do
  let values ← list j what fun entry => do checkIndex (← asNat entry what) bound what
  if !sortedNats values then fail s!"{what}: unsorted or repeated"
  pure values

def decSummary (nGlobals nParams nResults nTargets : Nat) (j : Json) : Except String SummaryAnn := do
  let (tag, fs) ← record j "summary"
  match tag with
  | "summary_unknown" => do arity tag fs 0; pure .unknown
  | "summary" => do
    arity tag fs 10
    pure (.known {
      reads := ← decTargets nGlobals nParams fs[0]! "summary reads"
      writes := ← decTargets nGlobals nParams fs[1]! "summary writes"
      grows := ← decTargets nGlobals nParams fs[2]! "summary grows"
      shrinks := ← decTargets nGlobals nParams fs[3]! "summary shrinks"
      rebinds := ← decTargets nGlobals nParams fs[4]! "summary rebinds"
      constructs := ← naturalList fs[5]! "summary constructs" nResults
      needs := ← naturalList fs[6]! "summary needs" nTargets
      escapes := ← naturalList fs[7]! "summary escapes" nTargets
      aborts := ← asFlag fs[8]! "summary aborts"
      outputs := ← asFlag fs[9]! "summary outputs" })
  | _ => fail s!"unknown summary tag {tag.quote}"

private def decResult (cx : Ctx) (j : Json) : Except String ResultDescriptor := do
  let (tag, fields) ← record j "result"
  unless tag == "result" do fail "expected result descriptor"
  arity tag fields 3
  let ty ← decTyRef cx fields[0]!
  let requestTag ← asStr fields[1]! "result request"
  let some request := Request.ofTag? requestTag | fail "unknown result request"
  let namedLocal ← optional fields[2]! "named result local" (decVar cx)
  pure { ty, request, namedLocal }

def decLocal (cx : Ctx) (j : Json) : R LocalVar := do
  let (tag, fs) ← openRecord j "local"
  unless tag == "local" do throw s!"expected a local, found tag {tag.quote}"
  liftE (arity tag fs 5)
  pure {
    name := ← liftE (asStr fs[0]! "local name")
    ty := ← liftE (decTyRef cx fs[1]!)
    kind := ← liftE (decVarKind (← asStr fs[2]! "local kind"))
    scope := ← liftE (asNat fs[3]! "local scope")
    org := ← liftE (decOrg cx fs[4]!) }

def decParam (nVars : Nat) (locals : Array LocalVar) (i : Nat) (j : Json) : R Param := do
  let (tag, fs) ← openRecord j "param"
  unless tag == "param" do throw s!"expected a param, found tag {tag.quote}"
  liftE (arity tag fs 2)
  let v ← liftE (checkIndex (← asNat fs[0]! "param variable") nVars "variable")
  unless v = i do throw s!"parameter {i} names variable {v}"
  match locals[v]? with
  | some lv => unless lv.scope = 0 do throw s!"parameter {i} is declared at scope {lv.scope}"
  | none => throw s!"parameter {i}: no variable row"
  pure ⟨v, ← liftE (decMode (← asStr fs[1]! "param mode"))⟩

def decImplBody (cx : Ctx) (j : Json) : R Impl := do
  let (tag, fs) ← openRecord j "impl"
  unless tag == "impl" do throw s!"expected an impl, found tag {tag.quote}"
  liftE (arity tag fs 6)
  let name ← liftE (asStr fs[0]! "impl name")
  let localsJ ← liftE (asArr fs[3]! "impl variables")
  let locals ← localsJ.mapM (decLocal cx)
  let cx' := { cx with nVars := locals.size }
  let paramsJ ← liftE (asArr fs[1]! "impl parameters")
  let mut params : Array Param := #[]
  for h : i in [0:paramsJ.size] do
    params := params.push (← decParam locals.size locals i paramsJ[i])
  let results ← liftE (list fs[2]! "impl results" (decResult cx'))
  modify fun c => { c with blocks := 0 }
  let body ← decBlock decodeFuel cx' fs[4]!
  let nBlocks := (← get).blocks
  for lv in locals do
    unless lv.scope < nBlocks do
      throw s!"variable {lv.name.quote}: scope {lv.scope} is not among the {nBlocks} scopes"
  let summary ← liftE (decSummary cx.nGlobals params.size results.length cx.nTargets fs[5]!)
  pure { name, params, results := results.toArray, vars := locals, body, summary }

def decImpl (cx : Ctx) (j : Json) : Except String Impl :=
  (decImplBody cx j).run' ⟨0, 0⟩

def decGlobal (cx : Ctx) (j : Json) : Except String Global :=
  (do
    let (tag, fs) ← openRecord j "global"
    unless tag == "global" do throw s!"expected a global, found tag {tag.quote}"
    liftE (arity tag fs 5)
    let name ← liftE (asStr fs[0]! "global name")
    let ty ← liftE (decTyRef cx fs[1]!)
    let kind ← liftE (decVarKind (← asStr fs[2]! "global kind"))
    let init ← decExpr decodeFuel { cx with nVars := 0 } fs[3]!
    let org ← liftE (decOrg cx fs[4]!)
    pure ({ name, ty, kind, init, org } : Global)).run' ⟨0, 0⟩

def decRootRef (impl : Impl) (nGlobals : Nat) (j : Json) : Except String RootRef := do
  let (tag, fs) ← record j "root"
  if tag == "r_static" then
    arity tag fs 0
    return .static
  arity tag fs 1
  let n ← asNat fs[0]! tag
  match tag with
  | "r_local" => pure (.local (← checkIndex n impl.vars.size "variable"))
  | "r_global" => pure (.global (← checkIndex n nGlobals "global"))
  | "r_param" => pure (.param (← checkIndex n impl.params.size "parameter"))
  | _ => fail s!"unknown root tag {tag.quote}"

def decContext (impls : Array Impl) (nGlobals : Nat) (j : Json) : Except String Context := do
  let (tag, fs) ← record j "context"
  unless tag == "context" do fail s!"expected a context, found tag {tag.quote}"
  arity tag fs 4
  let i ← checkIndex (← asNat fs[0]! "context impl") impls.size "implementation"
  let some impl := impls[i]? | fail "context impl"
  let decl ← asStr fs[1]! "context declaration key"
  let roots (x : Json) := list x "root set" (decRootRef impl nGlobals)
  let vrs ← list fs[2]! "context variable roots" fun vj => do
    let (vtag, vfs) ← record vj "variable roots"
    unless vtag == "vr" do fail s!"expected vr, found tag {vtag.quote}"
    unless vfs.size = 2 || vfs.size = 3 do
      fail s!"{vtag}: expected 2 or 3 fields, found {vfs.size}"
    let v ← checkIndex (← asNat vfs[0]! "vr variable") impl.vars.size "variable"
    let rs ← roots vfs[1]!

    let content ← if vfs.size = 3 then (do pure (some (← roots vfs[2]!))) else pure none
    pure (v, rs, content)
  let rec ascending : List (VarId × List RootRef × Option (List RootRef)) → Bool
    | a :: b :: rest => a.1 < b.1 && ascending (b :: rest)
    | _ => true
  unless ascending vrs do fail "context variable roots unsorted or repeated"
  let results ← list fs[3]! "context result roots" roots
  pure { impl := i, decl, varRoots := vrs.map fun (v, rs, _) => (v, rs), resultRoots := results
         contentRoots := vrs.filterMap fun (v, _, c) => c.map fun cs => (v, cs) }

def decFile (j : Json) : Except String String := do
  let (tag, fs) ← record j "file"
  unless tag == "file" do fail s!"expected a file, found tag {tag.quote}"
  arity tag fs 1
  asStr fs[0]! "file path"

def decOrigin (nFiles : Nat) (j : Json) : Except String Origin := do
  let (tag, fs) ← record j "origin"
  unless tag == "origin" do fail s!"expected an origin, found tag {tag.quote}"
  arity tag fs 3
  let file ← checkIndex (← asNat fs[0]! "origin file") nFiles "file"
  let line ← asNat fs[1]! "origin line"
  if line < 1 then fail "origin: line below 1"
  let kind ← asStr fs[2]! "origin kind"
  unless originKinds.contains kind do fail s!"origin: unknown node kind {kind.quote}"
  pure { file, line, kind }


def inEntry (what : String) (i : Nat) (r : Except String α) : Except String α :=
  match r with
  | .ok a => .ok a
  | .error e => .error s!"{what} {i}: {e}"

def decodeMapped (what : String) (j : Json) (dec : Json → Except String α) :
    Except String (Array α) := do
  let a ← asArr j what
  let mut out : Array α := #[]
  for h : i in [0:a.size] do
    out := out.push (← inEntry what i (dec a[i]))
  pure out

def schemaName : String := "goose-core/0.2"

private def decNonlocalTarget (nImpls : Nat) (j : Json) : Except String NonlocalTarget := do
  let (tag, fields) ← record j "nonlocal target"
  unless tag == "target" do fail "expected nonlocal target"
  arity tag fields 1
  let members ← naturalList fields[0]! "target members" nImpls
  match members with
  | [] => fail "target members: empty set"
  | first :: rest => pure ⟨first, rest⟩

def decodeModule (j : Json) : Except String Module := do
  let (tag, fs) ← record j "module"
  unless tag == "module" do fail s!"expected a module, found tag {tag.quote}"
  arity tag fs 11
  let schema ← asStr fs[0]! "schema"
  unless schema == schemaName do fail "unsupported schema"
  unless (← asStr fs[1]! "profile") == "core-construction" do fail "expected core-construction"
  let files ← decodeMapped "file" fs[2]! decFile
  let origins ← decodeMapped "origin" fs[10]! (decOrigin files.size)
  let rawStructs ← decStructDefs fs[4]!
  let (types, structs) ← decTypesWithStructs fs[3]! rawStructs
  let nGlobals := (← asArr fs[6]! "globals").size
  let nContexts := (← asArr fs[8]! "contexts").size
  let nImpls := (← asArr fs[7]! "implementations").size
  let targets ← decodeMapped "target" fs[5]! (decNonlocalTarget nImpls)
  let cx : Ctx := { types, nGlobals, nContexts, nOrigins := origins.size, nVars := 0, nTargets := targets.size }
  let globals ← decodeMapped "global" fs[6]! (decGlobal cx)
  let impls ← decodeMapped "impl" fs[7]! (decImpl cx)
  let contexts ← decodeMapped "context" fs[8]! (decContext impls nGlobals)
  let entry ← checkIndex (← asNat fs[9]! "entry") nContexts "context"
  pure { files, types, globals, impls, contexts, entry, origins, structs, targets }

def decodeBytes (bs : ByteArray) : Except String Module := do
  scan bs
  let some text := String.fromUTF8? bs | fail "input is not valid UTF-8"
  match Json.parse text with
  | .error e => fail s!"JSON: {e}"
  | .ok j => decodeModule j

end Goose.Construct.Decode
