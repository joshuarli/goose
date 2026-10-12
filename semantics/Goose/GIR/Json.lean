import Goose.Core.Json
import Goose.GIR.Syntax

/-!
The `gir-h/0.2` encoding: a strict decoder and the deterministic writer.

The encoding follows the Core one (`Goose.Core.Decode`): arrays, strings and
unsigned integers only, a tag and a fixed arity per record, no objects. The
decoder reuses Core's byte scan and scalar readers, so an input is held to the
same limits (size, nesting, alphabet) and every failure is a message that the
caller reports as `malformed`.

The type table is not part of the in-memory module. The decoder resolves each
index to a type; the writer builds the table again, numbering types by first
mention in document order, components before the type that uses them, so a
module written by `write` reads back to the same bytes.
-/

namespace Goose.GIR.Json

open Goose.Core
open Goose.Core.Decode (fail record arity asNat asStr asArr asFlag asInt decIntTy decMut decVarKind
  decUnOp decBinOp decCmpOp decConvKind list optional checkIndex natLimit)

def schemaName : String := "gir-h/0.2"
def profileName : String := "core-pilot"

/-! ### Decoder -/

/-- Tables a function's records are read against. -/
structure Tables where
  types : Array VTy
  nGlobals : Nat
  nFuncs : Nat
  nOrigins : Nat
  nSlots : Nat
  nScopes : Nat
  nBlocks : Nat

def decVTypeEntry (types : Array VTy) (sizes : Array Nat) (j : Lean.Json) : Except String (VTy × Nat) := do
  let (tag, fs) ← record j "type"
  let comp (x : Lean.Json) : Except String (Ty × Nat) := do
    let i ← checkIndex (← asNat x s!"{tag} component") types.size "type component"
    match types[i]?, sizes[i]? with
    | some (.data t), some z => pure (t, z)
    | some (.view ..), _ => fail "type component: a view is not a component of another type"
    | _, _ => fail "type component"
  match tag with
  | "int" => do
    arity tag fs 1
    pure (.data (.int (← decIntTy (← asStr fs[0]! "int type"))), 1)
  | "bool" => do arity tag fs 0; pure (.data .bool, 1)
  | "unit" => do arity tag fs 0; pure (.data .unit, 1)
  | "arr" => do
    arity tag fs 2
    let (t, z) ← comp fs[0]!
    let k ← asNat fs[1]! "arr count"
    if k < 1 then fail "arr: count below 1"
    pure (.data (.arr t k), z + 1)
  | "grow" => do
    arity tag fs 1
    let (t, z) ← comp fs[0]!
    pure (.data (.grow t), z + 1)
  | "ref" => do
    arity tag fs 2
    let m ← decMut (← asStr fs[0]! "ref mutability")
    let (t, z) ← comp fs[1]!
    pure (.data (.ref m t), z + 1)
  | "slice" => do
    arity tag fs 2
    let m ← decMut (← asStr fs[0]! "slice mutability")
    let (t, z) ← comp fs[1]!
    pure (.data (.slice m t), z + 1)
  | "tuple" => do
    arity tag fs 1
    let parts ← (← asArr fs[0]! "tuple components").toList.mapM comp
    if parts.length < 2 then fail "tuple: fewer than two components"
    pure (.data (.tuple (Decode.tyList (parts.map (·.1)))), 1 + (parts.map (·.2)).foldl (· + ·) 0)
  | "view" => do
    arity tag fs 2
    let m ← decMut (← asStr fs[0]! "view mutability")
    let (t, z) ← comp fs[1]!
    pure (.view m t, z + 1)
  | _ => fail s!"unknown type tag {tag.quote}"

def decVTypes (j : Lean.Json) : Except String (Array VTy) := do
  let entries ← asArr j "types"
  let mut types : Array VTy := #[]
  let mut sizes : Array Nat := #[]
  for h : i in [0:entries.size] do
    let (t, z) ← match decVTypeEntry types sizes entries[i] with
      | .ok r => pure r
      | .error e => fail s!"type {i}: {e}"
    if z > Decode.maxTypeTreeSize then fail s!"type {i}: tree size over {Decode.maxTypeTreeSize}"
    types := types.push t
    sizes := sizes.push z
  pure types

def decVTy (tb : Tables) (j : Lean.Json) : Except String VTy := do
  let i ← checkIndex (← asNat j "type") tb.types.size "type"
  match tb.types[i]? with
  | some t => pure t
  | none => fail "type"

/-- A type index that must name a data type. -/
def decTy (tb : Tables) (j : Lean.Json) : Except String Ty := do
  match (← decVTy tb j) with
  | .data t => pure t
  | .view .. => fail "type: a view where a data type is required"

def decVal (j : Lean.Json) : Except String ValueId := asNat j "value"

def decVals (j : Lean.Json) (what : String) : Except String (List ValueId) :=
  list j what decVal

def decOrgOpt (tb : Tables) (j : Lean.Json) : Except String (Option OriginId) :=
  optional j "origin" fun x => do checkIndex (← asNat x "origin") tb.nOrigins "origin"

def decBlockRef (tb : Tables) (j : Lean.Json) : Except String BlockId := do
  checkIndex (← asNat j "block") tb.nBlocks "block"

def decBnd (j : Lean.Json) : Except String Bnd := do
  let (tag, fs) ← record j "bound"
  match tag with
  | "bd_none" => do arity tag fs 0; pure .omitted
  | "bd_val" => do arity tag fs 1; pure (.val (← decVal fs[0]!))
  | "bd_end" => do arity tag fs 1; pure (.fromEnd (← decVal fs[0]!))
  | _ => fail s!"unknown bound tag {tag.quote}"

def decPart (j : Lean.Json) : Except String PrintPart := do
  let (tag, fs) ← record j "print part"
  match tag with
  | "pp_text" => do arity tag fs 1; pure (.text (← asStr fs[0]! "pp_text"))
  | "pp_val" => do arity tag fs 1; pure (.val (← decVal fs[0]!))
  | _ => fail s!"unknown print part tag {tag.quote}"

def decInst (tb : Tables) (j : Lean.Json) : Except String Inst := do
  let (tag, fs) ← record j "instruction"
  let org (i : Nat) := decOrgOpt tb fs[i]!
  let v (i : Nat) := decVal fs[i]!
  let def_ (op : Op) : Except String Inst := do pure (.def (← v 0) op)
  match tag with
  | "i_int" => do
    arity tag fs 3
    match (← decTy tb fs[1]!) with
    | .int t =>
      let n ← asInt fs[2]! "i_int"
      Decode.intRange t n
      def_ (.constInt t n)
    | _ => fail "i_int: type is not an integer type"
  | "i_bool" => do arity tag fs 2; def_ (.constBool (← asFlag fs[1]! "i_bool"))
  | "i_unit" => do arity tag fs 1; def_ .constUnit
  | "i_bin" => do
    arity tag fs 6
    let op ← decBinOp (← asStr fs[1]! "i_bin operator")
    let t ← match (← decTy tb fs[2]!) with
      | .int t => pure t
      | _ => fail "i_bin: type is not an integer type"
    def_ (.bin op t (← v 3) (← v 4) (← org 5))
  | "i_un" => do
    arity tag fs 5
    let op ← decUnOp (← asStr fs[1]! "i_un operator")
    let t ← match (← decTy tb fs[2]!) with
      | .int t => pure t
      | _ => fail "i_un: type is not an integer type"
    def_ (.un op t (← v 3) (← org 4))
  | "i_cmp" => do
    arity tag fs 5
    let op ← decCmpOp (← asStr fs[1]! "i_cmp comparison")
    let t ← match (← decTy tb fs[2]!) with
      | .int t => pure t
      | _ => fail "i_cmp: type is not an integer type"
    def_ (.cmp op t (← v 3) (← v 4))
  | "i_bcmp" => do
    arity tag fs 4
    def_ (.boolCmp (← decCmpOp (← asStr fs[1]! "i_bcmp comparison")) (← v 2) (← v 3))
  | "i_not" => do arity tag fs 2; def_ (.boolNot (← v 1))
  | "i_conv" => do
    arity tag fs 6
    let k ← decConvKind (← asStr fs[1]! "i_conv kind")
    let src ← match (← decTy tb fs[2]!) with
      | .int t => pure t
      | _ => fail "i_conv: source type is not an integer type"
    let dst ← match (← decTy tb fs[3]!) with
      | .int t => pure t
      | _ => fail "i_conv: target type is not an integer type"
    def_ (.conv k src dst (← v 4) (← org 5))
  | "i_next" => do
    arity tag fs 3
    let t ← match (← decTy tb fs[1]!) with
      | .int t => pure t
      | _ => fail "i_next: type is not an integer type"
    def_ (.next t (← v 2))
  | "i_slot" => do
    arity tag fs 2
    def_ (.slotAddr (← checkIndex (← asNat fs[1]! "slot") tb.nSlots "slot"))
  | "i_global" => do
    arity tag fs 2
    def_ (.globalAddr (← checkIndex (← asNat fs[1]! "global") tb.nGlobals "global"))
  | "i_elem" => do arity tag fs 3; def_ (.refElem (← v 1) (← v 2))
  | "i_freeze" => do arity tag fs 2; def_ (.refFreeze (← v 1))
  | "i_load" => do arity tag fs 2; def_ (.load (← v 1))
  | "i_snap" => do arity tag fs 2; def_ (.snapshot (← v 1))
  | "i_sview" => do arity tag fs 2; def_ (.sliceView (← v 1))
  | "i_vlen" => do arity tag fs 2; def_ (.viewLen (← v 1))
  | "i_vslice" => do
    arity tag fs 6
    let m ← decMut (← asStr fs[1]! "i_vslice mutability")
    def_ (.viewSlice m (← v 2) (← decBnd fs[3]!) (← decBnd fs[4]!) (← org 5))
  | "i_alen" => do arity tag fs 2; def_ (.arrayLen (← v 1))
  | "i_index" => do arity tag fs 4; def_ (.indexChecked (← v 1) (← v 2) (← org 3))
  | "i_push" => do arity tag fs 4; def_ (.push (← v 1) (← v 2) (← org 3))
  | "i_call" => do
    arity tag fs 4
    let f ← checkIndex (← asNat fs[1]! "function") tb.nFuncs "function"
    def_ (.call f (← decVals fs[2]! "call arguments") (← org 3))
  | "i_arr" => do
    arity tag fs 3
    def_ (.arrLit (← decTy tb fs[1]!) (← decVals fs[2]! "array elements"))
  | "i_fill" => do
    arity tag fs 3
    def_ (.arrFill (← decTy tb fs[1]!) (← v 2))
  | "x_init" => do
    arity tag fs 3
    let s ← checkIndex (← asNat fs[0]! "slot") tb.nSlots "slot"
    pure (.eff (.slotInit s (← decVal fs[1]!) (← decOrgOpt tb fs[2]!)))
  | "x_store" => do
    arity tag fs 3
    pure (.eff (.store (← decVal fs[0]!) (← decVal fs[1]!) (← decOrgOpt tb fs[2]!)))
  | "x_append" => do
    arity tag fs 3
    pure (.eff (.append (← decVal fs[0]!) (← decVal fs[1]!) (← decOrgOpt tb fs[2]!)))
  | "x_enter" => do
    arity tag fs 1
    pure (.eff (.enter (← checkIndex (← asNat fs[0]! "scope") tb.nScopes "scope")))
  | "x_leave" => do
    arity tag fs 1
    pure (.eff (.leave (← checkIndex (← asNat fs[0]! "scope") tb.nScopes "scope")))
  | "x_print" => do
    arity tag fs 2
    pure (.eff (.print (← list fs[0]! "print parts" decPart) (← decOrgOpt tb fs[1]!)))
  | "t_br" => do
    arity tag fs 2
    pure (.term (.br (← decBlockRef tb fs[0]!) (← decVals fs[1]! "branch arguments")))
  | "t_condbr" => do
    arity tag fs 5
    pure (.term (.condbr (← decVal fs[0]!) (← decBlockRef tb fs[1]!) (← decVals fs[2]! "branch arguments")
      (← decBlockRef tb fs[3]!) (← decVals fs[4]! "branch arguments")))
  | "t_ret" => do
    arity tag fs 2
    pure (.term (.ret (← decVals fs[0]! "returned values") (← decOrgOpt tb fs[1]!)))
  | "t_abort" => do
    arity tag fs 2
    let ks ← asStr fs[0]! "t_abort kind"
    let some k := AbortKind.ofTag? ks | fail s!"unknown abort kind {ks.quote}"
    pure (.term (.abort k (← decOrgOpt tb fs[1]!)))
  | "t_exit" => do
    arity tag fs 2
    pure (.term (.exit (← decVal fs[0]!) (← decOrgOpt tb fs[1]!)))
  | _ => fail s!"unknown instruction tag {tag.quote}"

def decBParam (tb : Tables) (j : Lean.Json) : Except String (ValueId × VTy) := do
  let (tag, fs) ← record j "block parameter"
  unless tag == "bp" do fail s!"expected a block parameter, found tag {tag.quote}"
  arity tag fs 2
  pure (← decVal fs[0]!, ← decVTy tb fs[1]!)

def decBlock (tb : Tables) (j : Lean.Json) : Except String Block := do
  let (tag, fs) ← record j "block"
  unless tag == "block" do fail s!"expected a block, found tag {tag.quote}"
  arity tag fs 2
  pure { params := ← list fs[0]! "block parameters" (decBParam tb)
         insts := ← list fs[1]! "instructions" (decInst tb) }

def decSlot (tb : Tables) (j : Lean.Json) : Except String Slot := do
  let (tag, fs) ← record j "slot"
  unless tag == "slot" do fail s!"expected a slot, found tag {tag.quote}"
  arity tag fs 4
  pure { ty := ← decTy tb fs[0]!
         kind := ← decVarKind (← asStr fs[1]! "slot kind")
         scope := ← checkIndex (← asNat fs[2]! "slot scope") tb.nScopes "scope"
         var := ← asNat fs[3]! "slot variable" }

/-- A scope's parent, which must be an earlier scope. -/
def decScope (i : Nat) (nScopes : Nat) (j : Lean.Json) : Except String (Option ScopeId) := do
  let (tag, fs) ← record j "scope"
  unless tag == "scope" do fail s!"expected a scope, found tag {tag.quote}"
  arity tag fs 1
  let p ← optional fs[0]! "scope parent" fun x => do checkIndex (← asNat x "scope parent") nScopes "scope"
  match p with
  | some q => if q < i then pure p else fail s!"parent {q} is not an earlier scope"
  | none => pure none

/-- The instruction records a block record holds, as far as its shape shows. -/
def instCount : Lean.Json → Nat
  | Lean.Json.arr a =>
    match a[2]? with
    | some (Lean.Json.arr xs) => xs.size
    | _ => 0
  | _ => 0

def decFunc (m : Tables) (j : Lean.Json) : Except String Func := do
  let (tag, fs) ← record j "func"
  unless tag == "func" do fail s!"expected a func, found tag {tag.quote}"
  arity tag fs 8
  let name ← asStr fs[0]! "func name"
  let params ← list fs[1]! "func parameters" (decTy m)
  let results ← list fs[2]! "func results" (decTy m)
  let scopesJ ← asArr fs[4]! "func scopes"
  let blocksJ ← asArr fs[5]! "func blocks"
  let slotsJ ← asArr fs[3]! "func slots"
  let tb := { m with nSlots := slotsJ.size, nScopes := scopesJ.size, nBlocks := blocksJ.size }
  let scopes ← scopesJ.mapIdx (fun i s => Decode.inEntry "scope" i (decScope i scopesJ.size s)) |>.mapM id
  let slots ← slotsJ.mapIdx (fun i s => Decode.inEntry "slot" i (decSlot tb s)) |>.mapM id
  let nInsts := blocksJ.foldl (fun n b => n + instCount b) 0
  if nInsts > Decode.maxNodesPerFunction then
    fail s!"more than {Decode.maxNodesPerFunction} instructions in one function"
  let blocks ← blocksJ.mapIdx (fun i b => Decode.inEntry "block" i (decBlock tb b)) |>.mapM id
  let summary ← Decode.decSummary m.nGlobals params.length fs[6]!
  let org ← decOrgOpt tb fs[7]!
  pure { name, params, results, slots, scopes, blocks, summary, org }

def decGlobal (tb : Tables) (j : Lean.Json) : Except String Global := do
  let (tag, fs) ← record j "global"
  unless tag == "global" do fail s!"expected a global, found tag {tag.quote}"
  arity tag fs 5
  pure { name := ← asStr fs[0]! "global name"
         ty := ← decTy tb fs[1]!
         kind := ← decVarKind (← asStr fs[2]! "global kind")
         init := ← decFunc tb fs[3]!
         org := ← checkIndex (← asNat fs[4]! "global origin") tb.nOrigins "origin" }

def decodeModule (j : Lean.Json) : Except String Module := do
  let (tag, fs) ← record j "module"
  unless tag == "module" do fail s!"expected a module, found tag {tag.quote}"
  arity tag fs 8
  let schema ← asStr fs[0]! "schema"
  unless schema == schemaName do fail s!"schema {schema.quote}: this reader implements {schemaName.quote}"
  let profile ← asStr fs[1]! "profile"
  unless profile == profileName do fail s!"profile {profile.quote}: this reader implements {profileName.quote}"
  let files ← Decode.decodeMapped "file" fs[2]! Decode.decFile
  let origins ← Decode.decodeMapped "origin" fs[7]! (Decode.decOrigin files.size)
  let types ← decVTypes fs[3]!
  let nGlobals := (← asArr fs[4]! "globals").size
  let nFuncs := (← asArr fs[5]! "functions").size
  let tb : Tables := ⟨types, nGlobals, nFuncs, origins.size, 0, 0, 0⟩
  let globals ← Decode.decodeMapped "global" fs[4]! (decGlobal tb)
  let funcs ← Decode.decodeMapped "func" fs[5]! (decFunc tb)
  let entry ← checkIndex (← asNat fs[6]! "entry") nFuncs "function"
  pure { files, globals, funcs, entry, origins }

/-- Decode a module from the bytes of a file. -/
def decodeBytes (bs : ByteArray) : Except String Module := do
  Decode.scan bs
  let some text := String.fromUTF8? bs | fail "input is not valid UTF-8"
  match Lean.Json.parse text with
  | .error e => fail s!"JSON: {e}"
  | .ok j => decodeModule j

/-! ### Writer -/

/-- A JSON string literal with only the escapes the encoding allows. -/
def quote (s : String) : String :=
  let body := s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 then
      let h := Nat.toDigits 16 c.toNat
      acc ++ "\\u00" ++ String.ofList (List.replicate (2 - h.length) '0' ++ h)
    else acc.push c) ""
  "\"" ++ body ++ "\""

def intTyTag : IntTy → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"

def mutTag : Mutability → String
  | .mutable => "mut"
  | .readOnly => "const"

def kindTag : VarKind → String
  | .immutable => "let"
  | .mutable => "var"

def unTag : UnOp → String
  | .neg => "neg" | .bitnot => "bitnot"

def binTag : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .bitand => "bitand" | .bitor => "bitor" | .bitxor => "bitxor" | .shl => "shl" | .shr => "shr"

def cmpTag : CmpOp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"

def convTag : ConvKind → String
  | .widen => "widen" | .as => "as" | .asUnchecked => "as_unchecked"

/-- The type table under construction, in order of first mention. -/
structure TypeTable where
  entries : Array VTy := #[]

abbrev W := StateM TypeTable

/-- The index of an entry, adding it when it is new. Its components are already
present, so they have smaller indices. -/
def addEntry (t : VTy) : W Nat := do
  match (← get).entries.findIdx? (· == t) with
  | some i => pure i
  | none =>
    modify fun s => { s with entries := s.entries.push t }
    pure ((← get).entries.size - 1)

mutual
/-- The index of a data type, after the indices of its components. -/
def internTy : Ty → W Nat
  | .int t => addEntry (.data (.int t))
  | .bool => addEntry (.data .bool)
  | .unit => addEntry (.data .unit)
  | .arr e k => do
    let _ ← internTy e
    addEntry (.data (.arr e k))
  | .grow e => do
    let _ ← internTy e
    addEntry (.data (.grow e))
  | .ref m e => do
    let _ ← internTy e
    addEntry (.data (.ref m e))
  | .slice m e => do
    let _ ← internTy e
    addEntry (.data (.slice m e))
  | .tuple ps => do
    internParts ps
    addEntry (.data (.tuple ps))

def internParts : TyList → W Unit
  | .nil => pure ()
  | .cons h tl => do
    let _ ← internTy h
    internParts tl
end

def internVTy : VTy → W Nat
  | .data t => internTy t
  | .view m e => do
    let _ ← internTy e
    addEntry (.view m e)

def wTy (t : Ty) : W String := do pure (toString (← internTy t))

def wVTy (t : VTy) : W String := do pure (toString (← internVTy t))

def wRec (tag : String) (fields : List String) : String :=
  "[" ++ ",".intercalate (quote tag :: fields) ++ "]"

def wList (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def wMap (xs : List α) (f : α → W String) : W String := do
  pure (wList (← xs.mapM f))

def wOpt (o : Option Nat) : String :=
  match o with
  | some n => s!"[{n}]"
  | none => "[]"

def wNats (xs : List Nat) : String := wList (xs.map toString)

def wBnd : Bnd → String
  | .omitted => wRec "bd_none" []
  | .val v => wRec "bd_val" [toString v]
  | .fromEnd v => wRec "bd_end" [toString v]

def wPart : PrintPart → String
  | .text s => wRec "pp_text" [quote s]
  | .val v => wRec "pp_val" [toString v]

def wOp (r : ValueId) : Op → W String
  | .constInt t n => do pure (wRec "i_int" [toString r, ← wTy (.int t), quote (toString n)])
  | .constBool b => pure (wRec "i_bool" [toString r, if b then "1" else "0"])
  | .constUnit => pure (wRec "i_unit" [toString r])
  | .bin o t a b org => do
    pure (wRec "i_bin" [toString r, quote (binTag o), ← wTy (.int t), toString a, toString b, wOpt org])
  | .un o t a org => do
    pure (wRec "i_un" [toString r, quote (unTag o), ← wTy (.int t), toString a, wOpt org])
  | .cmp o t a b => do
    pure (wRec "i_cmp" [toString r, quote (cmpTag o), ← wTy (.int t), toString a, toString b])
  | .boolCmp o a b => pure (wRec "i_bcmp" [toString r, quote (cmpTag o), toString a, toString b])
  | .boolNot a => pure (wRec "i_not" [toString r, toString a])
  | .conv k src dst a org => do
    pure (wRec "i_conv" [toString r, quote (convTag k), ← wTy (.int src), ← wTy (.int dst),
      toString a, wOpt org])
  | .next t a => do pure (wRec "i_next" [toString r, ← wTy (.int t), toString a])
  | .slotAddr s => pure (wRec "i_slot" [toString r, toString s])
  | .globalAddr g => pure (wRec "i_global" [toString r, toString g])
  | .refElem v i => pure (wRec "i_elem" [toString r, toString v, toString i])
  | .refFreeze a => pure (wRec "i_freeze" [toString r, toString a])
  | .load a => pure (wRec "i_load" [toString r, toString a])
  | .snapshot a => pure (wRec "i_snap" [toString r, toString a])
  | .sliceView a => pure (wRec "i_sview" [toString r, toString a])
  | .viewLen a => pure (wRec "i_vlen" [toString r, toString a])
  | .viewSlice m v lo hi org =>
    pure (wRec "i_vslice" [toString r, quote (mutTag m), toString v, wBnd lo, wBnd hi, wOpt org])
  | .arrayLen a => pure (wRec "i_alen" [toString r, toString a])
  | .indexChecked v i org => pure (wRec "i_index" [toString r, toString v, toString i, wOpt org])
  | .push a v org => pure (wRec "i_push" [toString r, toString a, toString v, wOpt org])
  | .call f args org => pure (wRec "i_call" [toString r, toString f, wNats args, wOpt org])
  | .arrLit t vs => do pure (wRec "i_arr" [toString r, ← wTy t, wNats vs])
  | .arrFill t v => do pure (wRec "i_fill" [toString r, ← wTy t, toString v])

def wInst : Inst → W String
  | .def r op => wOp r op
  | .eff (.slotInit s v org) => pure (wRec "x_init" [toString s, toString v, wOpt org])
  | .eff (.store r v org) => pure (wRec "x_store" [toString r, toString v, wOpt org])
  | .eff (.append r v org) => pure (wRec "x_append" [toString r, toString v, wOpt org])
  | .eff (.enter sc) => pure (wRec "x_enter" [toString sc])
  | .eff (.leave sc) => pure (wRec "x_leave" [toString sc])
  | .eff (.print parts org) => pure (wRec "x_print" [wList (parts.map wPart), wOpt org])
  | .term (.br b args) => pure (wRec "t_br" [toString b, wNats args])
  | .term (.condbr c t ta e ea) => pure (wRec "t_condbr" [toString c, toString t, wNats ta, toString e, wNats ea])
  | .term (.ret vs org) => pure (wRec "t_ret" [wNats vs, wOpt org])
  | .term (.abort k org) => pure (wRec "t_abort" [quote k.tag, wOpt org])
  | .term (.exit v org) => pure (wRec "t_exit" [toString v, wOpt org])

def wBlock (b : Block) : W String := do
  let ps ← wMap b.params fun (v, t) => do pure (wRec "bp" [toString v, ← wVTy t])
  let is ← wMap b.insts wInst
  pure (wRec "block" [ps, is])

def wTarget : Target → String
  | .param i => wRec "t_param" [toString i]
  | .global g => wRec "t_global" [toString g]

def wSummary : SummaryAnn → String
  | .unknown => wRec "summary_unknown" []
  | .known s =>
    wRec "summary" [wList (s.reads.map wTarget), wList (s.writes.map wTarget),
      wList (s.grows.map wTarget), wList (s.rebinds.map wTarget),
      if s.aborts then "1" else "0", if s.outputs then "1" else "0"]

def wFunc (f : Func) : W String := do
  let ps ← wMap f.params wTy
  let rs ← wMap f.results wTy
  let slots ← wMap f.slots.toList fun sl => do
    pure (wRec "slot" [← wTy sl.ty, quote (kindTag sl.kind), toString sl.scope, toString sl.var])
  let scopes := wList (f.scopes.toList.map fun p => wRec "scope" [wOpt p])
  let blocks ← wMap f.blocks.toList wBlock
  pure (wRec "func" [quote f.name, ps, rs, slots, scopes, blocks, wSummary f.summary, wOpt f.org])

def wGlobal (g : Global) : W String := do
  let t ← wTy g.ty
  let init ← wFunc g.init
  pure (wRec "global" [quote g.name, t, quote (kindTag g.kind), init, toString g.org])

/-- The type table as written: the index of every component is smaller. -/
def wTypeEntry (tab : Array VTy) (t : VTy) : String :=
  let ix (e : Ty) : String := toString ((tab.findIdx? (· == VTy.data e)).getD 0)
  match t with
  | .data (.int i) => wRec "int" [quote (intTyTag i)]
  | .data .bool => wRec "bool" []
  | .data .unit => wRec "unit" []
  | .data (.arr e k) => wRec "arr" [ix e, toString k]
  | .data (.grow e) => wRec "grow" [ix e]
  | .data (.ref m e) => wRec "ref" [quote (mutTag m), ix e]
  | .data (.slice m e) => wRec "slice" [quote (mutTag m), ix e]
  | .data (.tuple ps) =>
    let rec parts : TyList → List String
      | .nil => []
      | .cons h tl => ix h :: parts tl
    wRec "tuple" [wList (parts ps)]
  | .view m e => wRec "view" [quote (mutTag m), ix e]

/-- The module in the wire encoding, with the terminating line feed. -/
def write (m : Module) : String :=
  let ((globals, funcs), tab) := (do
    let gs ← wMap m.globals.toList wGlobal
    let fs ← wMap m.funcs.toList wFunc
    pure (gs, fs) : W (String × String)).run {}
  let files := wList (m.files.toList.map fun f => wRec "file" [quote f])
  let origins := wList (m.origins.toList.map fun o =>
    wRec "origin" [toString o.file, toString o.line, quote o.kind])
  let types := wList (tab.entries.toList.map (wTypeEntry tab.entries))
  wRec "module" [quote schemaName, quote profileName, files, types, globals, funcs,
    toString m.entry, origins] ++ "\n"

end Goose.GIR.Json
