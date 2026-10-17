import Goose.Core.Json
import Goose.GIR.Syntax

/-!
The `gir-h/0.4` encoding: a strict decoder and the deterministic writer.

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

def schemaName : String := "gir-h/0.4"
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
  profile : ArtifactProfile := .pilot

/-- Resolve field components against earlier data types. Views are valid table
entries but can never become a descriptor's stored field type. -/
def resolveStruct (types : Array VTy) (sizes : Array Nat) (raw : Decode.RawStructDef) :
    Except String (StructDef × Nat) := do
  let mut fields := #[]
  let mut treeSize := 1
  for f in raw.fields do
    let i ← checkIndex f.typeIndex types.size "struct field type component"
    let some (.data t) := types[i]? | fail "struct field type must be an earlier data type"
    let some z := sizes[i]? | fail "struct field type size"
    fields := fields.push ⟨t, f.binding, f.contents, f.byteOffset⟩
    treeSize := treeSize + z
  pure ({ byteSize := raw.byteSize, fields }, treeSize)

def decVTypeEntry (types : Array VTy) (sizes : Array Nat) (j : Lean.Json)
    (structs : Array Decode.RawStructDef := #[]) (profile : ArtifactProfile := .pilot) : Except String (VTy × Nat) := do
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
  | "growshrink" => do
    unless profile == .shrink do fail "growshrink requires core-shrink"
    arity tag fs 1
    let (t, z) ← comp fs[0]!
    pure (.data (.growshrink t), z + 1)
  | "limited" => do
    unless profile == .shrink do fail "limited requires core-shrink"
    arity tag fs 2
    let (t, z) ← comp fs[0]!
    let capacity ← asNat fs[1]! "limited capacity"
    if capacity == 0 then fail "limited capacity must be positive"
    if capacity > 2^31 - 1 then fail "limited capacity exceeds the wire limit"
    pure (.data (.limited t capacity), z + 1)
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
  | "struct" => do
    arity tag fs 1
    let sid ← checkIndex (← asNat fs[0]! "struct id") structs.size "struct"
    let some raw := structs[sid]? | fail "struct id"
    let (d, z) ← resolveStruct types sizes raw
    pure (.data (.structT sid (TyList.ofList (d.fields.toList.map (·.ty)))), z)
  | "view" => do
    arity tag fs 2
    let m ← decMut (← asStr fs[0]! "view mutability")
    let (t, z) ← comp fs[1]!
    pure (.view m t, z + 1)
  | _ => fail s!"unknown type tag {tag.quote}"

def decVTypesWithStructs (j : Lean.Json) (raw : Array Decode.RawStructDef)
    (profile : ArtifactProfile := .pilot) : Except String (Array VTy × Array StructDef) := do
  let entries ← asArr j "types"
  let mut types : Array VTy := #[]
  let mut sizes : Array Nat := #[]
  let mut definitions : Array (Option StructDef) := Array.replicate raw.size none
  for h : i in [0:entries.size] do
    let (t, z) ← match decVTypeEntry types sizes entries[i] raw profile with
      | .ok r => pure r
      | .error e => fail s!"type {i}: {e}"
    if z > Decode.maxTypeTreeSize then fail s!"type {i}: tree size over {Decode.maxTypeTreeSize}"
    match t with
    | .data (.structT sid _) =>
      if (definitions[sid]?).any (·.isSome) then fail "a struct descriptor has more than one type entry"
      let some d := raw[sid]? | fail "struct id"
      let (resolved, _) ← resolveStruct types sizes d
      definitions := definitions.set! sid (some resolved)
    | _ => pure ()
    types := types.push t
    sizes := sizes.push z
  let structs ← definitions.mapM fun
    | some d => pure d
    | none => fail "a struct descriptor has no type entry"
  pure (types, structs)

def decVTypes (j : Lean.Json) : Except String (Array VTy) := do
  pure (← decVTypesWithStructs j #[]).1

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

def decRootRef (tb : Tables) (nParams : Nat) (j : Lean.Json) : Except String RootRef := do
  let (tag, fs) ← record j "root reference"
  arity tag fs 1
  let i ← asNat fs[0]! "root reference index"
  match tag with
  | "r_local" => pure (.local (← checkIndex i tb.nSlots "slot"))
  | "r_global" => pure (.global (← checkIndex i tb.nGlobals "global"))
  | "r_param" => pure (.param (← checkIndex i nParams "parameter"))
  | _ => fail s!"unknown root reference tag {tag.quote}"

def decRootRows (tb : Tables) (nParams nRows : Nat) (rowKind expectedTag : String) (j : Lean.Json) :
    Except String (Array (Nat × List RootRef)) := do
  let rows ← (← asArr j "root rows").mapM fun row => do
    let (tag, fs) ← record row "root row"
    unless tag == expectedTag do fail s!"expected {expectedTag}, found tag {tag.quote}"
    arity tag fs 2
    let i ← checkIndex (← asNat fs[0]! s!"root row {rowKind}") nRows rowKind
    let roots ← list fs[1]! "root set" (decRootRef tb nParams)
    pure (i, roots)
  let rec distinct : List (Nat × List RootRef) → Bool
    | [] => true
    | (i, _) :: rest => !(rest.any (·.1 == i)) && distinct rest
  unless distinct rows.toList do fail s!"{expectedTag} rows repeat a {rowKind}"
  pure rows

def decRootInfo (tb : Tables) (nParams nResults : Nat) (j : Lean.Json) : Except String RootInfo := do
  let (tag, fs) ← record j "root info"
  unless tag == "roots" do fail s!"expected roots, found tag {tag.quote}"
  unless fs.size == 3 || fs.size == 4 do fail "roots expects 3 or 4 fields"
  let params ← decRootRows tb nParams nParams "parameter" "vr" fs[0]!
  let contents ← decRootRows tb nParams nParams "parameter" "cr" fs[1]!
  let results ← list fs[2]! "result root rows" (fun row => list row "root set" (decRootRef tb nParams))
  unless results.length == nResults do fail s!"root info has {results.length} result rows, expected {nResults}"
  let slots ← if fs.size == 4 then
      some <$> decRootRows tb nParams tb.nSlots "slot" "sr" fs[3]!
    else pure none
  pure { params, contents, results := results.toArray, slots }

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
  | "i_owner_borrow" => do arity tag fs 2; def_ (.ownerBorrow (← v 1))
  | "i_load" => do arity tag fs 2; def_ (.load (← v 1))
  | "i_snap" => do
    arity tag fs 3
    let mode ← asStr fs[1]! "i_snap mode"
    let some mode := match mode with | "owner" => some .owner | "borrowed" => some .borrowed | _ => none
      | fail s!"unknown snapshot mode {mode.quote}"
    def_ (.snapshot mode (← v 2))
  | "i_sview" => do arity tag fs 2; def_ (.sliceView (← v 1))
  | "i_vlen" => do arity tag fs 2; def_ (.viewLen (← v 1))
  | "i_vslice" => do
    arity tag fs 6
    let m ← decMut (← asStr fs[1]! "i_vslice mutability")
    def_ (.viewSlice m (← v 2) (← decBnd fs[3]!) (← decBnd fs[4]!) (← org 5))
  | "i_alen" => do arity tag fs 2; def_ (.arrayLen (← v 1))
  | "i_index" => do arity tag fs 4; def_ (.indexChecked (← v 1) (← v 2) (← org 3))
  | "i_index_proven" => do arity tag fs 3; def_ (.indexProven (← v 1) (← v 2))
  | "i_push" => do arity tag fs 4; def_ (.push (← v 1) (← v 2) (← org 3))
  | "i_pop" => do
    unless tb.profile == .shrink do fail "i_pop requires core-shrink"
    arity tag fs 3
    def_ (.pop (← v 1) (← org 2))
  | "i_call" => do
    arity tag fs 4
    let f ← checkIndex (← asNat fs[1]! "function") tb.nFuncs "function"
    def_ (.call f (← decVals fs[2]! "call arguments") (← org 3))
  | "i_struct" => do
    unless tb.profile == .shrink do fail "i_struct requires core-shrink"
    arity tag fs 3
    def_ (.structLit (← decTy tb fs[1]!) (← decVals fs[2]! "struct initializers"))
  | "i_field" => do
    unless tb.profile == .shrink do fail "i_field requires core-shrink"
    arity tag fs 3
    def_ (.fieldAddr (← v 1) (← asNat fs[2]! "field index"))
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
  | "x_pop_n" => do
    unless tb.profile == .shrink do fail "x_pop_n requires core-shrink"
    arity tag fs 3
    pure (.eff (.popN (← decVal fs[0]!) (← decVal fs[1]!) (← decOrgOpt tb fs[2]!)))
  | "x_resize" => do
    unless tb.profile == .shrink do fail "x_resize requires core-shrink"
    arity tag fs 4
    pure (.eff (.resize (← decVal fs[0]!) (← decVal fs[1]!)
      (← optional fs[2]! "resize fill" decVal) (← decOrgOpt tb fs[3]!)))
  | "x_clear" => do
    unless tb.profile == .shrink do fail "x_clear requires core-shrink"
    arity tag fs 2
    pure (.eff (.clear (← decVal fs[0]!) (← decOrgOpt tb fs[1]!)))
  | "x_replace" => do
    unless tb.profile == .shrink do fail "x_replace requires core-shrink"
    arity tag fs 3
    pure (.eff (.replace (← decVal fs[0]!) (← decVal fs[1]!) (← decOrgOpt tb fs[2]!)))
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
    if tb.profile != .shrink && k ∈ [.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] then
      fail s!"abort kind {ks.quote} requires core-shrink"
    pure (.term (.abort k (← decOrgOpt tb fs[1]!)))
  | "t_exit" => do
    arity tag fs 2
    pure (.term (.exit (← decVal fs[0]!) (← decOrgOpt tb fs[1]!)))
  | "t_unreachable" => do arity tag fs 0; pure (.term .unreachable)
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

def decFact (_tb : Tables) (j : Lean.Json) : Except String Fact := do
  let (tag, fs) ← record j "fact"
  match tag with
  | "f_ge0" => do arity tag fs 1; pure (.ge0 (← asNat fs[0]! "fact value"))
  | "f_lt" => do
    arity tag fs 2
    pure (.lt (← asNat fs[0]! "fact value") (← asNat fs[1]! "fact bound"))
  | "f_len_ge" => do
    arity tag fs 2
    pure (.lenGe (← asNat fs[0]! "fact reference") (← asNat fs[1]! "fact bound"))
  | "f_view_len_ge" => do
    arity tag fs 2
    pure (.viewLenGe (← asNat fs[0]! "fact view") (← asNat fs[1]! "fact bound"))
  | _ => fail s!"unknown fact tag {tag.quote}"

def decCertificate (tb : Tables) (j : Lean.Json) : Except String FactCertificate := do
  let (tag, fs) ← record j "certificate"
  unless tag == "certificate" do fail s!"expected a certificate, found tag {tag.quote}"
  arity tag fs 1
  let sets ← asArr fs[0]! "certificate block sets"
  sets.mapM fun facts => list facts "block facts" (decFact tb)

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
  arity tag fs 10
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
  let roots ← decRootInfo tb params.length results.length fs[6]!
  let summary ← Decode.decSummary m.profile m.nGlobals params.length fs[7]!
  let org ← decOrgOpt tb fs[8]!
  let certificate ← optional fs[9]! "fact certificate" (decCertificate tb)
  pure { name, params, results, slots, scopes, blocks, roots, summary, org, certificate }

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
  if fs.size < 2 then fail "module: missing schema or profile"
  let schema ← asStr fs[0]! "schema"
  unless schema == schemaName do fail s!"schema {schema.quote}: this reader implements {schemaName.quote}"
  let profileTag ← asStr fs[1]! "profile"
  let some profile := ArtifactProfile.ofTag? profileTag | fail s!"unknown profile {profileTag.quote}"
  let extra := if profile == .shrink then 1 else 0
  arity tag fs (8 + extra)
  let files ← Decode.decodeMapped "file" fs[2]! Decode.decFile
  let origins ← Decode.decodeMapped "origin" fs[7 + extra]! (Decode.decOrigin files.size)
  let raw ← if profile == .shrink then Decode.decStructDefs fs[4]! else pure #[]
  let (types, structs) ← decVTypesWithStructs fs[3]! raw profile
  let nGlobals := (← asArr fs[4 + extra]! "globals").size
  let nFuncs := (← asArr fs[5 + extra]! "functions").size
  let tb : Tables := ⟨types, nGlobals, nFuncs, origins.size, 0, 0, 0, profile⟩
  let globals ← Decode.decodeMapped "global" fs[4 + extra]! (decGlobal tb)
  let funcs ← Decode.decodeMapped "func" fs[5 + extra]! (decFunc tb)
  let entry ← checkIndex (← asNat fs[6 + extra]! "entry") nFuncs "function"
  pure { files, globals, funcs, entry, origins, profile, structs }

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
  | .structT sid fs => do
    internParts fs
    addEntry (.data (.structT sid fs))
  | .int t => addEntry (.data (.int t))
  | .bool => addEntry (.data .bool)
  | .unit => addEntry (.data .unit)
  | .arr e k => do
    let _ ← internTy e
    addEntry (.data (.arr e k))
  | .grow e => do
    let _ ← internTy e
    addEntry (.data (.grow e))
  | .growshrink e => do
    let _ ← internTy e
    addEntry (.data (.growshrink e))
  | .limited e k => do
    let _ ← internTy e
    addEntry (.data (.limited e k))
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
  | .ownerBorrow a => pure (wRec "i_owner_borrow" [toString r, toString a])
  | .load a => pure (wRec "i_load" [toString r, toString a])
  | .snapshot mode a => pure (wRec "i_snap" [toString r, quote (if mode == .owner then "owner" else "borrowed"), toString a])
  | .sliceView a => pure (wRec "i_sview" [toString r, toString a])
  | .viewLen a => pure (wRec "i_vlen" [toString r, toString a])
  | .viewSlice m v lo hi org =>
    pure (wRec "i_vslice" [toString r, quote (mutTag m), toString v, wBnd lo, wBnd hi, wOpt org])
  | .arrayLen a => pure (wRec "i_alen" [toString r, toString a])
  | .indexChecked v i org => pure (wRec "i_index" [toString r, toString v, toString i, wOpt org])
  | .indexProven v i => pure (wRec "i_index_proven" [toString r, toString v, toString i])
  | .push a v org => pure (wRec "i_push" [toString r, toString a, toString v, wOpt org])
  | .pop a org => pure (wRec "i_pop" [toString r, toString a, wOpt org])
  | .call f args org => pure (wRec "i_call" [toString r, toString f, wNats args, wOpt org])
  | .structLit t vs => do pure (wRec "i_struct" [toString r, ← wTy t, wNats vs])
  | .fieldAddr owner i => pure (wRec "i_field" [toString r, toString owner, toString i])
  | .arrLit t vs => do pure (wRec "i_arr" [toString r, ← wTy t, wNats vs])
  | .arrFill t v => do pure (wRec "i_fill" [toString r, ← wTy t, toString v])

def wInst : Inst → W String
  | .def r op => wOp r op
  | .eff (.slotInit s v org) => pure (wRec "x_init" [toString s, toString v, wOpt org])
  | .eff (.store r v org) => pure (wRec "x_store" [toString r, toString v, wOpt org])
  | .eff (.append r v org) => pure (wRec "x_append" [toString r, toString v, wOpt org])
  | .eff (.popN r n org) => pure (wRec "x_pop_n" [toString r, toString n, wOpt org])
  | .eff (.resize r n fill org) => pure (wRec "x_resize" [toString r, toString n, wOpt fill, wOpt org])
  | .eff (.clear r org) => pure (wRec "x_clear" [toString r, wOpt org])
  | .eff (.replace r run org) => pure (wRec "x_replace" [toString r, toString run, wOpt org])
  | .eff (.enter sc) => pure (wRec "x_enter" [toString sc])
  | .eff (.leave sc) => pure (wRec "x_leave" [toString sc])
  | .eff (.print parts org) => pure (wRec "x_print" [wList (parts.map wPart), wOpt org])
  | .term (.br b args) => pure (wRec "t_br" [toString b, wNats args])
  | .term (.condbr c t ta e ea) => pure (wRec "t_condbr" [toString c, toString t, wNats ta, toString e, wNats ea])
  | .term (.ret vs org) => pure (wRec "t_ret" [wNats vs, wOpt org])
  | .term (.abort k org) => pure (wRec "t_abort" [quote k.tag, wOpt org])
  | .term (.exit v org) => pure (wRec "t_exit" [toString v, wOpt org])
  | .term .unreachable => pure (wRec "t_unreachable" [])

def wBlock (b : Block) : W String := do
  let ps ← wMap b.params fun (v, t) => do pure (wRec "bp" [toString v, ← wVTy t])
  let is ← wMap b.insts wInst
  pure (wRec "block" [ps, is])

def wTarget : Target → String
  | .param i => wRec "t_param" [toString i]
  | .global g => wRec "t_global" [toString g]

def wRootRef : RootRef → String
  | .local x => wRec "r_local" [toString x]
  | .global g => wRec "r_global" [toString g]
  | .param i => wRec "r_param" [toString i]

def wRootInfo (r : RootInfo) : String :=
  let rows tag rs := wList (rs.toList.map fun (i, roots) => wRec tag [toString i, wList (roots.map wRootRef)])
  let fields := [rows "vr" r.params, rows "cr" r.contents,
    wList (r.results.toList.map fun roots => wList (roots.map wRootRef))]
  wRec "roots" (match r.slots with
    | none => fields
    | some slots => fields ++ [rows "sr" slots])

def wSummary (profile : ArtifactProfile) : SummaryAnn → String
  | .unknown => wRec "summary_unknown" []
  | .known s =>
    wRec "summary" ([wList (s.reads.map wTarget), wList (s.writes.map wTarget),
      wList (s.grows.map wTarget)] ++
      (if profile == .shrink then [wList (s.shrinks.map wTarget)] else []) ++
      [wList (s.rebinds.map wTarget), if s.aborts then "1" else "0", if s.outputs then "1" else "0"])

def wFact : Fact → String
  | .ge0 i => wRec "f_ge0" [toString i]
  | .lt i n => wRec "f_lt" [toString i, toString n]
  | .lenGe reference n => wRec "f_len_ge" [toString reference, toString n]
  | .viewLenGe v n => wRec "f_view_len_ge" [toString v, toString n]

def wCertificate (certificate : FactCertificate) : String :=
  wRec "certificate" [wList (certificate.toList.map fun facts => wList (facts.map wFact))]

def wFunc (profile : ArtifactProfile) (f : Func) : W String := do
  let ps ← wMap f.params wTy
  let rs ← wMap f.results wTy
  let slots ← wMap f.slots.toList fun sl => do
    pure (wRec "slot" [← wTy sl.ty, quote (kindTag sl.kind), toString sl.scope, toString sl.var])
  let scopes := wList (f.scopes.toList.map fun p => wRec "scope" [wOpt p])
  let blocks ← wMap f.blocks.toList wBlock
  let certificate := match f.certificate with | some c => wList [wCertificate c] | none => "[]"
  pure (wRec "func" [quote f.name, ps, rs, slots, scopes, blocks, wRootInfo f.roots,
    wSummary profile f.summary, wOpt f.org, certificate])

def wGlobal (profile : ArtifactProfile) (g : Global) : W String := do
  let t ← wTy g.ty
  let init ← wFunc profile g.init
  pure (wRec "global" [quote g.name, t, quote (kindTag g.kind), init, toString g.org])

/-- The type table as written: the index of every component is smaller. -/
def wTypeEntry (tab : Array VTy) (t : VTy) : String :=
  let ix (e : Ty) : String := toString ((tab.findIdx? (· == VTy.data e)).getD 0)
  match t with
  | .data (.structT sid _) => wRec "struct" [toString sid]
  | .data (.int i) => wRec "int" [quote (intTyTag i)]
  | .data .bool => wRec "bool" []
  | .data .unit => wRec "unit" []
  | .data (.arr e k) => wRec "arr" [ix e, toString k]
  | .data (.grow e) => wRec "grow" [ix e]
  | .data (.growshrink e) => wRec "growshrink" [ix e]
  | .data (.limited e k) => wRec "limited" [ix e, toString k]
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
    if m.profile == .shrink then
      for h : sid in [0:m.structs.size] do
        let _ ← internTy (.structT sid (TyList.ofList (m.structs[sid].fields.toList.map (·.ty))))
    let gs ← wMap m.globals.toList (wGlobal m.profile)
    let fs ← wMap m.funcs.toList (wFunc m.profile)
    pure (gs, fs) : W (String × String)).run {}
  let files := wList (m.files.toList.map fun f => wRec "file" [quote f])
  let origins := wList (m.origins.toList.map fun o =>
    wRec "origin" [toString o.file, toString o.line, quote o.kind])
  let types := wList (tab.entries.toList.map (wTypeEntry tab.entries))
  let structs := wList (m.structs.toList.map fun d =>
    wRec "struct_def" [toString d.byteSize, wList (d.fields.toList.map fun f =>
      wRec "field" [toString ((tab.entries.findIdx? (· == .data f.ty)).getD 0),
        quote (kindTag f.binding), quote (mutTag f.contents), toString f.byteOffset])])
  wRec "module" ([quote schemaName, quote m.profile.tag, files, types] ++
    (if m.profile == .shrink then [structs] else []) ++
    [globals, funcs, toString m.entry, origins]) ++ "\n"

end Goose.GIR.Json
