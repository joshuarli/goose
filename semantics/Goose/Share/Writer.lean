import Goose.Core.Syntax

/-!
A writer for the Core module encoding that `Goose.Core.Decode` reads.

Every record is a JSON array led by its tag, with no whitespace. Types are
resolved trees inside a decoded module, so a type is written as the index of
its first equal entry in the type table; the table itself is written entry by
entry with components referring to earlier entries. A type missing from the
table is written with an index past the table's end, which the decoder
rejects, so a module that did not come from a decoder fails loudly instead of
being written wrongly.
-/

namespace Goose.Share.Write

open Goose.Core

/-- A JSON string: only `"`, `\` and the control characters are escaped, the
latter as lower-case `\u00xx`. -/
def str (s : String) : String := Id.run do
  let hex (d : Nat) : Char := Char.ofNat (if d < 10 then 48 + d else 87 + d)
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c.toNat < 0x20 then
      out := out ++ "\\u00" ++ (hex (c.toNat / 16)).toString ++ (hex (c.toNat % 16)).toString
    else out := out.push c
  return out.push '"'

def arr (parts : List String) : String := "[" ++ ",".intercalate parts ++ "]"

def rec (tag : String) (fields : List String) : String := arr (str tag :: fields)

def nat (n : Nat) : String := toString n

def flag (b : Bool) : String := if b then "1" else "0"

def intTy : IntTy → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"

def mutability : Mutability → String
  | .mutable => "mut"
  | .readOnly => "const"

def varKind : VarKind → String
  | .immutable => "let"
  | .mutable => "var"

def mode : Mode → String
  | .byValue => "by_value"
  | .byRef => "by_ref"

def unOp : UnOp → String
  | .neg => "neg" | .bitnot => "bitnot"

def binOp : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .bitand => "bitand" | .bitor => "bitor" | .bitxor => "bitxor"
  | .shl => "shl" | .shr => "shr"

def cmpOp : CmpOp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"

def convKind : ConvKind → String
  | .widen => "widen" | .as => "as" | .asUnchecked => "as_unchecked"

def tyParts : TyList → List Ty
  | .nil => []
  | .cons t ts => t :: tyParts ts

/-- The index of a type in the table: the first equal entry. -/
def tyIndex (types : Array Ty) (t : Ty) : Nat :=
  (types.findIdx? (· == t)).getD types.size

/-- Write a type-table entry; components are indices of earlier entries. -/
def tyEntry (types : Array Ty) : Ty → String
  | .int t => rec "int" [str (intTy t)]
  | .bool => rec "bool" []
  | .unit => rec "unit" []
  | .arr e k => rec "arr" [nat (tyIndex types e), nat k]
  | .grow e => rec "grow" [nat (tyIndex types e)]
  | .ref m t => rec "ref" [str (mutability m), nat (tyIndex types t)]
  | .slice m e => rec "slice" [str (mutability m), nat (tyIndex types e)]
  | .tuple ps => rec "tuple" [arr ((tyParts ps).map fun t => nat (tyIndex types t))]

mutual
def place (ty : Ty → Nat) : Place → String
  | .var x => rec "p_local" [nat x]
  | .global g => rec "p_global" [nat g]
  | .deref e => rec "p_deref" [expr ty e]
  | .elem v i o => rec "p_elem" [view ty v, expr ty i, nat o]

def view (ty : Ty → Nat) : View → String
  | .of p => rec "v_of" [place ty p]
  | .val e => rec "v_val" [expr ty e]

def bound (ty : Ty → Nat) : Bound → String
  | .expr e => rec "b_expr" [expr ty e]
  | .fromEnd e => rec "b_end" [expr ty e]
  | .omitted => rec "b_none" []

def expr (ty : Ty → Nat) : Expr → String
  | .lit t n => rec "e_lit" [nat (ty (.int t)), str (toString n)]
  | .bool b => rec "e_bool" [flag b]
  | .read p => rec "e_read" [place ty p]
  | .ref m p => rec "e_ref" [str (mutability m), place ty p]
  | .slice m v lo hi o =>
    rec "e_slice" [str (mutability m), view ty v, bound ty lo, bound ty hi, nat o]
  | .len v => rec "e_len" [view ty v]
  | .un op e o => rec "e_un" [str (unOp op), expr ty e, nat o]
  | .bin op a b o => rec "e_bin" [str (binOp op), expr ty a, expr ty b, nat o]
  | .cmp op a b => rec "e_cmp" [str (cmpOp op), expr ty a, expr ty b]
  | .and a b => rec "e_and" [expr ty a, expr ty b]
  | .or a b => rec "e_or" [expr ty a, expr ty b]
  | .not e => rec "e_not" [expr ty e]
  | .conv k t e o => rec "e_conv" [str (convKind k), nat (ty t), expr ty e, nat o]
  | .call c args o => rec "e_call" [nat c, arr (args' ty args), nat o]
  | .push p e => rec "e_push" [place ty p, expr ty e]
  | .ifE c t f => rec "e_if" [expr ty c, block ty t, block ty f]
  | .blockE b => rec "e_block" [block ty b]
  | .arrLit t es => rec "e_arr" [nat (ty t), arr (exprs ty es)]
  | .fill t e => rec "e_fill" [nat (ty t), expr ty e]

def exprs (ty : Ty → Nat) : List Expr → List String
  | [] => []
  | e :: es => expr ty e :: exprs ty es

def arg (ty : Ty → Nat) : Arg → String
  | .byVal e => rec "a_val" [expr ty e]
  | .byRef m p => rec "a_ref" [str (mutability m), place ty p]

def args' (ty : Ty → Nat) : List Arg → List String
  | [] => []
  | a :: as => arg ty a :: args' ty as

def optExpr (ty : Ty → Nat) : Option Expr → List String
  | none => []
  | some e => [expr ty e]

def block (ty : Ty → Nat) : Block → String
  | .mk s ss v => rec "block" [nat s, arr (stmts ty ss), arr (optExpr ty v)]

def optBlock (ty : Ty → Nat) : Option Block → List String
  | none => []
  | some b => [block ty b]

def printArg (ty : Ty → Nat) : PrintArg → String
  | .text s => rec "pa_text" [str s]
  | .expr e => rec "pa_expr" [expr ty e]

def printArgs (ty : Ty → Nat) : List PrintArg → List String
  | [] => []
  | a :: as => printArg ty a :: printArgs ty as

def stmt (ty : Ty → Nat) : Stmt → String
  | .letS x e o => rec "s_let" [nat x, expr ty e, nat o]
  | .assign p e o => rec "s_assign" [place ty p, expr ty e, nat o]
  | .assignOp op p e o => rec "s_assign_op" [str (binOp op), place ty p, expr ty e, nat o]
  | .rebind x e o => rec "s_rebind" [nat x, expr ty e, nat o]
  | .expr e o => rec "s_expr" [expr ty e, nat o]
  | .append p v o => rec "s_append" [place ty p, view ty v, nat o]
  | .ifS c t f o => rec "s_if" [expr ty c, block ty t, arr (optBlock ty f), nat o]
  | .while c b o => rec "s_while" [expr ty c, block ty b, nat o]
  | .forRange x lo hi b o =>
    rec "s_for_range" [nat x, expr ty lo, expr ty hi, block ty b, nat o]
  | .forEach x i v byRef b o =>
    rec "s_for_each" [nat x, arr (i.toList.map nat), view ty v, flag byRef, block ty b, nat o]
  | .ret e o => rec "s_ret" [arr (optExpr ty e), nat o]
  | .brk o => rec "s_break" [nat o]
  | .cont o => rec "s_continue" [nat o]
  | .print as o => rec "s_print" [arr (printArgs ty as), nat o]
  | .assertS e o => rec "s_assert" [expr ty e, nat o]
  | .abort msg o => rec "s_abort" [str msg, nat o]
  | .exit e o => rec "s_exit" [expr ty e, nat o]

def stmts (ty : Ty → Nat) : List Stmt → List String
  | [] => []
  | s :: ss => stmt ty s :: stmts ty ss
end

def target : Target → String
  | .param i => rec "t_param" [nat i]
  | .global g => rec "t_global" [nat g]

def summary : SummaryAnn → String
  | .unknown => rec "summary_unknown" []
  | .known s =>
    rec "summary" [arr (s.reads.map target), arr (s.writes.map target),
      arr (s.grows.map target), arr (s.rebinds.map target), flag s.aborts, flag s.outputs]

def localVar (ty : Ty → Nat) (v : LocalVar) : String :=
  rec "local" [str v.name, nat (ty v.ty), str (varKind v.kind), nat v.scope, nat v.org]

def param (p : Param) : String := rec "param" [nat p.var, str (mode p.mode)]

def impl (ty : Ty → Nat) (i : Impl) : String :=
  rec "impl" [str i.name, arr (i.params.toList.map param),
    arr (i.results.toList.map fun t => nat (ty t)), arr (i.vars.toList.map (localVar ty)),
    block ty i.body, summary i.summary]

def global (ty : Ty → Nat) (g : Global) : String :=
  rec "global" [str g.name, nat (ty g.ty), str (varKind g.kind), expr ty g.init, nat g.org]

def rootRef : RootRef → String
  | .local x => rec "r_local" [nat x]
  | .global g => rec "r_global" [nat g]
  | .param i => rec "r_param" [nat i]

def context (c : Context) : String :=
  rec "context" [nat c.impl, str c.decl,
    arr (c.varRoots.map fun (x, rs) => rec "vr" [nat x, arr (rs.map rootRef)]),
    arr (c.resultRoots.map fun rs => arr (rs.map rootRef))]

def origin (o : Origin) : String := rec "origin" [nat o.file, nat o.line, str o.kind]

/-- The module as one line, without the final line feed. -/
def module (m : Module) : String :=
  let ty := tyIndex m.types
  rec "module" [str "goose-core/0.2", str "core-pilot",
    arr (m.files.toList.map fun f => rec "file" [str f]),
    arr (m.types.toList.map (tyEntry m.types)),
    arr (m.globals.toList.map (global ty)),
    arr (m.impls.toList.map (impl ty)),
    arr (m.contexts.toList.map context),
    nat m.entry,
    arr (m.origins.toList.map origin)]

end Goose.Share.Write
