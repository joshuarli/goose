import Goose.Construct.Json
import Goose.Core.Writer

namespace Goose.Construct.Writer
open Goose.Core (Param NonlocalTarget)
open Goose.Core.Writer

def tyParts : TyList → List Ty
  | .nil => []
  | .cons t ts => t :: tyParts ts


def tyIndex (types : Array Ty) (t : Ty) : Nat :=
  (types.findIdx? (· == t)).getD types.size


def tyEntry (types : Array Ty) : Ty → String
  | .int t => rec "int" [str (intTy t)]
  | .bool => rec "bool" []
  | .unit => rec "unit" []
  | .arr e k => rec "arr" [nat (tyIndex types e), nat k]
  | .varr e => rec "varr" [nat (tyIndex types e)]
  | .grow e => rec "grow" [nat (tyIndex types e)]
  | .growshrink e => rec "growshrink" [nat (tyIndex types e)]
  | .limited e capacity => rec "limited" [nat (tyIndex types e), nat capacity]
  | .ref m t => rec "ref" [str (mutability m), nat (tyIndex types t)]
  | .slice m e => rec "slice" [str (mutability m), nat (tyIndex types e)]
  | .tuple ps => rec "tuple" [arr ((tyParts ps).map fun t => nat (tyIndex types t))]
  | .structT sid _ => rec "struct" [nat sid]

mutual
def place (ty : Ty → Nat) : Place → String
  | .var x => rec "p_local" [nat x]
  | .global g => rec "p_global" [nat g]
  | .deref e => rec "p_deref" [expr ty e]
  | .elem v i o => rec "p_elem" [view ty v, expr ty i, nat o]
  | .field p i => rec "p_field" [place ty p, nat i]

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
  | .push p e org => rec "e_push" ([place ty p, expr ty e] ++ org.toList.map nat)
  | .pop p org => rec "e_pop" [place ty p, nat org]
  | .ifE c t f => rec "e_if" [expr ty c, block ty t, block ty f]
  | .blockE b => rec "e_block" [block ty b]
  | .arrLit t es => rec "e_arr" [nat (ty t), arr (exprs ty es)]
  | .fill t e => rec "e_fill" [nat (ty t), expr ty e]
  | .structLit t es => rec "e_struct" [nat (ty t), arr (exprs ty es)]
  | .bytes t data org => rec "e_bytes" [nat (ty t), arr (data.map (nat ∘ UInt8.toNat)), nat org]
  | .str t parts org => rec "e_str" [nat (ty t), arr (printArgs ty parts), nat org]
  | .copy t source org => rec "e_copy" [nat (ty t), place ty source, nat org]
  | .resultLocal var org => rec "e_result_local" [nat var, nat org]
  | .values operands => rec "e_values" [arr (exprs ty operands)]

def exprs (ty : Ty → Nat) : List Expr → List String
  | [] => []
  | e :: es => expr ty e :: exprs ty es

def arg (ty : Ty → Nat) : Arg → String
  | .byVal e => rec "a_val" [expr ty e]
  | .construct e => rec "a_construct" [expr ty e]
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
  | .view v => rec "pa_view" [view ty v]

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
  | .popN p e o => rec "s_pop_n" [place ty p, expr ty e, nat o]
  | .resize p size fill o => rec "s_resize" [place ty p, expr ty size, arr (optExpr ty fill), nat o]
  | .clear p o => rec "s_clear" [place ty p, nat o]
  | .assignWhole p e o => rec "s_assign_whole" [place ty p, expr ty e, nat o]
  | .ifS c t f o => rec "s_if" [expr ty c, block ty t, arr (optBlock ty f), nat o]
  | .while c b o => rec "s_while" [expr ty c, block ty b, nat o]
  | .forRange x lo hi b o =>
    rec "s_for_range" [nat x, expr ty lo, expr ty hi, block ty b, nat o]
  | .forEach x i v byRef b o =>
    rec "s_for_each" [nat x, arr (i.toList.map nat), view ty v, flag byRef, block ty b, nat o]
  | .receive vars producer org => rec "s_receive" [arr (vars.map nat), expr ty producer, nat org]
  | .appendValue owner producer org => rec "s_append_value" [place ty owner, expr ty producer, nat org]
  | .appendConstruct owner producer org => rec "s_append_construct" [place ty owner, expr ty producer, nat org]
  | .retValues operands org => rec "s_ret_values" [arr (exprs ty operands), nat org]
  | .retForward producer org => rec "s_ret_forward" [expr ty producer, nat org]
  | .returnFrom target operands org => rec "s_return_from" [nat target, arr (exprs ty operands), nat org]
  | .returnFromForward target producer org => rec "s_return_from_forward" [nat target, expr ty producer, nat org]
  | .breakValue value org => rec "s_break_value" [expr ty value, nat org]
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
  | .known s => rec "summary"
      [arr (s.reads.map target), arr (s.writes.map target), arr (s.grows.map target),
       arr (s.shrinks.map target), arr (s.rebinds.map target), arr (s.constructs.map nat),
       arr (s.needs.map nat), arr (s.escapes.map nat), flag s.aborts, flag s.outputs]

private def result (ty : Ty → Nat) (descriptor : ResultDescriptor) : String :=
  rec "result" [nat (ty descriptor.ty), str descriptor.request.tag,
    arr (descriptor.namedLocal.toList.map nat)]

def localVar (ty : Ty → Nat) (v : LocalVar) : String :=
  rec "local" [str v.name, nat (ty v.ty), str (varKind v.kind), nat v.scope, nat v.org]

def param (p : Param) : String := rec "param" [nat p.var, str (mode p.mode)]

def impl (ty : Ty → Nat) (i : Impl) : String :=
  rec "impl" [str i.name, arr (i.params.toList.map param),
    arr (i.results.toList.map (result ty)), arr (i.vars.toList.map (localVar ty)),
    block ty i.body, summary i.summary]

def global (ty : Ty → Nat) (g : Global) : String :=
  rec "global" [str g.name, nat (ty g.ty), str (varKind g.kind), expr ty g.init, nat g.org]

def rootRef : RootRef → String
  | .static => rec "r_static" []
  | .local x => rec "r_local" [nat x]
  | .global g => rec "r_global" [nat g]
  | .param i => rec "r_param" [nat i]

def context (c : Context) : String :=
  rec "context" [nat c.impl, str c.decl,

    arr (c.varRoots.map fun (x, rs) =>
      match (c.contentRoots.find? (·.1 == x)).map (·.2) with
      | some cs => rec "vr" [nat x, arr (rs.map rootRef), arr (cs.map rootRef)]
      | none => rec "vr" [nat x, arr (rs.map rootRef)]),
    arr (c.resultRoots.map fun rs => arr (rs.map rootRef))]

def origin (o : Origin) : String := rec "origin" [nat o.file, nat o.line, str o.kind]

def structDef (ty : Ty → Nat) (d : StructDef) : String :=
  rec "struct_def" [nat d.byteSize, arr (d.fields.toList.map fun f =>
    rec "field" [nat (ty f.ty), str (varKind f.binding), str (mutability f.contents), nat f.byteOffset]), str d.displayName]


def module (m : Module) : String :=
  let ty := tyIndex m.types
  rec "module" [str Decode.schemaName, str "core-construction",
    arr (m.files.toList.map fun f => rec "file" [str f]),
    arr (m.types.toList.map (tyEntry m.types)),
    arr (m.structs.toList.map (structDef ty)),
    arr (m.targets.toList.map fun target => rec "target" [arr (target.members.map nat)]),
    arr (m.globals.toList.map (global ty)),
    arr (m.impls.toList.map (impl ty)),
    arr (m.contexts.toList.map context), nat m.entry, arr (m.origins.toList.map origin)]

end Goose.Construct.Writer
