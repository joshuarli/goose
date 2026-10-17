import Goose.Lower.Validation.SourceSymbolRefs

namespace Goose.Lower.Validation.SourceSymbolSource

open Goose.Core Goose.Core.Sound

inductive Reference where
  | slot (index : Nat)
  | global (index : Nat)
  | context (index : Nat)
  | origin (index : Nat)

def Reference.Within (module : Module) (vars : Array LocalVar) : Reference → Prop
  | .slot index => index < vars.size
  | .global index => index < module.globals.size
  | .context index => index < module.contexts.size
  | .origin index => index < module.origins.size

def Within (module : Module) (vars : Array LocalVar) (references : List Reference) : Prop :=
  ∀ reference ∈ references, reference.Within module vars

@[simp] theorem within_nil : Within module vars [] := by simp [Within]
@[simp] theorem within_append : Within module vars (first ++ second) ↔ Within module vars first ∧ Within module vars second := by
  simp [Within, List.mem_append, or_imp, forall_and]
@[simp] theorem within_cons : Within module vars (first :: rest) ↔ first.Within module vars ∧ Within module vars rest := by
  simp [Within, List.mem_cons, forall_eq_or_imp]

mutual

def placeReferences : Place → List Reference
  | .var index => [.slot index]
  | .global index => [.global index]
  | .deref expr => exprReferences expr
  | .elem view index origin => .origin origin :: (viewReferences view ++ exprReferences index)
  | .field place _ => placeReferences place
termination_by x => sizeOf x

def viewReferences : View → List Reference
  | .of place => placeReferences place
  | .val expr => exprReferences expr
termination_by x => sizeOf x

def boundReferences : Bound → List Reference
  | .omitted => []
  | .expr expr | .fromEnd expr => exprReferences expr
termination_by x => sizeOf x

def exprReferences : Expr → List Reference
  | .lit .. | .bool _ => []
  | .read place | .ref _ place => placeReferences place
  | .slice _ view lo hi origin => .origin origin ::
      (viewReferences view ++ boundReferences lo ++ boundReferences hi)
  | .len view => viewReferences view
  | .un _ expr origin | .conv _ _ expr origin => .origin origin :: exprReferences expr
  | .not expr | .fill _ expr => exprReferences expr
  | .bin _ left right origin => .origin origin :: (exprReferences left ++ exprReferences right)
  | .cmp _ left right | .and left right | .or left right => exprReferences left ++ exprReferences right
  | .call context args origin => .origin origin :: .context context :: args.flatMap argReferences
  | .push place expr origin => origin.toList.map Reference.origin ++ placeReferences place ++ exprReferences expr
  | .pop place origin => .origin origin :: placeReferences place
  | .ifE condition yes no => exprReferences condition ++ blockReferences yes ++ blockReferences no
  | .blockE body => blockReferences body
  | .arrLit _ exprs | .structLit _ exprs => exprs.flatMap exprReferences
termination_by x => sizeOf x

def argReferences : Arg → List Reference
  | .byVal expr => exprReferences expr
  | .byRef _ place => placeReferences place
termination_by x => sizeOf x

def printReferences : PrintArg → List Reference
  | .text _ => []
  | .expr expr => exprReferences expr
termination_by x => sizeOf x

def stmtReferences (stmt : Stmt) : List Reference :=
  .origin (stmtSourceOrigin stmt) :: (match stmt with
  | .letS slot expr _ | .rebind slot expr _ => .slot slot :: exprReferences expr
  | .expr expr _ | .assertS expr _ | .exit expr _ => exprReferences expr
  | .assign place expr _ | .assignOp _ place expr _ | .popN place expr _ | .assignWhole place expr _ =>
      placeReferences place ++ exprReferences expr
  | .resize place size fill _ => placeReferences place ++ exprReferences size ++
      (match fill with | none => [] | some expr => exprReferences expr)
  | .clear place _ => placeReferences place
  | .append place view _ => placeReferences place ++ viewReferences view
  | .ifS condition yes no _ => exprReferences condition ++ blockReferences yes ++
      (match no with | none => [] | some body => blockReferences body)
  | .while condition body _ => exprReferences condition ++ blockReferences body
  | .forRange slot lo hi body _ => .slot slot :: (exprReferences lo ++ exprReferences hi ++ blockReferences body)
  | .forEach slot index view _ body _ => .slot slot ::
      (index.toList.map Reference.slot ++ viewReferences view ++ blockReferences body)
  | .ret expr _ => match expr with | none => [] | some expr => exprReferences expr
  | .brk _ | .cont _ | .abort .. => []
  | .print args _ => args.flatMap printReferences)
termination_by sizeOf stmt

def blockReferences : Block → List Reference
  | .mk _ stmts tail => stmts.flatMap stmtReferences ++
      (match tail with | none => [] | some expr => exprReferences expr)
termination_by x => sizeOf x

end

theorem Within.transport {env after : TEnv} (mod : after.mod = env.mod)
    (vars : after.vars = env.vars) (checked : Within after.mod after.vars references) :
    Within env.mod env.vars references := by
  simpa only [mod, vars] using checked

end Goose.Lower.Validation.SourceSymbolSource
