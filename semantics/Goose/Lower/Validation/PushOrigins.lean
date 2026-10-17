import Goose.Core.Sound.Module
import Goose.Core.Sound.Invert

namespace Goose.Core

mutual
def Place.pushOrigins : Place → List (Option OriginId)
  | .var _ => []
  | .global _ => []
  | .deref e => e.pushOrigins
  | .elem v i _ => v.pushOrigins ++ i.pushOrigins
  | .field p _ => p.pushOrigins

termination_by x => sizeOf x

def View.pushOrigins : View → List (Option OriginId)
  | .of p => p.pushOrigins
  | .val e => e.pushOrigins

termination_by x => sizeOf x

def Bound.pushOrigins : Bound → List (Option OriginId)
  | .expr e | .fromEnd e => e.pushOrigins
  | .omitted => []

termination_by x => sizeOf x

def Expr.pushOrigins : Expr → List (Option OriginId)
  | .lit .. | .bool _ => []
  | .read p | .ref _ p | .pop p _ => p.pushOrigins
  | .slice _ v lo hi _ => v.pushOrigins ++ lo.pushOrigins ++ hi.pushOrigins
  | .len v => v.pushOrigins
  | .un _ e _ | .not e | .conv _ _ e _ | .fill _ e => e.pushOrigins
  | .bin _ a b _ | .cmp _ a b | .and a b | .or a b => a.pushOrigins ++ b.pushOrigins
  | .call _ args _ => args.flatMap Arg.pushOrigins
  | .push p e origin => origin :: (p.pushOrigins ++ e.pushOrigins)
  | .ifE c t f => c.pushOrigins ++ t.pushOrigins ++ f.pushOrigins
  | .blockE b => b.pushOrigins
  | .arrLit _ es | .structLit _ es => es.flatMap Expr.pushOrigins

termination_by x => sizeOf x

def Arg.pushOrigins : Arg → List (Option OriginId)
  | .byVal e => e.pushOrigins
  | .byRef _ p => p.pushOrigins

termination_by x => sizeOf x

def PrintArg.pushOrigins : PrintArg → List (Option OriginId)
  | .text _ => []
  | .expr e => e.pushOrigins

termination_by x => sizeOf x

def Stmt.pushOrigins : Stmt → List (Option OriginId)
  | .letS _ e _ | .rebind _ e _ | .expr e _ | .assertS e _ | .exit e _ => e.pushOrigins
  | .assign p e _ | .assignOp _ p e _ | .popN p e _ | .assignWhole p e _ => p.pushOrigins ++ e.pushOrigins
  | .resize p size fill _ => p.pushOrigins ++ size.pushOrigins ++ (match fill with | none => [] | some e => e.pushOrigins)
  | .clear p _ => p.pushOrigins
  | .append p v _ => p.pushOrigins ++ v.pushOrigins
  | .ifS c t f _ => c.pushOrigins ++ t.pushOrigins ++ (match f with | none => [] | some b => b.pushOrigins)
  | .while c b _ => c.pushOrigins ++ b.pushOrigins
  | .forRange _ lo hi b _ => lo.pushOrigins ++ hi.pushOrigins ++ b.pushOrigins
  | .forEach _ _ v _ b _ => v.pushOrigins ++ b.pushOrigins
  | .ret e _ => match e with | none => [] | some x => x.pushOrigins
  | .brk _ | .cont _ | .abort .. => []
  | .print args _ => args.flatMap PrintArg.pushOrigins

termination_by x => sizeOf x

def Block.pushOrigins : Block → List (Option OriginId)
  | .mk _ ss value => ss.flatMap Stmt.pushOrigins ++ (match value with | none => [] | some e => e.pushOrigins)
termination_by x => sizeOf x

end


end Goose.Core

namespace Goose.Lower.Validation.PushOrigins

open Goose.Core

def Present (origins : List (Option OriginId)) : Prop :=
  ∀ origin ∈ origins, origin.isSome = true

@[simp] theorem present_nil : Present [] := by simp [Present]

@[simp] theorem present_append (first second : List (Option OriginId)) :
    Present (first ++ second) ↔ Present first ∧ Present second := by
  simp [Present, List.mem_append, or_imp, forall_and]

@[simp] theorem present_cons (origin : Option OriginId) (rest : List (Option OriginId)) :
    Present (origin :: rest) ↔ origin.isSome = true ∧ Present rest := by
  simp [Present, List.mem_cons, forall_eq_or_imp]

open Goose.Core.Sound

theorem pushOrigin_present_of_typed {env : TEnv} {owner : Place} {arg : Expr}
    {origin : Option OriginId} {ty : Ty} {start finish : Nat}
    (typed : tyExpr env (.push owner arg origin) start = .ok (ty, finish))
    (profile : env.mod.profile = .shrink) : origin.isSome = true := by
  rcases tyExpr_push_profileOrg_ok env owner arg origin ty start finish typed with
    ⟨pilot, _⟩ | ⟨_, value, rfl⟩
  · rw [profile] at pilot
    cases pilot
  · rfl

end Goose.Lower.Validation.PushOrigins
