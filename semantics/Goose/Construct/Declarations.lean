import Goose.Construct.Syntax

namespace Goose.Construct

def Ty.storageType : Ty → Bool
  | .int _ | .bool => true
  | .arr element _ | .varr element | .grow element => element.flat || element.variableElement
  | .growshrink element | .limited element _ => element.flat
  | .structT _ fields => fields.flat
  | _ => false

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
    | _, .arr .. => false
    | _, _ => match source.element?, target.element? with
      | some a, some b => a == b && source.storageType && target.storageType
      | _, _ => false

def Ty.passesTo (source target : Ty) : Bool :=
  match source, target with
  | .ref sourceMut a, .ref targetMut b | .slice sourceMut a, .slice targetMut b =>
      a == b && (sourceMut == .mutable || targetMut == .readOnly)
  | _, _ => source.adaptsTo target

def Ty.ownerElem? : Ty → Option Ty
  | .grow element | .growshrink element | .limited element _ => some element
  | _ => none

structure DeclarationEnv where
  module : Module
  variables : Array LocalVar

mutual
def DeclarationEnv.placeType? (env : DeclarationEnv) : Place → Option Ty
  | .var x => (env.variables[x]?).map (·.ty)
  | .global g => (env.module.globals[g]?).map (·.ty)
  | .deref e => do
    match ← env.exprType? e with
    | .ref _ t => some t
    | _ => none
  | .elem v _ _ => env.viewElement? v
  | .field p i => do
    match ← env.placeType? p with
    | .structT sid _ => ((← env.module.structs[sid]?).fields[i]?).map (·.ty)
    | _ => none

def DeclarationEnv.viewElement? (env : DeclarationEnv) : View → Option Ty
  | .of p => do
    match ← env.placeType? p with
    | .arr t _ | .varr t | .grow t | .growshrink t | .limited t _ => some t
    | _ => none
  | .val e => do
    match ← env.exprType? e with
    | .slice _ t => some t
    | _ => none

def DeclarationEnv.exprType? (env : DeclarationEnv) : Expr → Option Ty
  | .lit t _ => some (.int t)
  | .bool _ | .cmp .. | .and .. | .or .. | .not _ => some .bool
  | .read p => env.placeType? p
  | .ref m p => (env.placeType? p).map (.ref m)
  | .slice m v _ _ _ => (env.viewElement? v).map (.slice m)
  | .len _ => some (.int .i64)
  | .un _ e _ => env.exprType? e
  | .bin _ a _ _ => env.exprType? a
  | .conv _ t _ _ => some t
  | .call c _ _ => do
    let context ← env.module.contexts[c]?
    let impl ← env.module.impls[context.impl]?
    match impl.results.toList with
    | [] => some .unit
    | [t] => some t.ty
    | _ => none
  | .push p _ _ => do some (.ref .mutable (← (← env.placeType? p).ownerElem?))
  | .pop p _ => do (← env.placeType? p).ownerElem?
  | .ifE _ t _ _ => env.blockType? t
  | .blockE b _ => env.blockType? b
  | .arrLit t _ _ | .fill t _ _ | .structLit t _ | .bytes t _ _ | .str t _ _ | .copy t _ _ => some t
  | .resultLocal id _ => (env.variables[id]?).map (·.ty)
  | .values _ => none

def DeclarationEnv.blockType? (env : DeclarationEnv) : Block → Option Ty
  | .mk _ _ none => some .unit
  | .mk _ _ (some e) => env.exprType? e
end

end Goose.Construct
