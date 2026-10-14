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

mutual
def expressionResultTypes? : Nat → DeclarationEnv → Expr → Option (List Ty)
  | 0, _, _ => none
  | fuel + 1, env, .values expressions => do
      let channels ← expressions.mapM (expressionResultTypes? fuel env)
      if channels.all (fun types => types.length == 1) then some channels.flatten else none
  | _, env, .call contextId _ _ => do
      let context ← env.module.contexts[contextId]?
      let implementation ← env.module.impls[context.impl]?
      some (implementation.results.toList.map (·.ty))
  | fuel + 1, env, .blockE block _ => blockResultTypes? fuel env block
  | fuel + 1, env, .ifE _ left right _ =>
      match blockResultTypes? fuel env left, blockResultTypes? fuel env right with
      | some [.unit], some rightTypes => some rightTypes
      | some leftTypes, _ => some leftTypes
      | none, rightTypes => rightTypes
  | _ + 1, env, expression => (env.exprType? expression).map (fun ty => [ty])

def blockResultTypes? : Nat → DeclarationEnv → Block → Option (List Ty)
  | 0, _, _ => none
  | fuel + 1, env, .mk _ statements tail =>
      match tail with
      | some expression => expressionResultTypes? fuel env expression
      | none => firstValueBreakTypes fuel env statements <|> some [.unit]

private def firstValueBreakTypes : Nat → DeclarationEnv → List Stmt → Option (List Ty)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, env, statement :: rest =>
      let current := match statement with
        | .breakValue expression _ => expressionResultTypes? fuel env expression
        | .ifS _ (.mk _ left _) right _ =>
            firstValueBreakTypes fuel env left <|>
              (right.bind fun block => match block with
                | .mk _ statements _ => firstValueBreakTypes fuel env statements)
        | .while _ (.mk _ statements _) _ |
          .forRange _ _ _ (.mk _ statements _) _ |
          .forEach _ _ _ _ (.mk _ statements _) _ => firstValueBreakTypes fuel env statements
        | _ => none
      current <|> firstValueBreakTypes fuel env rest
end


end Goose.Construct
