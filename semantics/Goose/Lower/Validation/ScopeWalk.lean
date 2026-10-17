import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def scopeNeutral : Inst → Bool
  | .eff (.enter _) | .eff (.leave _) | .term (.ret ..) => false
  | _ => true

inductive ScopeTrace (parents : Array (Option ScopeId)) :
    List ScopeId → List Inst → List ScopeId → Prop
  | nil (stack) : ScopeTrace parents stack [] stack
  | neutral {before after inst rest} (neutral : scopeNeutral inst = true)
      (tail : ScopeTrace parents before rest after) :
      ScopeTrace parents before (inst :: rest) after
  | enter {before after scope rest}
      (parent : parents[scope]?.getD none = before.head?)
      (tail : ScopeTrace parents (scope :: before) rest after) :
      ScopeTrace parents before (.eff (.enter scope) :: rest) after
  | leave {before after scope rest}
      (tail : ScopeTrace parents before rest after) :
      ScopeTrace parents (scope :: before) (.eff (.leave scope) :: rest) after
  | ret {after values origin rest}
      (tail : ScopeTrace parents [] rest after) :
      ScopeTrace parents [] (.term (.ret values origin) :: rest) after

theorem walkBlock_cons (f : Func) (block : BlockId) (params) (inst : Inst)
    (rest : List Inst) (stack : List ScopeId) (walk : ScopeWalk) :
    walkBlock f block ⟨params, inst :: rest⟩ stack walk =
      let next := walkBlock f block ⟨params, [inst]⟩ stack walk
      walkBlock f block ⟨params, rest⟩ next.1 next.2 := by
  rfl

theorem walkBlock_neutral {inst : Inst} (neutral : scopeNeutral inst = true)
    (f : Func) (block : BlockId) (params) (stack : List ScopeId) (walk : ScopeWalk) :
    (walkBlock f block ⟨params, [inst]⟩ stack walk).1 = stack ∧
      (walkBlock f block ⟨params, [inst]⟩ stack walk).2.scopes = walk.scopes ∧
      (walkBlock f block ⟨params, [inst]⟩ stack walk).2.join = walk.join := by
  cases inst with
  | «def» value op =>
    cases op <;> simp [GIR.walkBlock, ScopeWalk.noteStorage]
    all_goals repeat' first | split | constructor | rfl
  | eff effect =>
    cases effect <;> simp_all [scopeNeutral, GIR.walkBlock, ScopeWalk.noteStorage]
    all_goals repeat' first | split | constructor | rfl
  | term term =>
    cases term <;> simp_all [scopeNeutral, GIR.walkBlock]

theorem ScopeTrace.walkBlock {f : Func} {before after : List ScopeId} {insts : List Inst}
    (trace : ScopeTrace f.scopes before insts after) (block : BlockId) (params)
    (walk : ScopeWalk) :
    (walkBlock f block ⟨params, insts⟩ before walk).1 = after ∧
      (walkBlock f block ⟨params, insts⟩ before walk).2.scopes = walk.scopes ∧
      (walkBlock f block ⟨params, insts⟩ before walk).2.join = walk.join := by
  induction trace generalizing walk with
  | nil => simp [GIR.walkBlock]
  | @neutral before after inst rest neutral tail ih =>
    rw [walkBlock_cons]
    have one := walkBlock_neutral neutral f block params before walk
    simp only [one.1]
    obtain ⟨out, scopes, join⟩ := ih (GIR.walkBlock f block ⟨params, [inst]⟩ before walk).2
    exact ⟨out, scopes.trans one.2.1, join.trans one.2.2⟩
  | @enter before after scope rest parent tail ih =>
    rw [walkBlock_cons]
    cases before with
    | nil => simpa [GIR.walkBlock, parent] using ih walk
    | cons head rest => simpa [GIR.walkBlock, parent] using ih walk
  | leave tail ih =>
    rw [walkBlock_cons]
    simpa [GIR.walkBlock] using ih walk
  | ret tail ih =>
    rw [walkBlock_cons]
    simpa [GIR.walkBlock] using ih walk

theorem ScopeTrace.append {parents : Array (Option ScopeId)}
    {before middle after : List ScopeId} {left right : List Inst}
    (first : ScopeTrace parents before left middle)
    (second : ScopeTrace parents middle right after) :
    ScopeTrace parents before (left ++ right) after := by
  induction first with
  | nil => exact second
  | neutral neutral tail ih => exact .neutral neutral (ih second)
  | enter parent tail ih => exact .enter parent (ih second)
  | leave tail ih => exact .leave (ih second)
  | ret tail ih => exact .ret (ih second)

theorem ScopeTrace.leavePrefix (parents : Array (Option ScopeId))
    (front rest : List ScopeId) :
    ScopeTrace parents (front ++ rest) (front.map fun sc => .eff (.leave sc)) rest := by
  induction front with
  | nil => exact .nil rest
  | cons scope front ih => exact .leave ih

theorem ScopeTrace.leaveTo (parents : Array (Option ScopeId))
    (stack : List ScopeId) (depth : Nat) :
    ScopeTrace parents stack
      ((stack.take (stack.length - depth)).map fun sc => .eff (.leave sc))
      (stack.drop (stack.length - depth)) := by
  have trace := ScopeTrace.leavePrefix parents
    (stack.take (stack.length - depth)) (stack.drop (stack.length - depth))
  simpa using trace

theorem ScopeTrace.leaveReturn (parents : Array (Option ScopeId))
    (stack : List ScopeId) (values : List ValueId) (origin : Option OriginId) :
    ScopeTrace parents stack
      ((stack.map fun sc => .eff (.leave sc)) ++ [.term (.ret values origin)]) [] := by
  have leaves : ScopeTrace parents stack
      (stack.map fun sc => .eff (.leave sc)) [] := by
    simpa using ScopeTrace.leavePrefix parents stack []
  exact leaves.append (.ret (.nil []))

theorem ScopeTrace.scoped {parents : Array (Option ScopeId)}
    {before : List ScopeId} {scope : ScopeId} {body : List Inst}
    (parent : parents[scope]?.getD none = before.head?)
    (inside : ScopeTrace parents (scope :: before) body (scope :: before)) :
    ScopeTrace parents before
      (.eff (.enter scope) :: (body ++ [.eff (.leave scope)])) before :=
  .enter parent (inside.append (.leave (.nil before)))

end Goose.Lower.Validation
