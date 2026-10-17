import Goose.Lower.Validation.ScopeSource
import Goose.Lower.ContextLowering

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ScopeAction.emitReturn (parents : Array (Option ScopeId))
    (values : List ValueId) (origin : Option OriginId) :
    ScopeAction parents none (Goose.Lower.emitTerm (.ret values origin)) := by
  refine ⟨advB_emitTerm _, ?_⟩
  intro env before entry exit valid bound head
  have empty : before.stack = [] := by
    cases stack : before.stack with
    | nil => rfl
    | cons scope rest => simp [stack] at head
  have unwound := (ScopeAction.unwindReturn parents none values origin).preserves
    env before entry exit valid bound head
  simpa only [bind_run, leaveTo, get_apply, empty, List.length_nil, Nat.sub_self,
    List.take_zero, leaveAll, pure_run] using unwound

theorem ScopeAction.finishFunction (parents : Array (Option ScopeId)) (impl : Impl) (value : ValueId) :
    ScopeAction parents none (Goose.Lower.finishFunction impl value) := by
  unfold Goose.Lower.finishFunction
  refine (ScopeAction.read parents none).bind fun env =>
    (ScopeAction.isLive parents none).bind fun live => ?_
  cases live <;> simp only [Bool.false_eq_true, reduceIte]
  · exact ScopeAction.pure parents none _
  · split
    · exact ScopeAction.header [] [] advB_newBlock0 fun sink _ =>
        ScopeAction.emitNeutralTerm parents none (.br sink []) rfl
    · exact ScopeAction.emitReturn parents _ none

def scopeInitialState (env : LEnv) (types : List VTy) : LS :=
  (setCur (some 0) env (newBlock types env initState).2).2

theorem scopeInitialState_stack (env : LEnv) (types : List VTy) :
    (scopeInitialState env types).stack = [] := rfl

theorem scopeInitialState_size (env : LEnv) (types : List VTy) :
    (scopeInitialState env types).blocks.size = 1 := rfl

theorem scopeInitialState_bound (env : LEnv) (types : List VTy) :
    ScopeLiveBound (scopeInitialState env types) := by
  intro block current
  have blockId : 0 = block := Option.some.inj current
  subst block
  exact Nat.zero_lt_succ _

theorem scopeInitialState_valid (parents : Array (Option ScopeId)) (env : LEnv) (types : List VTy) :
    ScopeBuilder parents (fun _ => []) (fun _ => []) (scopeInitialState env types) := by
  have empty := ScopeBuilder.initState parents (fun _ => []) (fun _ => [])
  have bound : ScopeLiveBound initState := by intro block live; cases live
  have allocated := empty.newBlock bound env types
  have same : (fun block : BlockId => if block = initState.blocks.size then initState.stack else []) =
      (fun _ => ([] : List ScopeId)) := by
    funext block
    split <;> rfl
  rw [same] at allocated
  exact allocated.setCur (some 0) (by intro block current; rfl) env

def scopeImplTail (impl : Impl) (parameters : List ValueId) : B Unit := do
  let pre := (impl.params.toList.zip parameters).map fun (parameter, value) =>
    (parameter.var, value, (impl.vars[parameter.var]?.map (·.org)).getD 0)
  let result ← lowerBlock none pre false impl.body
  finishFunction impl result

theorem scopeImplTail_action (parents : Array (Option ScopeId)) (impl : Impl)
    (parameters : List ValueId) (source : ScopeTableContains parents (blockScopes none impl.body)) :
    ScopeAction parents none (scopeImplTail impl parameters) := by
  unfold scopeImplTail
  exact (scope_lowerBlock parents none none _ false impl.body source).bind fun value =>
    ScopeAction.finishFunction parents impl value

theorem lowerImpl_scopeTraces {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) :
    ∃ entry exit : BlockId → List ScopeId, entry 0 = [] ∧
      ∀ block body, (lowerImpl module impl).blocks[block]? = some body →
        ScopeTrace (lowerImpl module impl).scopes (entry block) body.insts (exit block) := by
  let env := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun parameter => VTy.data (tyOfVar impl parameter.var)
  let parameters := (newBlock types env initState).1.2
  let initial := scopeInitialState env types
  let action := scopeImplTail impl parameters
  let parents := (lowerImpl module impl).scopes
  have source := lowerImpl_lexicalScopeTable checked
  have actionScopes := scopeImplTail_action parents impl parameters source
  obtain ⟨entry, exit, valid, framed⟩ := actionScopes.preserves env initial
    (fun _ => []) (fun _ => []) (scopeInitialState_valid parents env types)
    (scopeInitialState_bound env types) rfl
  have initialEntry : entry 0 = [] := (framed 0 (by rw [scopeInitialState_size]; decide)).1
  have blocks : (lowerImpl module impl).blocks = finishBlocks (action env initial).2.blocks := by rfl
  refine ⟨entry, exit, initialEntry, ?_⟩
  intro block body lookup
  rw [blocks] at lookup
  simp only [finishBlocks, Array.getElem?_map] at lookup
  cases row : (action env initial).2.blocks[block]? with
  | none => simp [row] at lookup
  | some built =>
    simp only [row, Option.map_some, Option.some.injEq] at lookup
    subst body
    exact valid.traces block built row

theorem lowerContextAt_scopeTraces {module : Core.Module} {impl : Impl}
    (checked : checkImpl module impl = .ok ()) (context : Context) :
    ∃ entry exit : BlockId → List ScopeId, entry 0 = [] ∧
      ∀ block body, (lowerContextAt module context impl).blocks[block]? = some body →
        ScopeTrace (lowerContextAt module context impl).scopes (entry block) body.insts (exit block) := by
  obtain ⟨entry, exit, initial, traces⟩ := lowerImpl_scopeTraces checked
  refine ⟨entry, exit, initial, ?_⟩
  intro block body lookup
  rw [lowerContextAt_blocks] at lookup
  simpa only [lowerContextAt_scopes] using traces block body lookup

def scopeGlobalTail (global : Core.Global) : B Unit := do
  let value ← lowerExpr global.init
  emitTerm (.ret [value] (some global.org))

theorem lowerGlobal_scopeTraces {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (checked : checkGlobal module index global = .ok ()) :
    ∃ entry exit : BlockId → List ScopeId, entry 0 = [] ∧
      ∀ block body, (lowerGlobal module global).init.blocks[block]? = some body →
        ScopeTrace (lowerGlobal module global).init.scopes (entry block) body.insts (exit block) := by
  let env := lowerEnv module #[] [global.ty]
  let initial := scopeInitialState env []
  let action := scopeGlobalTail global
  let parents := (lowerGlobal module global).init.scopes
  have source := lowerGlobal_lexicalScopeTable checked
  have actionScopes : ScopeAction parents none action :=
    (scope_lowerExpr parents none global.init source).bind fun value =>
      ScopeAction.emitReturn parents [value] (some global.org)
  obtain ⟨entry, exit, valid, framed⟩ := actionScopes.preserves env initial
    (fun _ => []) (fun _ => []) (scopeInitialState_valid parents env [])
    (scopeInitialState_bound env []) rfl
  have initialEntry : entry 0 = [] := (framed 0 (by rw [scopeInitialState_size]; decide)).1
  have blocks : (lowerGlobal module global).init.blocks = finishBlocks (action env initial).2.blocks := by rfl
  refine ⟨entry, exit, initialEntry, ?_⟩
  intro block body lookup
  rw [blocks] at lookup
  simp only [finishBlocks, Array.getElem?_map] at lookup
  cases row : (action env initial).2.blocks[block]? with
  | none => simp [row] at lookup
  | some built =>
    simp only [row, Option.map_some, Option.some.injEq] at lookup
    subst body
    exact valid.traces block built row

end Goose.Lower.Validation
