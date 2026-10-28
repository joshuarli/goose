import Goose.Proofs.ExitExecutionBlockNonlocal
import Goose.Proofs.Exit

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem activation_if_block_returnFrom_propagates (fuel : Nat) (config : EvalConfig)
    (activation target : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId : Nat) (operands : List Expr)
    (origin ifOrigin handlerOrigin : Goose.Core.OriginId) (rest innerRest : List Stmt)
    (tail innerTail : Option Expr) (initial outerBound innerBound before : ExecutionState)
    (carriers : List Carrier) (implementation : Impl)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (outerBinding : bindAll activation.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == activation.act then
        { current with scopes := (outerScope, initial.nextScope) :: activation.scopes } else current) } = .ok () outerBound)
    (innerBinding : bindAll activation.act outerBound.nextScope []
      { outerBound with nextScope := outerBound.nextScope + 1 } = .ok () innerBound)
    (selected : targetActivation config targetId innerBound = .ok target innerBound)
    (_outer : ∃ prior between suffix,
      innerBound.activations = prior ++ activation :: between ++ target :: suffix)
    (distinct : target.act ≠ activation.act)
    (completed : withExitChannels
      { activation with scopes := (innerScope, outerBound.nextScope) :: (outerScope, initial.nextScope) :: activation.scopes }
      target operands origin
      (fun channels => evalOperands fuel config
        { activation with scopes := (innerScope, outerBound.nextScope) :: (outerScope, initial.nextScope) :: activation.scopes } channels operands)
      innerBound = .ok carriers before)
    :
    let innerEnv := { activation with scopes := (outerScope, initial.nextScope) :: activation.scopes }
    let unwound := releaseScopeState activation outerScope initial.nextScope
      (releaseScopeState innerEnv innerScope outerBound.nextScope before)
    enterActivation (fuel + 7) config activation pre
      (.mk outerScope (.ifS (.bool true)
        (.mk innerScope (.returnFrom targetId operands origin :: innerRest) innerTail) none ifOrigin :: rest) tail)
      handlerOrigin initial = .escape ⟨target.act, .nonlocal targetId⟩ carriers { unwound with
        activations := unwound.activations.filter (fun current => current.act != activation.act) } := by
  let innerEnv := { activation with scopes := (outerScope, initial.nextScope) :: activation.scopes }
  obtain ⟨_, _, _, _, _, _, _, escaped, _⟩ :=
    block_returnFrom_nearest_unwinds fuel config innerEnv target [] [] innerScope targetId
      operands origin innerRest innerTail outerBound innerBound before carriers innerBinding selected completed
  have bodyEscape : execActivationBody (fuel + 6) config activation pre
      (.mk outerScope (.ifS (.bool true)
        (.mk innerScope (.returnFrom targetId operands origin :: innerRest) innerTail) none ifOrigin :: rest) tail) initial =
      .escape ⟨target.act, .nonlocal targetId⟩ carriers
        (releaseScopeState activation outerScope initial.nextScope
          (releaseScopeState innerEnv innerScope outerBound.nextScope before)) := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, outerBinding, execStmts, execStmt,
      evalValue, expectBool, pure, if_true]
    dsimp only [innerEnv] at escaped ⊢
    simp only [escaped, releaseScope, bind, EvalM.get, EvalM.set]
  simp only [enterActivation, lookup]
  exact Goose.Proofs.Exit.runtime_activation_propagates config.layout activation
    (implementation.results.toList.map (·.ty)) handlerOrigin _ initial _
    ⟨target.act, .nonlocal targetId⟩ carriers bodyEscape distinct

theorem activation_block_unwind_preserves_outside (activation : RuntimeActivation)
    (outerScope innerScope : Nat) (outerInst innerInst : Goose.Core.ScopeInst) (before : ExecutionState)
    (entry : Goose.Core.RootInst × Value)
    (outerOutside : (Goose.Proofs.Exit.runtimeScopeRoots activation outerScope outerInst).contains entry.1 = false)
    (innerOutside : (Goose.Proofs.Exit.runtimeScopeRoots
      { activation with scopes := (outerScope, outerInst) :: activation.scopes } innerScope innerInst).contains entry.1 = false) :
    let innerEnv := { activation with scopes := (outerScope, outerInst) :: activation.scopes }
    let unwound := releaseScopeState activation outerScope outerInst
      (releaseScopeState innerEnv innerScope innerInst before)
    unwound.construction = before.construction ∧ (entry ∈ unwound.objects ↔ entry ∈ before.objects) := by
  refine ⟨rfl, ?_⟩
  rw [Goose.Proofs.Exit.runtime_release_scope_outside activation outerScope outerInst _ entry outerOutside]
  exact Goose.Proofs.Exit.runtime_release_scope_outside _ innerScope innerInst before entry innerOutside

#print axioms activation_block_unwind_preserves_outside
#print axioms activation_if_block_returnFrom_propagates

end Goose.Proofs.ExitExecution
