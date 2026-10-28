import Goose.Proofs.ExitExecutionBlockNonlocal
import Goose.Proofs.ExitExecutionLandedChannels

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem activation_if_block_returnFrom_catches (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
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
    (selected : targetActivation config targetId innerBound = .ok activation innerBound)
    (completed : withExitChannels
      { activation with scopes := (innerScope, outerBound.nextScope) :: (outerScope, initial.nextScope) :: activation.scopes }
      activation operands origin
      (fun channels => evalOperands fuel config
        { activation with scopes := (innerScope, outerBound.nextScope) :: (outerScope, initial.nextScope) :: activation.scopes } channels operands)
      innerBound = .ok carriers before)
    (landed : LandedResultChannels before activation.channels (implementation.results.toList.map (·.ty)) carriers) :
    let innerEnv := { activation with scopes := (outerScope, initial.nextScope) :: activation.scopes }
    let unwound := releaseScopeState activation outerScope initial.nextScope
      (releaseScopeState innerEnv innerScope outerBound.nextScope before)
    enterActivation (fuel + 7) config activation pre
      (.mk outerScope (.ifS (.bool true)
        (.mk innerScope (.returnFrom targetId operands origin :: innerRest) innerTail) none ifOrigin :: rest) tail)
      handlerOrigin initial = .ok carriers { unwound with
        activations := unwound.activations.filter (fun current => current.act != activation.act) } := by
  let innerEnv := { activation with scopes := (outerScope, initial.nextScope) :: activation.scopes }
  obtain ⟨_, _, _, _, _, _, _, escaped, _⟩ :=
    block_returnFrom_nearest_unwinds fuel config innerEnv activation [] [] innerScope targetId
      operands origin innerRest innerTail outerBound innerBound before carriers innerBinding selected completed
  have bodyEscape : execActivationBody (fuel + 6) config activation pre
      (.mk outerScope (.ifS (.bool true)
        (.mk innerScope (.returnFrom targetId operands origin :: innerRest) innerTail) none ifOrigin :: rest) tail) initial =
      .escape ⟨activation.act, .nonlocal targetId⟩ carriers
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
  have preserved : LandedResultChannels
      (releaseScopeState activation outerScope initial.nextScope
        (releaseScopeState innerEnv innerScope outerBound.nextScope before))
      activation.channels (implementation.results.toList.map (·.ty)) carriers :=
    landed.of_construction_eq (before := before) (after :=
      releaseScopeState activation outerScope initial.nextScope
        (releaseScopeState innerEnv innerScope outerBound.nextScope before)) rfl
  simp only [enterActivation, lookup]
  exact finishActivation_catches_landed config.layout activation (implementation.results.toList.map (·.ty))
    handlerOrigin _ initial _ ⟨activation.act, .nonlocal targetId⟩ carriers bodyEscape rfl preserved

#print axioms activation_if_block_returnFrom_catches

end Goose.Proofs.ExitExecution
