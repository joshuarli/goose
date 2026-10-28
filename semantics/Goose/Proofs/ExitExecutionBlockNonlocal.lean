import Goose.Proofs.ExitExecutionBase

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem block_returnFrom_nearest_unwinds (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope targetId : Nat) (operands : List Expr)
    (origin : Goose.Core.OriginId) (rest : List Stmt) (tail : Option Expr)
    (initial bound before : ExecutionState) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (selected : targetActivation config targetId bound = .ok activation bound)
    (completed : withExitChannels
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      activation operands origin
      (fun channels => evalOperands fuel config
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels operands)
      bound = .ok carriers before) :
    ∃ target discarded outer,
      config.module.targets[targetId]? = some target ∧
      bound.activations = discarded ++ activation :: outer ∧
      target.contains activation.implementation = true ∧
      (∀ earlier ∈ discarded, target.contains earlier.implementation = false) ∧
      execBlock (fuel + 3) config environment pre channels
        (.mk scope (.returnFrom targetId operands origin :: rest) tail) initial =
        .escape ⟨activation.act, .nonlocal targetId⟩ carriers
          (releaseScopeState environment scope initial.nextScope before) ∧
      (releaseScopeState environment scope initial.nextScope before).construction =
        before.construction := by
  obtain ⟨_, target, discarded, outer, declared, stack, included, excluded⟩ :=
    targetActivation_selects_nearest config targetId bound bound activation selected
  refine ⟨target, discarded, outer, declared, stack, included, excluded, ?_, rfl⟩
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope
      { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope, binding, execStmts, execStmt, selected, completed,
    Goose.Construct.escaped, releaseScope, EvalM.get, EvalM.set]

#print axioms block_returnFrom_nearest_unwinds

end Goose.Proofs.ExitExecution
