import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem neverEscapes_enclosingActivation (environment : RuntimeActivation) :
    ProducerNeverEscapes (enclosingActivation environment) := by
  unfold enclosingActivation
  producer_never_escapes_base

private theorem enclosing_return_escape_origin (environment : RuntimeActivation)
    (action : RuntimeActivation → EvalM (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : ((do
      let activation ← enclosingActivation environment
      returned activation.act (← action activation)) : EvalM Flow) initial = .escape address carriers final) :
    ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
      (action activation initial = .escape address carriers final ∨
        (action activation initial = .ok carriers final ∧ address = ⟨activation.act, .ordinary⟩)) := by
  cases selected : enclosingActivation environment initial with
  | stop reason after | jump target kind after => simp only [bind, selected] at escaped; cases escaped
  | escape target payload after => exact False.elim (neverEscapes_enclosingActivation _ _ _ _ _ selected)
  | ok activation after =>
      have unchanged := stateQuery_enclosingActivation environment initial
      rw [selected] at unchanged
      change after = initial at unchanged
      subst after
      cases evaluated : action activation initial with
      | stop reason after | jump target kind after => simp only [bind, selected, evaluated] at escaped; cases escaped
      | escape target payload after =>
          simp only [bind, selected, evaluated] at escaped
          cases escaped
          exact ⟨activation, rfl, Or.inl evaluated⟩
      | ok payload after =>
          simp only [bind, selected, evaluated, returned] at escaped
          cases escaped
          exact ⟨activation, rfl, Or.inr ⟨evaluated, rfl⟩⟩

theorem returnValuesInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operands : List Expr) (origin : Goose.Core.OriginId) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.retValues operands origin) initial = .escape address carriers final) :
    ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
      (withExitChannels environment activation operands origin
          (fun channels => evalOperands fuel config environment channels operands) initial = .escape address carriers final ∨
       (withExitChannels environment activation operands origin
          (fun channels => evalOperands fuel config environment channels operands) initial = .ok carriers final ∧
        address = ⟨activation.act, .ordinary⟩)) := by
  apply enclosing_return_escape_origin environment _ initial final address carriers
  simpa only [execStmt] using escaped

theorem returnForwardInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (producer : Expr) (origin : Goose.Core.OriginId) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.retForward producer origin) initial = .escape address carriers final) :
    ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
      (withExitChannels environment activation (List.replicate activation.channels.length producer) origin
          (fun channels => evalProduce fuel config environment channels producer) initial = .escape address carriers final ∨
       (withExitChannels environment activation (List.replicate activation.channels.length producer) origin
          (fun channels => evalProduce fuel config environment channels producer) initial = .ok carriers final ∧
        address = ⟨activation.act, .ordinary⟩)) := by
  apply enclosing_return_escape_origin environment _ initial final address carriers
  simpa only [execStmt] using escaped

theorem returnProduceInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (producer : Expr) (origin : Goose.Core.OriginId) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.ret (some producer) origin) initial = .escape address carriers final) :
    ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
      let operands := match (generalizing := false) producer with | .values operands => operands | _ => List.replicate activation.channels.length producer
      (withExitChannels environment activation operands origin
          (fun channels => evalProduce fuel config environment channels producer) initial = .escape address carriers final ∨
       (withExitChannels environment activation operands origin
          (fun channels => evalProduce fuel config environment channels producer) initial = .ok carriers final ∧
        address = ⟨activation.act, .ordinary⟩)) := by
  cases producer <;> apply enclosing_return_escape_origin environment _ initial final address carriers <;>
    simpa only [execStmt] using escaped

private theorem jump_escape_origin (action : EvalM (List Carrier)) (target : Nat)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (action >>= fun values => (jump target (.breakValue values) : EvalM Flow)) initial =
      .escape address carriers final) : action initial = .escape address carriers final := by
  cases result : action initial with
  | stop reason after | jump target kind after | ok values after =>
      simp only [bind, result, jump] at escaped
      cases escaped
  | escape target payload after =>
      simp only [bind, result] at escaped
      cases escaped
      rfl

theorem breakProduceInvocation_escape_inv (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (producer : Expr) (origin : Goose.Core.OriginId) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.breakValue producer origin) initial = .escape address carriers final) :
    ∃ target, currentBreak environment.act (some .block) initial = .ok target initial ∧
      let activation := { environment with channels := target.channels }
      let operands := match (generalizing := false) producer with
        | .values operands => operands | _ => List.replicate activation.channels.length producer
      withExitChannels environment activation operands origin
        (fun channels => evalProduce fuel config environment channels producer) initial = .escape address carriers final := by
  have safe : ProducerNeverEscapes (currentBreak environment.act (some .block)) := by
    unfold currentBreak
    producer_never_escapes_base
  simp only [execStmt] at escaped
  cases selected : currentBreak environment.act (some .block) initial with
  | stop reason after | jump target kind after => simp only [bind, selected] at escaped; cases escaped
  | escape target payload after => exact False.elim (safe _ _ _ _ selected)
  | ok target after =>
      have unchanged := stateQuery_currentBreak environment.act (some .block) initial
      rw [selected] at unchanged
      change after = initial at unchanged
      subst after
      refine ⟨target, rfl, ?_⟩
      dsimp only
      cases producer <;> apply jump_escape_origin _ target.id initial final address carriers <;>
        simpa only [bind, selected] using escaped

#print axioms breakProduceInvocation_escape_inv

#print axioms returnValuesInvocation_escape_inv
#print axioms returnForwardInvocation_escape_inv
#print axioms returnProduceInvocation_escape_inv
end Goose.Proofs.ExitExecution
