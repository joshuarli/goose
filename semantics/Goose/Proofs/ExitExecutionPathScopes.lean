import Goose.Proofs.ExitExecutionPathContext
import Goose.Proofs.ExitExecutionUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem blockInvocation_escape_succ_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitCallSite config (.block (fuel + 1) environment pre channels (.mk scope statements tail)) initial child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  obtain ⟨bound, before, binding, origin, released⟩ :=
    execBlock_escape_call fuel config environment pre channels scope statements tail initial final address carriers escaped
  rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
  · exact ⟨Flow, .statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements,
      bound, before,
        (.blockStatements fuel environment pre channels scope statements tail initial bound binding), fromStatements, released⟩
  · subst tail
    rcases fromTail with ⟨empty, fromValue⟩ | ⟨nonempty, fromProduce⟩
    · exact ⟨Value, .value fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression,
        middle, before,
          (.blockValueTail fuel environment pre channels scope statements expression initial bound middle value binding normal empty),
        fromValue, released⟩
    · exact ⟨List Carrier, .produce fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression,
        middle, before,
          (.blockProduceTail fuel environment pre channels scope statements expression initial bound middle value binding normal nonempty),
        fromProduce, released⟩


private theorem scopeZero_escape_impossible (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execResultScope environment pre channels (.mk scope statements tail)
      (fun localEnvironment localStatements => execStmts 0 config localEnvironment localStatements)
      tailAction initial = .escape address carriers final) : False := by
  obtain ⟨bound, before, binding, origin, released⟩ :=
    execResultScope_escape_call environment pre channels scope statements tail
      (fun localEnvironment localStatements => execStmts 0 config localEnvironment localStatements)
      tailAction initial final address carriers escaped
  rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
  · simp only [execStmts, timeout, EvalM.stop] at fromStatements
    cases fromStatements
  · simp only [execStmts, timeout, EvalM.stop] at normal
    cases normal

theorem activationScopeInvocation_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (ExitInvocation.activationScope fuel environment pre (.mk scope statements tail)).action config initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitCallSite config (.activationScope fuel environment pre (.mk scope statements tail)) initial child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  by_cases zeroFuel : fuel = 0
  · subst fuel
    exact False.elim (scopeZero_escape_impossible config environment pre environment.channels scope statements tail
      (fun localEnvironment expression => withCompletionChannels environment.channels (expressionOrigin expression)
          (fun channels => evalProduce 0 config localEnvironment channels expression)) initial final address carriers escaped)
  ·
    obtain ⟨bound, before, binding, origin, released⟩ :=
      execResultScope_escape_call environment pre environment.channels scope statements tail
        (fun localEnvironment statements => execStmts fuel config localEnvironment statements)
        (fun localEnvironment expression => withCompletionChannels environment.channels (expressionOrigin expression)
          (fun channels => evalProduce fuel config localEnvironment channels expression)) initial final address carriers escaped
    rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
    · exact ⟨Flow, .statements fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements,
        bound, before,
          (.activationStatements fuel environment pre scope statements tail initial bound binding), fromStatements, released⟩
    · subst tail
      exact ⟨List Carrier, .completionTail fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } environment.channels expression,
        middle, before,
          (.activationTail fuel environment pre scope statements expression initial bound middle value binding normal),
        fromTail, released⟩


theorem resultScopeInvocation_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements tail)).action config initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitCallSite config (.resultScope fuel environment pre channels (.mk scope statements tail)) initial child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  by_cases zeroFuel : fuel = 0
  · subst fuel
    exact False.elim (scopeZero_escape_impossible config environment pre channels scope statements tail
      (fun localEnvironment expression => evalProduce 0 config localEnvironment channels expression) initial final address carriers escaped)
  ·
    obtain ⟨bound, before, binding, origin, released⟩ :=
      execResultScope_escape_call environment pre channels scope statements tail
        (fun localEnvironment statements => execStmts fuel config localEnvironment statements)
        (fun localEnvironment expression => evalProduce fuel config localEnvironment channels expression)
        initial final address carriers escaped
    rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
    · exact ⟨Flow, .statements fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements,
        bound, before,
          (.resultStatements fuel environment pre channels scope statements tail initial bound binding), fromStatements, released⟩
    · subst tail
      exact ⟨List Carrier, .produce fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression,
        middle, before,
          (.resultTail fuel environment pre channels scope statements expression initial bound middle value binding normal),
        fromTail, released⟩


theorem blockInvocation_escape_inv (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execBlock fuel config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitCallSite config (.block fuel environment pre channels (.mk scope statements tail)) initial child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  cases fuel with
  | zero => simp only [execBlock, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      exact blockInvocation_escape_succ_inv fuel config environment pre channels scope statements tail
        initial final address carriers escaped

#print axioms blockInvocation_escape_inv
#print axioms activationScopeInvocation_escape_inv
#print axioms resultScopeInvocation_escape_inv

end Goose.Proofs.ExitExecution
