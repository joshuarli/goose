import Goose.Proofs.ExitExecutionPathScopeForward

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem execBlock_statements_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial bound before : ExecutionState) (reason : Goose.Core.Stop)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (stopped : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .stop reason before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .stop reason before := by
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope
      { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope]
  simp only [binding, stopped]

private theorem execBlock_valueTail_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle : ExecutionState) (value : Value) (reason : Goose.Core.Stop)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (empty : channels.isEmpty = true)
    (stopped : evalValue fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      expression middle = .stop reason before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements (some expression)) initial =
      .stop reason before := by
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope
      { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope]
  simp only [binding, normal, empty, ite_true, stopped]

private theorem execBlock_produceTail_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle : ExecutionState) (value : Value) (reason : Goose.Core.Stop)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (nonempty : channels.isEmpty = false)
    (stopped : evalProduce fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      channels expression middle = .stop reason before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements (some expression)) initial =
      .stop reason before := by
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope
      { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope]
  simp only [binding, normal, nonempty, Bool.false_eq_true, ite_false, stopped]

private theorem execResultScope_statements_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial bound before : ExecutionState) (reason : Goose.Core.Stop)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (stopped : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .stop reason before)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier)) :
    execResultScope environment pre channels (.mk scope statements tail)
      (fun localEnvironment localStatements => execStmts fuel config localEnvironment localStatements)
      tailAction initial = .stop reason before := by
  unfold execResultScope
  have fresh : freshScope = fun state => .ok state.nextScope
      { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, EvalM.get, EvalM.set, withScope]
  simp only [binding, stopped]

private theorem execResultScope_tail_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle : ExecutionState) (value : Value) (reason : Goose.Core.Stop)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (stopped : tailAction { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      expression middle = .stop reason before) :
    execResultScope environment pre channels (.mk scope statements (some expression))
      (fun localEnvironment localStatements => execStmts fuel config localEnvironment localStatements)
      tailAction initial = .stop reason before := by
  unfold execResultScope
  have fresh : freshScope = fun state => .ok state.nextScope
      { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, EvalM.get, EvalM.set, withScope]
  simp only [binding, normal, stopped]

theorem ExitCallSite.blockStatements_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {tail : Option Expr}
    {initial bound before : ExecutionState} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.block (fuel + 1) environment pre channels (.mk scope statements tail))
      initial (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (stopped : ExitInvocation.action config (ExitInvocation.statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound =
      .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.block (fuel + 1) environment pre channels (.mk scope statements tail)) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    statements bound = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execBlock_statements_stop fuel config environment pre channels scope statements tail
    initial bound before reason binding stopped

theorem ExitCallSite.blockValueTail_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.block (fuel + 1) environment pre channels
      (.mk scope statements (some expression))) initial
      (.value fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression) middle)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (empty : channels.isEmpty = true)
    (stopped : ExitInvocation.action config (ExitInvocation.value fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression) middle =
      .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.block (fuel + 1) environment pre channels (.mk scope statements (some expression))) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change evalValue fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    expression middle = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execBlock_valueTail_stop fuel config environment pre channels scope statements expression
    initial bound middle value reason binding normal empty stopped

theorem ExitCallSite.blockProduceTail_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.block (fuel + 1) environment pre channels
      (.mk scope statements (some expression))) initial
      (.produce fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression) middle)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (nonempty : channels.isEmpty = false)
    (stopped : ExitInvocation.action config (ExitInvocation.produce fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      channels expression) middle = .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.block (fuel + 1) environment pre channels (.mk scope statements (some expression))) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change evalProduce fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    channels expression middle = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execBlock_produceTail_stop fuel config environment pre channels scope statements expression
    initial bound middle value reason binding normal nonempty stopped

theorem ExitCallSite.activationStatements_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)}
    {scope : Nat} {statements : List Stmt} {tail : Option Expr}
    {initial bound before : ExecutionState} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.activationScope fuel environment pre (.mk scope statements tail)) initial
      (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (stopped : ExitInvocation.action config (ExitInvocation.statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound =
      .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.activationScope fuel environment pre (.mk scope statements tail)) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    statements bound = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execResultScope_statements_stop fuel config environment pre environment.channels scope statements tail
    initial bound before reason binding stopped
    (fun localEnvironment expression => withCompletionChannels environment.channels
      (expressionOrigin expression) (fun completed => evalProduce fuel config localEnvironment completed expression))

theorem ExitCallSite.activationTail_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.activationScope fuel environment pre
      (.mk scope statements (some expression))) initial
      (.completionTail fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        environment.channels expression) middle)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (stopped : ExitInvocation.action config (ExitInvocation.completionTail fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      environment.channels expression) middle = .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.activationScope fuel environment pre (.mk scope statements (some expression))) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change withCompletionChannels environment.channels (expressionOrigin expression)
    (fun completed => evalProduce fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      completed expression) middle = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execResultScope_tail_stop fuel config environment pre environment.channels scope statements expression
    initial bound middle value reason binding normal
    (fun localEnvironment expression => withCompletionChannels environment.channels
      (expressionOrigin expression) (fun completed => evalProduce fuel config localEnvironment completed expression))
    stopped

theorem ExitCallSite.resultStatements_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {tail : Option Expr}
    {initial bound before : ExecutionState} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.resultScope fuel environment pre channels (.mk scope statements tail)) initial
      (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (stopped : ExitInvocation.action config (ExitInvocation.statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound =
      .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements tail)) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    statements bound = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execResultScope_statements_stop fuel config environment pre channels scope statements tail
    initial bound before reason binding stopped
    (fun localEnvironment expression => evalProduce fuel config localEnvironment channels expression)

theorem ExitCallSite.resultTail_stop_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {reason : Goose.Core.Stop}
    (_site : ExitCallSite config (.resultScope fuel environment pre channels
      (.mk scope statements (some expression))) initial
      (.produce fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression) middle)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (stopped : ExitInvocation.action config (ExitInvocation.produce fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      channels expression) middle = .stop reason before) :
    ∃ finalReason final, ExitInvocation.action config
      (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements (some expression))) initial =
        .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change evalProduce fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    channels expression middle = .stop reason before at stopped
  refine ⟨reason, before, ?_, rfl, rfl, .refl _⟩
  exact execResultScope_tail_stop fuel config environment pre channels scope statements expression
    initial bound middle value reason binding normal
    (fun localEnvironment expression => evalProduce fuel config localEnvironment channels expression)
    stopped

#print axioms ExitCallSite.blockStatements_stop_after_child
#print axioms ExitCallSite.blockValueTail_stop_after_child
#print axioms ExitCallSite.blockProduceTail_stop_after_child
#print axioms ExitCallSite.activationStatements_stop_after_child
#print axioms ExitCallSite.activationTail_stop_after_child
#print axioms ExitCallSite.resultStatements_stop_after_child
#print axioms ExitCallSite.resultTail_stop_after_child

end Goose.Proofs.ExitExecution
