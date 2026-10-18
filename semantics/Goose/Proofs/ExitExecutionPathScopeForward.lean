import Goose.Proofs.ExitExecutionPathScopeFrames

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem execResultScope_statements_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial bound before : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (escaped : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .escape address carriers before)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier)) :
    execResultScope environment pre channels (.mk scope statements tail)
      (fun localEnvironment localStatements => execStmts fuel config localEnvironment localStatements)
      tailAction initial = .escape address carriers
        (releaseScopeState environment scope initial.nextScope before) := by
  unfold execResultScope
  have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, EvalM.get, EvalM.set, withScope]
  simp only [binding, escaped]
  simp [releaseScope, bind, EvalM.get, EvalM.set]

private theorem execResultScope_tail_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle before : ExecutionState) (value : Value)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (escaped : tailAction { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      expression middle = .escape address carriers before) :
    execResultScope environment pre channels (.mk scope statements (some expression))
      (fun localEnvironment localStatements => execStmts fuel config localEnvironment localStatements)
      tailAction initial = .escape address carriers
        (releaseScopeState environment scope initial.nextScope before) := by
  unfold execResultScope
  have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, EvalM.get, EvalM.set, withScope]
  simp only [binding, normal, escaped]
  simp [releaseScope, bind, EvalM.get, EvalM.set]

private theorem execBlock_statements_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial bound before : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (escaped : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .escape address carriers before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope]
  simp only [binding, escaped]
  simp [releaseScope, bind, EvalM.get, EvalM.set]

private theorem execBlock_valueTail_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle before : ExecutionState) (value : Value)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (empty : channels.isEmpty = true)
    (escaped : evalValue fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      expression middle = .escape address carriers before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements (some expression)) initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope]
  simp only [binding, normal]
  split <;> simp_all [releaseScope, bind, EvalM.get, EvalM.set]

private theorem execBlock_produceTail_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle before : ExecutionState) (value : Value)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (nonempty : channels.isEmpty = false)
    (escaped : evalProduce fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      channels expression middle = .escape address carriers before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements (some expression)) initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  unfold execBlock
  have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
    funext state
    rfl
  rw [fresh]
  simp only [bind, withScope]
  simp only [binding, normal]
  split <;> simp_all [releaseScope, bind, EvalM.get, EvalM.set]

theorem ExitCallSite.blockStatements_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {tail : Option Expr}
    {initial bound before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (_site : ExitCallSite config (.block (fuel + 1) environment pre channels (.mk scope statements tail))
      initial (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (escaped : ExitInvocation.action config (ExitInvocation.statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound =
      .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.block (fuel + 1) environment pre channels
      (.mk scope statements tail)) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    statements bound = .escape address carriers before at escaped
  refine ⟨_, ?_, rfl, ?_⟩
  · exact execBlock_statements_escape fuel config environment pre channels scope statements tail
      initial bound before address carriers binding escaped
  · exact .refl before.construction.storage

theorem ExitCallSite.blockValueTail_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {address : ExitAddress} {carriers : List Carrier}
    (_site : ExitCallSite config (.block (fuel + 1) environment pre channels
      (.mk scope statements (some expression))) initial
      (.value fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression) middle)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (empty : channels.isEmpty = true)
    (escaped : ExitInvocation.action config (ExitInvocation.value fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression) middle =
      .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.block (fuel + 1) environment pre channels
      (.mk scope statements (some expression))) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change evalValue fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    expression middle = .escape address carriers before at escaped
  refine ⟨_, ?_, rfl, ?_⟩
  · exact execBlock_valueTail_escape fuel config environment pre channels scope statements expression
      initial bound middle before value binding normal empty escaped
  · exact .refl before.construction.storage

theorem ExitCallSite.blockProduceTail_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {address : ExitAddress} {carriers : List Carrier}
    (_site : ExitCallSite config (.block (fuel + 1) environment pre channels
      (.mk scope statements (some expression))) initial
      (.produce fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression) middle)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      statements bound = .ok (.normal value) middle)
    (nonempty : channels.isEmpty = false)
    (escaped : ExitInvocation.action config (ExitInvocation.produce fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression) middle =
      .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.block (fuel + 1) environment pre channels
      (.mk scope statements (some expression))) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change evalProduce fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    channels expression middle = .escape address carriers before at escaped
  refine ⟨_, ?_, rfl, ?_⟩
  · exact execBlock_produceTail_escape fuel config environment pre channels scope statements expression
      initial bound middle before value binding normal nonempty escaped
  · exact .refl before.construction.storage

theorem ExitCallSite.activationStatements_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)}
    {scope : Nat} {statements : List Stmt} {tail : Option Expr}
    {initial bound before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (_site : ExitCallSite config (.activationScope fuel environment pre (.mk scope statements tail)) initial
      (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (escaped : ExitInvocation.action config (ExitInvocation.statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound =
      .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.activationScope fuel environment pre
      (.mk scope statements tail)) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    statements bound = .escape address carriers before at escaped
  have result := execResultScope_statements_escape fuel config environment pre environment.channels
    scope statements tail initial bound before address carriers binding escaped
    (fun localEnvironment expression => withCompletionChannels environment.channels
      (expressionOrigin expression) (fun completed => evalProduce fuel config localEnvironment completed expression))
  refine ⟨_, result, rfl, ?_⟩
  exact .refl before.construction.storage

theorem ExitCallSite.activationTail_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {address : ExitAddress} {carriers : List Carrier}
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
    (escaped : ExitInvocation.action config (ExitInvocation.completionTail fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      environment.channels expression) middle = .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.activationScope fuel environment pre
      (.mk scope statements (some expression))) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change withCompletionChannels environment.channels (expressionOrigin expression)
    (fun completed => evalProduce fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      completed expression) middle = .escape address carriers before at escaped
  have result := execResultScope_tail_escape fuel config environment pre environment.channels
    scope statements expression initial bound middle before value binding normal
    (fun localEnvironment expression => withCompletionChannels environment.channels
      (expressionOrigin expression) (fun completed => evalProduce fuel config localEnvironment completed expression))
    escaped
  refine ⟨_, result, rfl, ?_⟩
  exact .refl before.construction.storage

theorem ExitCallSite.resultStatements_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {tail : Option Expr}
    {initial bound before : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (_site : ExitCallSite config (.resultScope fuel environment pre channels (.mk scope statements tail)) initial
      (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (escaped : ExitInvocation.action config (ExitInvocation.statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound =
      .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.resultScope fuel environment pre channels
      (.mk scope statements tail)) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    statements bound = .escape address carriers before at escaped
  have result := execResultScope_statements_escape fuel config environment pre channels
    scope statements tail initial bound before address carriers binding escaped
    (fun localEnvironment expression => evalProduce fuel config localEnvironment channels expression)
  refine ⟨_, result, rfl, ?_⟩
  exact .refl before.construction.storage

theorem ExitCallSite.resultTail_escape_after_child {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {channels : List Channel}
    {scope : Nat} {statements : List Stmt} {expression : Expr}
    {initial bound middle before : ExecutionState} {value : Value} {address : ExitAddress} {carriers : List Carrier}
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
    (escaped : ExitInvocation.action config (ExitInvocation.produce fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
      channels expression) middle = .escape address carriers before) :
    ∃ final, ExitInvocation.action config (ExitInvocation.resultScope fuel environment pre channels
      (.mk scope statements (some expression))) initial =
      .escape address carriers final ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      CleanupStorageTrace [] before.construction.storage final.construction.storage := by
  change evalProduce fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
    channels expression middle = .escape address carriers before at escaped
  have result := execResultScope_tail_escape fuel config environment pre channels
    scope statements expression initial bound middle before value binding normal
    (fun localEnvironment expression => evalProduce fuel config localEnvironment channels expression)
    escaped
  refine ⟨_, result, rfl, ?_⟩
  exact .refl before.construction.storage

#print axioms ExitCallSite.blockStatements_escape_after_child
#print axioms ExitCallSite.blockValueTail_escape_after_child
#print axioms ExitCallSite.blockProduceTail_escape_after_child
#print axioms ExitCallSite.activationStatements_escape_after_child
#print axioms ExitCallSite.activationTail_escape_after_child
#print axioms ExitCallSite.resultStatements_escape_after_child
#print axioms ExitCallSite.resultTail_escape_after_child

end Goose.Proofs.ExitExecution
