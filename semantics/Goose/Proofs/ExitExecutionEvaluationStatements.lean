import Goose.Proofs.ExitExecutionEvaluationStatementCases

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem execStmt_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    PreservesFresh (execStmt (fuel + 1) config environment statement) := by
  cases statement with
  | letS x e org => exact execStmt_letS_preservesFresh_succ fuel config previous environment x e org
  | assign p e org => exact execStmt_assign_preservesFresh_succ fuel config previous environment p e org
  | assignOp op p e org => exact execStmt_assignOp_preservesFresh_succ fuel config previous environment op p e org
  | rebind x e org => exact execStmt_rebind_preservesFresh_succ fuel config previous environment x e org
  | expr e org => exact execStmt_expr_preservesFresh_succ fuel config previous environment e org
  | append p v org => exact execStmt_append_preservesFresh_succ fuel config previous environment p v org
  | popN p e org => exact execStmt_popN_preservesFresh_succ fuel config previous environment p e org
  | resize p e fill org => exact execStmt_resize_preservesFresh_succ fuel config previous environment p e fill org
  | clear p org => exact execStmt_clear_preservesFresh_succ fuel config previous environment p org
  | assignWhole p e org => exact execStmt_assignWhole_preservesFresh_succ fuel config previous environment p e org
  | ifS c a b org => exact execStmt_ifS_preservesFresh_succ fuel config previous environment c a b org
  | «while» c b org => exact execStmt_while_preservesFresh_succ fuel config previous environment c b org
  | forRange x lo hi b org => exact execStmt_forRange_preservesFresh_succ fuel config previous environment x lo hi b org
  | forEach x index v byRef b org => exact execStmt_forEach_preservesFresh_succ fuel config previous environment x index v byRef b org
  | receive vars e org => exact execStmt_receive_preservesFresh_succ fuel config previous environment vars e org
  | appendValue p e org => exact execStmt_appendValue_preservesFresh_succ fuel config previous environment p e org
  | appendConstruct p e org => exact execStmt_appendConstruct_preservesFresh_succ fuel config previous environment p e org
  | retValues es org => exact execStmt_retValues_preservesFresh_succ fuel config previous environment es org
  | retForward e org => exact execStmt_retForward_preservesFresh_succ fuel config previous environment e org
  | returnFrom target es org => exact execStmt_returnFrom_preservesFresh_succ fuel config previous environment target es org
  | returnFromForward target e org => exact execStmt_returnFromForward_preservesFresh_succ fuel config previous environment target e org
  | breakValue e org => exact execStmt_breakValue_preservesFresh_succ fuel config previous environment e org
  | ret e org => exact execStmt_ret_preservesFresh_succ fuel config previous environment e org
  | brk org => exact execStmt_brk_preservesFresh_succ fuel config previous environment org
  | cont org => exact execStmt_cont_preservesFresh_succ fuel config previous environment org
  | print args org => exact execStmt_print_preservesFresh_succ fuel config previous environment args org
  | assertS e org => exact execStmt_assertS_preservesFresh_succ fuel config previous environment e org
  | abort msg org => exact execStmt_abort_preservesFresh_succ fuel config previous environment msg org
  | exit e org => exact execStmt_exit_preservesFresh_succ fuel config previous environment e org

theorem execBlock_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesFresh (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  fresh_eval previous

theorem execResultBlockWith_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesFresh (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith, execResultScope]
  fresh_eval previous

theorem execActivationBody_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesFresh (execActivationBody (fuel + 1) config environment pre body) := by
  cases body
  simp only [execActivationBody, execResultScope]
  fresh_eval previous

theorem invokeCall_preservesFresh_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesFresh fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    PreservesFresh (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply preservesFresh_bind
  · exact stateQuery_preservesFresh _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · fresh_eval previous
    · apply preservesFresh_bind
      · fresh_eval previous
      · intro callableChannels
        apply preservesFresh_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply preservesFresh_bind
          · apply preservesFresh_listMapM
            intro channel
            cases channel <;> fresh_eval previous
          · intro renewed
            apply preservesFresh_bind
            · exact preservesFresh_get
            · intro state
              split
              · fresh_eval previous
              · apply preservesFresh_allocateActivation
                  (make := fun act => ⟨id, act, implementation.vars, [], renewed⟩)
                  (action := fun activation => do
                    let carriers ← enterActivation fuel config activation
                      ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                      implementation.body origin
                    deliverCarriers fuel config.layout channels carriers origin)
                · intro act; rfl
                · intro activation
                  fresh_eval previous

#print axioms execStmt_preservesFresh_succ

end Goose.Proofs.ExitExecution
