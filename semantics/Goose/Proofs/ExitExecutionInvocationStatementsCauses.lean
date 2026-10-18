import Goose.Proofs.ExitExecutionInvocationStatementsDefinitions

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def StatementInvocationSource : {α : Type} → ExitInvocation α → Prop
  | _, .statement _ _ statement => match statement with
    | .retValues .. | .retForward .. | .returnFrom .. | .returnFromForward .. | .breakValue .. | .ret .. => False
    | _ => True
  | _, .whileLoop .. | _, .rangeLoop .. | _, .eachLoop .. | _, .loop .. | _, .push .. | _, .globals .. => True
  | _, _ => False

def StatementCausalChild (config : EvalConfig) (parent : ExitInvocation α) (initial : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier) : Prop :=
  ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
    StatementInvocationEdge config parent initial child prepared ∧
      child.action config prepared = .escape address carriers before

end Goose.Proofs.ExitExecution
