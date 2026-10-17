import Goose.Proofs.ExitExecutionPathContext

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def ExitInvocation.rank : ExitInvocation α → Nat × Nat
  | .module _ => (2, 0)
  | .globals _ globalIds => (1, globalIds.length)
  | .activationScope fuel .. | .resultScope fuel .. => (0, 4 * fuel + 2)
  | .completionTail fuel .. => (0, 4 * fuel + 1)
  | .value fuel .. | .bound fuel .. | .place fuel .. | .view fuel ..
  | .produce fuel .. | .operands fuel .. | .build fuel .. | .element fuel .. | .arguments fuel ..
  | .call fuel .. | .activation fuel .. | .activationBody fuel .. | .resultBlock fuel ..
  | .resultBlockWith fuel .. | .block fuel .. | .statements fuel .. | .statement fuel ..
  | .printArgument fuel .. | .whileLoop fuel .. | .rangeLoop fuel .. | .eachLoop fuel ..
  | .loop fuel .. | .push fuel .. => (0, 4 * fuel)

private theorem ValueInvocationEdge.rank_lt {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : ValueInvocationEdge config caller initial child prepared) : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) child.rank caller.rank := by
  cases site <;> simp only [ExitInvocation.rank] <;> first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)

private theorem ProducerInvocationChild.rank_lt {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : ProducerInvocationChild config caller initial child prepared) : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) child.rank caller.rank := by
  cases site with
  | produce receiving body => cases body <;> simp only [ExitInvocation.rank] <;> first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)
  | build renewed body => cases body <;> simp only [ExitInvocation.rank] <;> first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)
  | elementBuild | elementValue =>
      simp only [ExitInvocation.rank]
      first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)

private theorem StatementInvocationEdge.rank_lt {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : StatementInvocationEdge config caller initial child prepared) : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) child.rank caller.rank := by
  cases site
  case globalNext =>
    simp only [ExitInvocation.rank]
    apply Prod.Lex.right
    exact Nat.lt_succ_self _
  all_goals simp only [ExitInvocation.rank]
  all_goals first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)

theorem ExitCallSite.rank_lt {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : ExitCallSite config caller initial child prepared) : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) child.rank caller.rank := by
  cases site
  case values site => exact site.rank_lt
  case producer site => exact site.rank_lt
  case statements site => exact site.rank_lt
  all_goals simp only [ExitInvocation.rank] <;> first | (apply Prod.Lex.left; omega) | (apply Prod.Lex.right; omega)

#print axioms ExitCallSite.rank_lt
end Goose.Proofs.ExitExecution
