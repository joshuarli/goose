import Goose.Core.Construction
import Goose.Core.Eval

namespace Goose.Construct
open Goose.Core

structure ExitPlan where
  discarded : List Activation
  catcher : Activation
  outer : List Activation

def planExit? (target : NonlocalTarget) : List Activation → Option ExitPlan
  | [] => none
  | activation :: outer =>
      if target.contains activation.implementation then
        some ⟨[], activation, outer⟩
      else
        (planExit? target outer).map fun plan =>
          { plan with discarded := activation :: plan.discarded }

def releaseActivation (activation : Activation) (store : Store) : Store :=
  activation.scopes.foldl (fun current (scope, scopeInst) =>
    releaseVars activation.vars activation.act scope scopeInst activation.vars.size current) store

def unwindStore (plan : ExitPlan) (store : Store) : Store :=
  releaseActivation plan.catcher (plan.discarded.foldl (fun current activation =>
    releaseActivation activation current) store)

def unwindState (plan : ExitPlan) (state : St) : St :=
  { state with store := unwindStore plan state.store }

end Goose.Construct
