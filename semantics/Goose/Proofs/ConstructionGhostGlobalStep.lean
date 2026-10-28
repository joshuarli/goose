import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionGhostGlobalStep
open Goose.Construct

theorem evalM_bind_assoc (action : EvalM α) (next : α → EvalM β) (last : β → EvalM γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext state
  simp only [bind]
  cases action state <;> rfl

def globalInitializer (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId) : EvalM Unit := do
  let some descriptor := config.module.globals[global]? | fault .unbound
  let act ← freshAct
  let environment : RuntimeActivation := ⟨0, act, #[], [], []⟩
  let value ← if descriptor.ty.nonfixed then
    let materialized ← materializeProducer fuel ⟨config.module, environment.vars⟩ descriptor.init
      (evalValue fuel config environment descriptor.init)
    let carrier ← match materialized with
      | some values => do
          let destination ← materializedDestination fuel config.layout act descriptor.ty descriptor.org values.size (.fixed values)
          publishCarriers descriptor.org [.completed destination]
          pure (.completed destination)
      | none =>
          constructLocal ⟨config.module, environment.vars⟩ act descriptor.ty descriptor.org descriptor.init
            (fun destination => buildExpr fuel config environment destination descriptor.init)
    carrierValue carrier
  else evalValue fuel config environment descriptor.init
  bindRoot (.global global) value

theorem initGlobals_step (fuel : Nat) (config : EvalConfig) (global : Goose.Core.GlobalId)
    (rest : List Goose.Core.GlobalId) :
    initGlobals fuel config (global :: rest) =
      (globalInitializer fuel config global >>= fun _ => initGlobals fuel config rest) := by
  funext before
  simp only [initGlobals, globalInitializer, bind]
  cases found : config.module.globals[global]? <;> simp only [found, fault, EvalM.stop]
  all_goals repeat' (split <;> try simp_all [bind, pure, EvalM.stop])

#print axioms evalM_bind_assoc
#print axioms initGlobals_step
end Goose.Proofs.ConstructionGhostGlobalStep
