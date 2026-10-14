import Goose.Construct.GIR.Eval
import Goose.Construct.GIR.Validate
import Goose.Construct.TraceJson

namespace Goose.Construct.GIR.Run
open Goose.Core (NumProfile)

private def initGlobals : Nat → Config → List Nat → EvalM Unit
  | 0, _, _ => timeout
  | _ + 1, _, [] => pure ()
  | fuel + 1, config, globalId :: rest => do
      let some global := config.module.globals[globalId]? | fault .unbound
      let storage ← reserveRootObject (.global globalId)
      let destinations ← if global.ty.nonfixed then do
          let request := match global.init.results.head?.map (·.request) with
            | some .elementRun => Core.ConstructionRequest.elementRun
            | _ => .value
          let capability : Core.Destination Ty :=
            ⟨0, ⟨.global globalId,[]⟩, global.ty, global.ty, request, 0, 0⟩
          let id ← liftConstruction global.org (openDestination storage capability (← receivingLayout config.layout global.ty) none)
          pure [id]
        else pure []
      let results ← executeFunction fuel config (config.module.funcs.size + globalId) global.init [] destinations global.org
      match results with
      | [.register value] => bindRoot (.global globalId) value
      | [.completed id] =>
          liftConstruction global.org (publishOperation [id])
          bindRoot (.global globalId) (.stored { (← storedDestination id) with object := some storage })
      | _ => fault .arity
      initGlobals fuel config rest

private def runModule (fuel : Nat) (config : Config) : EvalM Unit := do
  initGlobals fuel config (List.range config.module.globals.size)
  let results ← executeFn fuel config config.module.entry [] [] 0
  unless results.isEmpty do fault .arity

def run (fuel : Nat) (profile : NumProfile) (module : Module) : ExecutionResult :=
  match runModule fuel ⟨module, profile⟩ .initial with
  | .ok () state => .done .returned state.construction.stdout state.construction.events
  | .stop (.abort kind origin) state => .done (.aborted kind origin) state.construction.stdout state.construction.events
  | .stop (.exit code) state => .done (.exited code) state.construction.stdout state.construction.events
  | .stop .timeout state => .timeout state.construction.stdout state.construction.events
  | .stop (.fault kind) _ => .fault kind
  | .escape _ _ _ | .jump _ _ _ => .fault .flow

end Goose.Construct.GIR.Run
