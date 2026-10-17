import Lake
import Lake.Load.Workspace

open Lake

def main (args : List String) : IO UInt32 := do
  let root :: config :: modules := args
    | throw <| IO.userError "expected semantics root, Lake config, and ordered modules"
  let (elan, some lean, some lake) ← findInstall?
    | throw <| IO.userError "Lean and Lake installations could not be found"
  let env ← (Env.compute lake lean elan).toIO IO.userError
  let some ws ← (loadWorkspace {
      lakeEnv := env, wsDir := root, relConfigFile := config
    }).toBaseIO
    | throw <| IO.userError "Lake workspace loading failed"
  let out ← IO.getStdout
  let total := modules.length
  ws.runFetchM (do
    for (module, index) in modules.zipIdx do
      out.putStrLn s!"[{index + 1}/{total}] +{module}:olean"
      out.flush
      let some mod := ws.findModule? module.toName
        | error s!"Lake module not found: {module}"
      discard <| (← mod.olean.fetch).await
      out.putStrLn s!"built +{module}:olean"
      out.flush
  ) {trustHash := false, verbosity := .verbose}
  return 0
