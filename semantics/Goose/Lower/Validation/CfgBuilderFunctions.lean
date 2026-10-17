import Goose.Lower.CoreToGir

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def cfg_implAction (impl : Core.Impl) : B Unit := do
  let (entry, parameters) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
  setCur (some entry)
  let pre := (impl.params.toList.zip parameters).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
  let value ← lowerBlock none pre false impl.body
  finishFunction impl value

def cfg_implState (module : Core.Module) (impl : Core.Impl) : LS :=
  (cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState).2

def cfg_globalAction (global : Core.Global) : B Unit := do
  let (entry, _) ← newBlock []
  setCur (some entry)
  let value ← lowerExpr global.init
  emitTerm (.ret [value] (some global.org))

def cfg_globalState (module : Core.Module) (global : Core.Global) : LS :=
  (cfg_globalAction global (lowerEnv module #[] [global.ty]) initState).2

theorem cfg_impl_blocks (module : Core.Module) (impl : Core.Impl) :
    (lowerImpl module impl).blocks = finishBlocks (cfg_implState module impl).blocks := rfl

theorem cfg_context_blocks (module : Core.Module) (context : Context) (impl : Core.Impl) :
    (lowerContextAt module context impl).blocks = finishBlocks (cfg_implState module impl).blocks := rfl

theorem cfg_global_blocks (module : Core.Module) (global : Core.Global) :
    (lowerGlobal module global).init.blocks = finishBlocks (cfg_globalState module global).blocks := rfl

end Goose.Lower.Validation
