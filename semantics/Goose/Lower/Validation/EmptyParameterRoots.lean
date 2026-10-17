import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.EmptyParameterRoots

open Goose.Core

def unusedEmptyParameter : Module :=
  let base := Checks.specializedParameterSummary
  { base with
    impls := base.impls.modify 0 (fun impl =>
        { impl with body := .mk 0 [] none, summary := .unknown })
      |>.modify 1 (fun impl =>
        { impl with summary := .known ⟨[], [], [], [], [], false, true⟩ })
    contexts := base.contexts.modify 1 fun ctx => { ctx with varRoots := [(0, [])] } }

def calledEmptyParameter : Module :=
  { unusedEmptyParameter with
    impls := unusedEmptyParameter.impls.modify 0 fun impl =>
      { impl with body := .mk 0 [.expr (.call 1 [.byRef .mutable (.global 0)] 0) 0] none } }

#guard match Core.validate unusedEmptyParameter with
  | .ok _ => true
  | _ => false

#guard match GIR.validate (lower unusedEmptyParameter) with
  | .ok _ => true
  | _ => false

#guard match Core.validate calledEmptyParameter with
  | .error rejection => rejection.rule == .call
  | _ => false

#guard match GIR.validate (lower calledEmptyParameter) with
  | .error rejection => rejection.code == .v050 &&
      rejection.message == "function receiver parameter 0 root info omits a root passed at a call site"
  | _ => false

end Goose.Lower.Validation.EmptyParameterRoots
