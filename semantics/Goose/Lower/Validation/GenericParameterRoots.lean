import Goose.Lower.Validation.Checks

namespace Goose.Lower.Validation.GenericParameterRoots

open Goose.Core

def genericParameter : Module :=
  let base := Checks.specializedParameterSummary
  { base with contexts := base.contexts.modify 1 fun ctx =>
      { ctx with varRoots := [(0, [.param 0])] } }

def explicitRootUnion : Module :=
  { genericParameter with
    globals := genericParameter.globals.push ⟨"other", .int .i64, .mutable, .lit .i64 2, 0⟩,
    impls := genericParameter.impls.modify 0 fun impl =>
      { impl with summary := .known ⟨[.global 0, .global 1], [], [], [], [], false, true⟩ },
    contexts := genericParameter.contexts.modify 1 fun ctx =>
      { ctx with varRoots := [(0, [.param 0, .global 1])] } }

def explicitRootMismatch : Module :=
  { explicitRootUnion with
    contexts := explicitRootUnion.contexts.modify 1 fun ctx =>
      { ctx with varRoots := [(0, [.global 1])] } }

def directGlobalRead : Module :=
  { genericParameter with
    impls := genericParameter.impls.modify 1 fun impl =>
      { impl with body := .mk 0 [.print [.expr (.read (.global 0))] 0] none } }

#guard match Core.validate genericParameter with
  | .ok _ => true
  | _ => false

#guard match GIR.validate (lower genericParameter) with
  | .ok _ => true
  | _ => false

#guard match Core.validate explicitRootUnion with
  | .error rejection => rejection.rule == .call
  | _ => false

#guard match GIR.validate (lower explicitRootUnion) with
  | .ok _ => true
  | _ => false

#guard match Core.validate explicitRootMismatch with
  | .error rejection => rejection.rule == .call
  | _ => false

#guard match GIR.validate (lower explicitRootMismatch) with
  | .error rejection => rejection.code == .v050 &&
      rejection.message == "function receiver parameter 0 root info omits a root passed at a call site"
  | _ => false

#guard match Core.validate directGlobalRead with
  | .error rejection => rejection.rule == .summary
  | _ => false

#guard match GIR.validate (lower directGlobalRead) with
  | .error rejection => rejection.code == .v050 &&
      rejection.message == "function receiver: receiver reads global 0, which its summary omits"
  | _ => false

end Goose.Lower.Validation.GenericParameterRoots
