import Goose.Lower.Validation.ExpressionTypingPermissions

namespace Goose.Lower.Validation.ExpressionTypingPermissionsChecks

open Goose.Core Goose.GIR

def arrayTy : Ty := .arr (.int .i64) 4

def chain : Func :=
  { name := "permissions", params := [.ref .mutable arrayTy], results := [],
    slots := #[], scopes := #[], summary := .unknown, org := none,
    blocks := #[⟨[(0, .data (.ref .mutable arrayTy))],
      [.def 1 (.refFreeze 0), .def 2 (.snapshot .borrowed 1),
        .def 3 (.refElem 2 4), .def 4 (.constInt .i64 0), .term (.ret [] none)]⟩] }

def types : Array (Option VTy) :=
  #[some (.data (.ref .mutable arrayTy)), some (.data (.ref .readOnly arrayTy)),
    some (.view .readOnly (.int .i64)), some (.data (.ref .readOnly (.int .i64))), some (.data (.int .i64))]

#guard chain.permissionRound #[] #[] types (Array.replicate 5 (true, true)) ==
  #[(true, true), (false, false), (true, true), (true, true), (false, false)]

#guard chain.permissionsFromTables #[] #[] types ==
  #[(true, true), (false, false), (false, false), (false, false), (false, false)]

theorem chain_stable :
    chain.permissionRound #[] #[] types (chain.permissionsFromTables #[] #[] types) =
      chain.permissionsFromTables #[] #[] types := permissionsFromTables_stable #[] #[] chain types

#print axioms permissionRound_descending
#print axioms permissionsFromTables_stable
#print axioms permissionsFromTables_invariant

end Goose.Lower.Validation.ExpressionTypingPermissionsChecks
