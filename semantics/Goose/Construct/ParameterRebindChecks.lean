import Goose.Construct.Validate

set_option Elab.async false

namespace Goose.Construct.ParameterRebindChecks
open Goose.Construct

def slice : Ty := .slice .readOnly (.int .i64)
def body (sample : Bool) : Block := .mk 0
  ([.rebind 0 (.read (.var 1)) 0] ++ if sample then
    [.expr (.read (.elem (.val (.read (.var 0))) (.lit .i64 0) 0)) 0] else []) none

def module (sample : Bool) (reads : List Target) : Module :=
  let entry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none,
    .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩
  let rebind : Impl := ⟨"rebind", #[⟨0, .byValue⟩, ⟨1, .byValue⟩], #[],
    #[⟨"view", slice, .mutable, 0, 0⟩, ⟨"source", slice, .immutable, 0, 0⟩], body sample,
    .known ⟨reads, [], [], [], [.param 0], [], [], [], true, false⟩⟩
  ⟨#["parameter-roots.goose"], #[.int .i64, slice], #[], #[entry, rebind],
    #[⟨0, "entry", [], [], []⟩,
      ⟨1, "rebind", [(0, [.param 0]), (1, [.param 1])], [], []⟩],
    0, #[⟨0, 17, "call"⟩], #[], #[]⟩

theorem mutable_parameter_rebind_validated : validate (module false []) = .ok () := by cbv

theorem rebound_parameter_sample_validated :
    validate (module true [.param 0, .param 1]) = .ok () := by cbv

def rejection (m : Module) : Option String := match validate m with
  | .ok _ => none
  | .error error => some error.message

def escapingLocal (inner : Bool) : Module :=
  let original := module false []
  let array : Ty := .arr (.int .i64) 1
  let localVar : LocalVar := ⟨"local", array, .immutable, if inner then 1 else 0, 0⟩
  let statements : List Stmt := [.letS 2 (.arrLit array [.lit .i64 1] 0) 0,
    .rebind 0 (.slice .readOnly (.of (.var 2)) .omitted .omitted 0) 0]
  let old := original.impls[1]'(by decide)
  let body := if inner then Block.mk 0 [.ifS (.bool true) (.mk 1 statements none) none 0] none
    else .mk 0 (statements ++ [.ret (some (.read (.var 0))) 0]) none
  let implementation := { old with
    vars := old.vars.push localVar
    body := body
    results := if inner then #[] else #[⟨slice, .register, none⟩] }
  { original with
    impls := original.impls.set! 1 implementation
    contexts := original.contexts.set! 1 { original.contexts[1]'(by decide) with resultRoots := if inner then [] else [[.param 0]] } }

def transitiveLoop : Module :=
  let original := module false []
  let old := original.impls[1]'(by decide)
  let implementation := { old with
    vars := #[⟨"view", slice, .mutable, 0, 0⟩, ⟨"middle", slice, .mutable, 0, 0⟩,
      ⟨"source", slice, .immutable, 0, 0⟩, ⟨"unused", slice, .immutable, 0, 0⟩]
    params := #[⟨0, .byValue⟩, ⟨1, .byValue⟩, ⟨2, .byValue⟩, ⟨3, .byValue⟩]
    body := .mk 0 [.while (.bool false) (.mk 1
      [.rebind 0 (.read (.var 1)) 0, .rebind 1 (.read (.var 2)) 0] none) 0,
      .expr (.read (.elem (.val (.read (.var 0))) (.lit .i64 0) 0)) 0] none
    summary := .known ⟨[.param 0, .param 1, .param 2], [], [], [], [.param 0, .param 1], [], [], [], true, false⟩ }
  { original with
    impls := original.impls.set! 1 implementation
    contexts := original.contexts.set! 1 { original.contexts[1]'(by decide) with
      varRoots := [(0, [.param 0]), (1, [.param 1]), (2, [.param 2]), (3, [.param 3])] } }

def bodyRoots (program : Module) : Option (List (Goose.Core.VarId × List RootRef)) := do
  let implementation ← program.impls[1]?
  let context ← program.contexts[1]?
  (parameterBodyRootContext program implementation context).toOption.map (·.varRoots)

theorem parameter_body_roots :
    bodyRoots (module false []) = some [(0, [.param 0, .param 1]), (1, [.param 1])] := by cbv

theorem transitive_loop_roots : bodyRoots transitiveLoop =
    some [(0, [.param 0, .param 1, .param 2]), (1, [.param 1, .param 2]),
      (2, [.param 2]), (3, [.param 3])] := by cbv

theorem transitive_loop_validated : validate transitiveLoop = .ok () := by cbv

theorem omitted_rebound_read_rejected : rejection (module true [.param 0]) =
    some "rebind reads parameter 1, which its summary omits" := by cbv

theorem inner_scope_rebind_rejected : rejection (escapingLocal true) =
    some "root local ends before view" := by cbv

theorem rebound_local_result_rejected : rejection (escapingLocal false) =
    some "a returned reference or slice is rooted at local variable 2" := by cbv

def returningRebound (declared : List RootRef) : Module :=
  let original := module false []
  let old := original.impls[1]'(by decide)
  { original with
    impls := original.impls.set! 1 { old with
      results := #[⟨slice, .register, none⟩]
      body := .mk 0 [.rebind 0 (.read (.var 1)) 0] (some (.read (.var 0))) }
    contexts := original.contexts.set! 1 { original.contexts[1]'(by decide) with resultRoots := [declared] } }

theorem rebound_result_validated : validate (returningRebound [.param 0, .param 1]) = .ok () := by cbv

theorem omitted_rebound_result_rejected : rejection (returningRebound [.param 0]) =
    some "result roots exceed declared channel roots" := by cbv

def forgedEntry : Module :=
  let original := module false []
  { original with contexts := original.contexts.set! 1 { original.contexts[1]'(by decide) with
      varRoots := [(0, [.param 0, .param 1]), (1, [.param 1])] } }

theorem forged_entry_roots_rejected : rejection forgedEntry =
    some "parameter 0 is annotated with the roots of parameter 1" := by cbv

#print axioms mutable_parameter_rebind_validated
#print axioms rebound_parameter_sample_validated
#print axioms parameter_body_roots
#print axioms transitive_loop_roots
#print axioms transitive_loop_validated
#print axioms omitted_rebound_read_rejected
#print axioms inner_scope_rebind_rejected
#print axioms rebound_local_result_rejected
#print axioms rebound_result_validated
#print axioms omitted_rebound_result_rejected
#print axioms forged_entry_roots_rejected

end Goose.Construct.ParameterRebindChecks
