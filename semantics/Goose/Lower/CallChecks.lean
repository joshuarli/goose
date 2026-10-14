import Goose.Lower.Call

namespace Goose.Lower.CallChecks

open Goose.Core Goose.GIR

def variables : Array LocalVar := #[⟨"x", .int .i64, .mutable, 0, 0⟩]

def arguments : List Arg :=
  [.byVal (.bool true), .byRef .readOnly (.var 0), .byVal (.bool false)]

def initialBuilder : LS :=
  { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [0] }

def source : Core.Module :=
  let first : Impl :=
    { name := "first", params := #[], results := #[.int .i64], vars := #[],
      body := .mk 0 [] (some (.lit .i64 7)), summary := .unknown }
  let second : Impl :=
    { name := "second", params := #[], results := #[.int .i64], vars := #[],
      body := .mk 0 [] (some (.lit .i64 9)), summary := .unknown }
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [] none, summary := .unknown }
  { files := #["calls.goose"], types := #[.int .i64], globals := #[],
    impls := #[first, second, main], contexts := #[⟨1, "second", [], [[]], []⟩,
      ⟨0, "first", [], [[]], []⟩, ⟨2, "main", [], [], []⟩], entry := 2,
    origins := #[⟨0, 1, "calls"⟩] }

def argumentBuilder : LS :=
  (lowerArgs arguments (lowerEnv source variables) initialBuilder).2

def argumentFunction : Func :=
  { name := "arguments", params := [], results := [],
    slots := (lowerEnv source variables).slots, scopes := #[none],
    blocks := finishBlocks argumentBuilder.blocks, summary := .unknown, org := none }

theorem concrete_arguments (n : Nat) : ArgsClaim n arguments := by
  apply argsClaim
  intro a ha
  simp [arguments] at ha
  rcases ha with rfl | rfl | rfl
  · cases n with
    | zero => exact argClaim_zero _
    | succ n => exact argClaim_byVal ((claims n).expr _ rfl)
  · cases n with
    | zero => exact argClaim_zero _
    | succ n => exact argClaim_byRef ((claims n).place _ rfl) _
  · cases n with
    | zero => exact argClaim_zero _
    | succ n => exact argClaim_byVal ((claims n).expr _ rfl)

theorem concrete_argument_cells (n : Nat) (profile : NumProfile) :
    SimG ⟨⟨profile, lower source⟩, argumentFunction⟩ (0, 0) ⟨0, [(0, 11)], {}, 0⟩
      (mapList (evalArg n ⟨profile, source⟩ ⟨variables, 0, [(0, 11)], 0⟩) arguments)
      (fun vals pt frame => [0, 2, 3].length = vals.length ∧
        Post ⟨profile, source⟩ ⟨variables, 0, [(0, 11)], 0⟩
          ⟨⟨profile, lower source⟩, argumentFunction⟩ initialBuilder ⟨0, [(0, 11)], {}, 0⟩
          argumentBuilder frame pt (cellsOf [0, 2, 3] vals)) := by
  apply concrete_arguments n (lowerEnv source variables) initialBuilder [0, 2, 3]
    argumentBuilder (0, 0) ⟨profile, source⟩ ⟨variables, 0, [(0, 11)], 0⟩
    ⟨⟨profile, lower source⟩, argumentFunction⟩ ⟨0, [(0, 11)], {}, 0⟩
  · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish argumentBuilder
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem concrete_callee (profile : NumProfile) (n : Nat) :
    CalleeCallClaim n ⟨profile, source⟩ 0 :=
  calleeCallClaim_nil (ctx := ⟨1, "second", [], [[]], []⟩)
    (impl := source.impls[1]) rfl rfl rfl rfl profile n

theorem concrete_call_expression (profile : NumProfile) (n : Nat) :
    ExprEClaim n ⟨profile, source⟩ (.call 0 [] 0) := by
  cases n with
  | zero => exact exprEClaim_zero _ _
  | succ n => exact exprEClaim_call (argsEClaim [] (by simp)) (concrete_callee profile n)

theorem concrete_nested_call_arguments (profile : NumProfile) (n : Nat) :
    ArgsEClaim n ⟨profile, source⟩ [.byVal (.call 0 [] 0), .byVal (.bool true)] := by
  apply argsEClaim
  intro a ha
  simp at ha
  rcases ha with rfl | rfl
  · cases n with
    | zero => exact argEClaim_zero _ _
    | succ n => exact argEClaim_byVal (concrete_call_expression profile n)
  · cases n with
    | zero => exact argEClaim_zero _ _
    | succ n => exact argEClaim_byVal (ExprLowerClaim.toEventual ((claims n).expr (.bool true) rfl))

def referenceCallee : Impl :=
  { name := "reference", params := #[⟨0, .byRef⟩], results := #[.int .i64],
    vars := #[⟨"p", .ref .readOnly (.int .i64), .immutable, 0, 0⟩],
    body := .mk 0 [.ret (some (.read (.deref (.read (.var 0))))) 0] none,
    summary := .unknown }

def referenceSource : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := variables,
      body := .mk 0 [.letS 0 (.lit .i64 42) 0,
        .expr (.call 0 [.byRef .readOnly (.var 0)] 0) 0] none, summary := .unknown }
  { files := #["reference.goose"], types := #[.int .i64, .ref .readOnly (.int .i64)],
    globals := #[], impls := #[referenceCallee, main],
    contexts := #[⟨0, "reference", [(0, [.param 0])], [[]], []⟩,
      ⟨1, "main", [], [], []⟩], entry := 1, origins := #[⟨0, 1, "reference"⟩] }

theorem concrete_reference_callee (profile : NumProfile) (n : Nat) :
    CalleeCallClaim n ⟨profile, referenceSource⟩ 0 :=
  calleeCallClaim_flow (ctx := ⟨0, "reference", [(0, [.param 0])], [[]], []⟩)
    (impl := referenceCallee) rfl rfl rfl rfl profile n

theorem concrete_reference_argument (profile : NumProfile) (n : Nat) :
    ArgsEClaim n ⟨profile, referenceSource⟩ [.byRef .readOnly (.var 0)] := by
  apply argsEClaim
  intro arg harg
  simp only [List.mem_singleton] at harg
  subst arg
  cases n with
  | zero => exact argEClaim_zero _ _
  | succ n =>
    exact argEClaim_byRef (PlaceLowerClaim.toEventual ((claims n).place (.var 0) rfl)) _

theorem concrete_reference_call_expression (profile : NumProfile) (n : Nat) :
    ExprEClaim n ⟨profile, referenceSource⟩ (.call 0 [.byRef .readOnly (.var 0)] 0) := by
  cases n with
  | zero => exact exprEClaim_zero _ _
  | succ n =>
    exact exprEClaim_call (concrete_reference_argument profile n) (concrete_reference_callee profile n)

def abortCallee : Impl :=
  { name := "abort", params := #[], results := #[], vars := #[],
    body := .mk 0 [.abort "stop" 0] none, summary := .unknown }

def abortSource : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[], vars := #[],
      body := .mk 0 [.expr (.call 0 [] 0) 0] none, summary := .unknown }
  { files := #["abort.goose"], types := #[], globals := #[], impls := #[abortCallee, main],
    contexts := #[⟨0, "abort", [], [], []⟩, ⟨1, "main", [], [], []⟩],
    entry := 1, origins := #[⟨0, 1, "abort"⟩] }

theorem concrete_noReturn_call_expression (profile : NumProfile) (n : Nat) :
    ExprEClaim n ⟨profile, abortSource⟩ (.call 0 [] 0) := by
  cases n with
  | zero => exact exprEClaim_zero _ _
  | succ n =>
    exact exprEClaim_call (argsEClaim [] (by simp))
      (calleeCallClaim_flow (ctx := ⟨0, "abort", [], [], []⟩)
        (impl := abortCallee) rfl rfl rfl rfl profile n)

#guard (lowerArgs arguments (lowerEnv source variables) initialBuilder).1 == [0, 2, 3]
#guard match Option.map (fun (block : BlockB) => block.insts.toList) argumentBuilder.blocks[0]? with
  | some [Inst.def 0 (.constBool true), .def 1 (.slotAddr 0), .def 2 (.refFreeze 1),
      Inst.def 3 (.constBool false)] => true
  | _ => false

#guard match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  match enterCall 20 ⟨profile, source⟩ 4 0 [] St.initial,
      callFn 30 ⟨profile, lower source⟩ 4 1 [] St.initial with
  | .ok (.int .i64 9) coreState, .ok (.int .i64 9) girState =>
    coreState.trace == girState.trace && coreState.nextAct == girState.nextAct &&
      coreState.nextScope == girState.nextScope &&
      coreState.store.roots.isEmpty && girState.store.roots.isEmpty
  | _, _ => false

#guard match Core.validate referenceSource, GIR.validate (lower referenceSource) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 80 profile referenceSource, GIR.run 160 profile (lower referenceSource) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

#guard abortSource.noReturn 0
#guard match Core.validate abortSource, GIR.validate (lower abortSource) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 80 profile abortSource, GIR.run 160 profile (lower abortSource) with
  | .done (.aborted coreKind coreOrigin) coreTrace,
      .done (.aborted girKind girOrigin) girTrace =>
    coreKind == girKind && coreOrigin == girOrigin && coreTrace == girTrace
  | _, _ => false

end Goose.Lower.CallChecks
