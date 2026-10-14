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

end Goose.Lower.CallChecks
