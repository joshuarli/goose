import Goose.Lower.Unwind
import Goose.Proofs.Lower

namespace Goose.Lower.UnwindChecks

open Goose.Core Goose.GIR

def variables : Array LocalVar := #[⟨"x", .int .i64, .mutable, 1, 0⟩]

def scopedBuilder : LS :=
  { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [1, 0] }

def beforeFrame : GIR.Frame := ⟨0, [(1, 11), (0, 10)], {}, 0⟩

def beforeEnv : Env := ⟨variables, 0, [(1, 11), (0, 10)], 0⟩

def finishedBuilder (m : Core.Module) : LS :=
  (leaveTo 0 (lowerEnv m variables []) scopedBuilder).2

def scopeFunction : Func :=
  { name := "unwind", params := [], results := [],
    slots := variables.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩,
    scopes := #[none, some 0], blocks := #[], summary := .unknown, org := none }

def unwindFunction (m : Core.Module) : Func :=
  { scopeFunction with blocks := finishBlocks (finishedBuilder m).blocks }

theorem concrete_full_unwind (cfg : Cfg) :
    SimG ⟨⟨cfg.profile, lower cfg.mod⟩, unwindFunction cfg.mod⟩ (0, 0) beforeFrame
      (releaseScopes beforeEnv [(1, 11), (0, 10)])
      (fun _ pt' fr' => UnwindPost scopedBuilder beforeFrame (finishedBuilder cfg.mod)
        fr' [] pt') := by
  apply leaveTo_sim cfg beforeEnv ⟨⟨cfg.profile, lower cfg.mod⟩, unwindFunction cfg.mod⟩
    (lowerEnv cfg.mod variables []) 0 scopedBuilder (finishedBuilder cfg.mod) () (0, 0) beforeFrame
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  · rfl
  · exact Goose.Proofs.Lower.extT_finish (finishedBuilder cfg.mod)

def localState : St :=
  ⟨Store.empty.introduce (.local 0 11 0) (.int .i64 9), "", 1, 12⟩

def unwindResult : Res GIR.Frame :=
  (execEff scopeFunction beforeFrame (.leave 1) >>= fun frame =>
    execEff scopeFunction frame (.leave 0)) localState

#guard match unwindResult with
  | .ok frame state => frame.scopes.isEmpty && (state.store.roots[RootInst.local 0 11 0]?).isNone
  | .stop _ _ => false

end Goose.Lower.UnwindChecks
