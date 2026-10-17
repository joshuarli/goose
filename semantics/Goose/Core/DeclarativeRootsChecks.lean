import Goose.Core.DeclarativeRoots

namespace Goose.Core.Declarative
open Goose.Core

private def noEffects : Summary := ⟨[], [], [], [], [], false, false⟩
private def ownerImpl : Impl :=
  ⟨"roots", #[], #[],
    #[⟨"owner", .grow (.int .i64), .mutable, 0, 0⟩,
      ⟨"reference", .ref .mutable (.int .i64), .mutable, 0, 0⟩],
    .mk 0 [] none, .known noEffects⟩
private def forgedContext : Context := ⟨0, "forged", [(1, [.local 1])], [], []⟩
private def rootModule : Module := ⟨#[], #[], #[], #[ownerImpl], #[forgedContext], 0, #[], .pilot, #[]⟩

example : ¬ ContextRoots rootModule ownerImpl forgedContext := by
  intro h
  obtain ⟨lv, _, _, roots⟩ := h.annotations.1 1 [.local 1] (by simp [forgedContext])
  have forged := roots (.local 1) (by simp)
  simp [RootDeclared, ownerImpl, Ty.isRefLike] at forged

example : ¬ SummaryContains rootModule ownerImpl forgedContext { shrinks := [.global 0] } := by
  intro h
  obtain ⟨_, _, _, _, _, shrinks, _, _, _⟩ := h noEffects rfl
  have missing := shrinks (.global 0) (by simp)
  simp [expandTargets, noEffects] at missing

example : ¬ SummaryContains rootModule ownerImpl forgedContext { rebinds := [.param 0] } := by
  intro h
  obtain ⟨_, _, _, _, _, _, rebinds, _, _⟩ := h noEffects rfl
  have missing := rebinds (.param 0) (by simp)
  simp [noEffects] at missing

example : ¬ SummaryContains rootModule ownerImpl forgedContext { aborts := true } := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, aborts, _⟩ := h noEffects rfl
  have missing := aborts rfl
  simp [noEffects] at missing

example : ¬ SummaryContains rootModule ownerImpl forgedContext { outputs := true } := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, outputs⟩ := h noEffects rfl
  have missing := outputs rfl
  simp [noEffects] at missing

example : ¬ BindRoots ⟨rootModule, ownerImpl, forgedContext, [0]⟩ [0] 1 [.local 0] := by
  intro h
  obtain ⟨lv, ann, _, ha, subset, _⟩ := h
  have annotation : ann = [.local 1] := by
    simpa [PEnv.ann, forgedContext] using ha.symm
  subst ann
  have missing := subset (.local 0) (by simp)
  simp at missing

example : ¬ ResultRoots ⟨rootModule, ownerImpl, forgedContext, []⟩ [.local 0] := by
  intro h
  exact h.1 0 (by simp)

example : ¬ BlockRoots 0 2 [.local 1] := by
  intro h
  exact h 1 (by simp) (by decide)

example : RootExpr ⟨rootModule, ownerImpl, forgedContext, []⟩ (.pop (.global 0) 0)
    ⟨0, {}⟩ [] ⟨0, { reads := [.global 0], shrinks := [.global 0], aborts := true }⟩ := by
  exact ⟨_, _, ⟨rfl, rfl⟩, _, (), rfl, _, (), rfl, _, (), rfl, rfl, rfl⟩

#print axioms root_syntax_sound
#print axioms contextRoots_sound
#print axioms globalRoots_sound
#print axioms accepted_contextRoots
#print axioms accepted_globalRoots

end Goose.Core.Declarative
