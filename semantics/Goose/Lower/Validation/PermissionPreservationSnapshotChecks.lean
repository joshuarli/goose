import Goose.Lower.Validation.PermissionPreservationSnapshots

namespace Goose.Lower.Validation.PermissionSnapshotChecks

open Goose.Core Goose.GIR

private def module : Core.Module :=
  { files := #[], types := #[], globals := #[], impls := #[], contexts := #[], entry := 0, origins := #[] }

private def env : Core.TEnv :=
  { mod := module, impl := none, vars := #[⟨"array", .arr (.int .i64) 1, .immutable, 0, 0⟩],
    visible := [0], loops := 0, inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

private def place : Place := .deref (.ref .readOnly (.var 0))

private def initial : LS := ⟨#[⟨[], #[]⟩], #[], some 0, [], #[]⟩

private theorem generated : GeneratedBuilderState initial := by
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · intro block current
    have same : block = 0 := Option.some.inj current.symm
    subst block
    decide
  · intro index body row target member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    have same : index = 0 := by change index < 1 at bound; nat_omega
    subst index
    simp [initial] at row
    subst body
    simp [cfgBlock, GIR.Block.terms] at member

private def ownerState : LS := (lowerPlace place (lowerEnv module env.vars []) initial).2

private def finalState : LS := (lowerView (.of place) (lowerEnv module env.vars []) initial).2

private def site : SnapshotSourceSite (lowerEnv module env.vars []) 1 .borrowed 0 :=
  { typingEnv := env, results := [], place := place,
    info := ⟨.arr (.int .i64) 1, false, false⟩, start := 0, finish := 0,
    beforePlace := initial, ownerState := ownerState, emittedState := finalState,
    aligned := rfl, typed := rfl, generated := generated, lowered := rfl, live := rfl, emitted := rfl }

example : Core.tyPlace env place 0 = .ok (⟨.arr (.int .i64) 1, false, false⟩, 0) := rfl

#guard finalState.vals[1]? == some (some (.view .mutable (.int .i64)))

example : FreshPermissionInstruction (lower module)
    (permissionFunc (lowerEnv module env.vars []) finalState) (lowerEnv module env.vars [])
    0 finalState (.def 1 (.snapshot .borrowed 0)) :=
  site.permissionInstruction

example : FreshContentsEvidence (lowerEnv module env.vars []) 0 finalState 1 :=
  site.freshSnapshotContents (element := .int .i64) (.refl _) (by cbv)

end Goose.Lower.Validation.PermissionSnapshotChecks
