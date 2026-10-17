import Goose.Lower.Validation.ActualContents

namespace Goose.Lower.Validation.ActualContentsChecks

open Goose.Core Goose.GIR

private def module : Core.Module :=
  { files := #[], types := #[], globals := #[], impls := #[], contexts := #[], entry := 0, origins := #[] }

private def env : TEnv :=
  { mod := module, impl := none, vars := #[⟨"array", .arr (.int .i64) 1, .immutable, 0, 0⟩],
    visible := [0], loops := 0, inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

private def place : Place := .deref (.ref .readOnly (.var 0))

private def initial : LS :=
  ⟨#[⟨[], #[]⟩, ⟨[(0, .data (.int .i64))], #[]⟩], #[some (.data (.int .i64))], some 0, [0]⟩

private def output : ValueId × LS := lowerPlace place (lowerEnv module env.vars []) initial

private def finalState : LS :=
  ⟨#[⟨[], #[.def 1 (.slotAddr 0)]⟩, ⟨[(0, .data (.int .i64))], #[]⟩],
    #[some (.data (.int .i64)), some (.data (.ref .readOnly (.arr (.int .i64) 1)))], some 0, [0]⟩

private theorem output_eq : output = (1, finalState) := rfl

private theorem generated : GeneratedBuilderState initial := by
  refine ⟨?_, ?_, ?_⟩
  · exact List.Perm.refl _
  · intro block current
    have same : block = 0 := Option.some.inj current.symm
    subst block
    decide
  · intro index body row target member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    have either : index = 0 ∨ index = 1 := by change index < 2 at bound; nat_omega
    rcases either with rfl | rfl
    all_goals
      simp [initial] at row
      subst body
      simp [cfgBlock, GIR.Block.terms] at member

example : Core.tyPlace env place 1 = .ok (⟨.arr (.int .i64) 1, false, false⟩, 1) := by rfl

#guard (tyEnv (lowerEnv module env.vars []) output.2).contentsWritable 0 == some true

#guard let lowered := lowerView (.of place) (lowerEnv module env.vars []) initial
  lowered.2.vals[lowered.1]? == some (some (.view .mutable (.int .i64)))

private def frozenEnv : TEnv :=
  { env with vars := #[⟨"array", .arr (.int .i64) 1, .mutable, 0, 0⟩] }

#guard let lowered := lowerPlace place (lowerEnv module frozenEnv.vars []) initial
  (tyEnv (lowerEnv module frozenEnv.vars []) lowered.2).contentsWritable lowered.1 == some false

private def joined : Expr := .ifE (.bool true)
  (.mk 1 [] (some (.ref .readOnly (.var 0))))
  (.mk 2 [] (some (.ref .readOnly (.var 0))))

#guard match Core.tyExpr env joined 1 with
  | .ok (.ref .readOnly (.arr (.int .i64) 1), _) => true
  | _ => false

#guard let lowered := lowerExpr joined (lowerEnv module env.vars []) initial
  (tyEnv (lowerEnv module env.vars []) lowered.2).contentsWritable lowered.1 == some true

private theorem actualContents :
    (tyEnv (lowerEnv module env.vars []) output.2).contentsWritable output.1 = some true := by
  have slotEvidence : FreshContentsEvidence (lowerEnv module env.vars []) 1 output.2 output.1 :=
    lowerPlace_var_fresh_contents (env := env) (index := 0) (start := 1) (finish := 1)
      (info := ⟨.arr (.int .i64) 1, false, true⟩) (by rfl)
      generated.dense generated.live (current := 0) rfl rfl
  exact slotEvidence.forget.contentsWritable

private theorem evidence : FreshContentsEvidence (lowerEnv module env.vars []) 1 output.2 output.1 := by
  rw [output_eq]
  apply lowerPlace_generated_actual_contents place (env := env) (start := 1) (finish := 1)
    (info := ⟨.arr (.int .i64) 1, false, false⟩) (before := initial) (after := finalState) (value := 1)
    (by rfl) rfl (by rfl) ?_ generated
  change (tyEnv (lowerEnv module env.vars []) finalState).contentsWritable 1 = some true
  simpa only [output_eq] using actualContents

example : ∃ authorized,
    ContentsClosed ((lowerEnv module env.vars []).globals.map (·.2)) module.structs
      (permissionFunc (lowerEnv module env.vars []) output.2) output.2.vals authorized ∧
    NonIntegerParameters (permissionFunc (lowerEnv module env.vars []) output.2) authorized ∧
    authorized output.1 ∧ ¬ authorized 0 := by
  obtain ⟨authorized, closed, noninteger, member, fresh⟩ := evidence
  refine ⟨authorized, closed, noninteger, member, ?_⟩
  intro old
  have impossible := fresh 0 old
  omega

end Goose.Lower.Validation.ActualContentsChecks
