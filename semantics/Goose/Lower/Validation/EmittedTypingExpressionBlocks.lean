import Goose.Lower.Validation.EmittedTypingBlockSource
import Goose.Lower.Validation.EmittedTypingGeneratedBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem emitted_source_blockExpression {results : List Ty} (body : Core.Block)
    (child : ∀ env, EmittedSourceBlock env results body) :
    ∀ env, EmittedSourceExpression env results (.blockE body) := by
  intro env type start finish source initial before generated builder
  exact child (Core.exprEnv env) source none [] true generated builder trivial trivial
    (by intro slot value origin member; cases member)

theorem emitted_source_ifExpression {env : Core.TEnv} {results : List Ty}
    (condition : Expr) (yes no : Core.Block) (conditionChild : EmittedSourceExpression env results condition)
    (yesChild : ∀ env, EmittedSourceBlock env results yes) (noChild : ∀ env, EmittedSourceBlock env results no) :
    EmittedSourceExpression env results (.ifE condition yes no) := by
  intro type start finish source initial before generated builder
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, yesStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  let le := lowerEnv env.mod env.vars results
  let evaluated := lowerExpr condition le before
  have conditionBuilder := conditionChild conditionSource generated builder
  have conditionGenerated : GeneratedBuilderState evaluated.2 := generated.lowerExpr condition rfl
  have checked := emitted_checked_generated_ifValue_recorded conditionBuilder conditionGenerated evaluated.1 (sourceBlockScope yes)
    (value_lowerExpr condition le before _ _ rfl) (lowerBlock none [] true yes) (lowerBlock none [] true no)
    (fun initial started builder generated _ _ =>
      ⟨yesChild (Core.exprEnv env) yesSource none [] true generated builder trivial trivial
          (by intro slot value origin member; cases member),
        generated.lowerBlock none [] true yes trivial rfl⟩)
    (fun initial started builder generated _ _ =>
      ⟨noChild (Core.exprEnv env) noSource none [] true generated builder trivial trivial
          (by intro slot value origin member; cases member),
        generated.lowerBlock none [] true no trivial rfl⟩)
    (advB_lowerBlock none [] true yes) (advB_lowerBlock none [] true no)
    (types_lowerBlock none [] true yes) (value_lowerBlock none [] yes) (value_lowerBlock none [] no)
  exact checked.1

end Goose.Lower.Validation
