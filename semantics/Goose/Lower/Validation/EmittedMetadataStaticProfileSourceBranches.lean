import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceBlocks
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {profile : ArtifactProfile} {le : LEnv}

theorem EmittedProfileRun.ifValue (condition : ValueId) {yes no : B ValueId}
    (yesRun : EmittedProfileRun profile le yes) (noRun : EmittedProfileRun profile le no) :
    EmittedProfileRun profile le (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinValue endT valueT endF valueF) := by
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.fork condition).bind fun pair =>
    (EmittedProfileRun.setCur _).bind fun _ => yesRun.bind fun valueT =>
      EmittedProfileRun.curBlock.bind fun endT => (EmittedProfileRun.setCur _).bind fun _ =>
        noRun.bind fun valueF => EmittedProfileRun.curBlock.bind fun endF =>
          EmittedProfileRun.joinValue (endT, endF) valueT valueF

theorem EmittedProfileRun.ifThen (condition : ValueId) {body : B ValueId}
    (bodyRun : EmittedProfileRun profile le body) :
    EmittedProfileRun profile le (Goose.Lower.whenLive () fun _ => do
      let (target, join) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some target)
      let _ ← body
      Goose.Lower.emitTerm (.br join [])
      Goose.Lower.setCur (some join)) := by
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.fork condition).bind fun pair =>
    (EmittedProfileRun.setCur _).bind fun _ => bodyRun.bind fun _ =>
      (EmittedProfileRun.emitTerm (.br pair.2 []) trivial).bind fun _ => EmittedProfileRun.setCur _

theorem EmittedProfileRun.ifArms (condition : ValueId) {yes no : B ValueId}
    (yesRun : EmittedProfileRun profile le yes) (noRun : EmittedProfileRun profile le no) :
    EmittedProfileRun profile le (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let _ ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) := by
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.fork condition).bind fun pair =>
    (EmittedProfileRun.setCur _).bind fun _ => yesRun.bind fun _ =>
      EmittedProfileRun.curBlock.bind fun endT => (EmittedProfileRun.setCur _).bind fun _ =>
        noRun.bind fun _ => EmittedProfileRun.curBlock.bind fun endF => EmittedProfileRun.joinArms endT endF

theorem profile_source_and {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : EmittedProfileSourceExpression env results left) (rightChild : EmittedProfileSourceExpression env results right) :
    EmittedProfileSourceExpression env results (.and left right) := by
  intro type start finish source
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (leftChild leftSource).bind fun value => EmittedProfileRun.shortCircuit true value (rightChild rightSource)

theorem profile_source_or {env : Core.TEnv} {results : List Ty} (left right : Expr)
    (leftChild : EmittedProfileSourceExpression env results left) (rightChild : EmittedProfileSourceExpression env results right) :
    EmittedProfileSourceExpression env results (.or left right) := by
  intro type start finish source
  obtain ⟨leftType, leftFinish, leftSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, rightStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨rightType, rightFinish, rightSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (leftChild leftSource).bind fun value => EmittedProfileRun.shortCircuit false value (rightChild rightSource)

theorem profile_source_ifExpression {env : Core.TEnv} {results : List Ty}
    (condition : Expr) (yes no : Core.Block) (conditionChild : EmittedProfileSourceExpression env results condition)
    (yesChild : ∀ env, EmittedProfileSourceBlock env results yes) (noChild : ∀ env, EmittedProfileSourceBlock env results no) :
    EmittedProfileSourceExpression env results (.ifE condition yes no) := by
  intro type start finish source
  obtain ⟨conditionType, conditionFinish, conditionSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, yesStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨yesType, yesFinish, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨noType, noFinish, noSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (conditionChild conditionSource).bind fun value => EmittedProfileRun.ifValue value
    (yesChild (Core.exprEnv env) yesSource none [] true) (noChild (Core.exprEnv env) noSource none [] true)

theorem profile_source_conditional {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (yes : Core.Block) (otherwise : Option Core.Block) (origin : OriginId)
    (conditionChild : EmittedProfileSourceExpression env results condition)
    (yesChild : ∀ env, EmittedProfileSourceBlock env results yes)
    (otherwiseChild : ∀ body, otherwise = some body → ∀ env, EmittedProfileSourceBlock env results body) :
    EmittedProfileSourceStatement env results scope (.ifS condition yes otherwise origin) := by
  intro output start finish source loop
  obtain ⟨conditionFinish, yesType, yesFinish, conditionSource, yesSource, otherwiseSource, _⟩ := tyStmt_if_children source
  cases otherwise with
  | none => exact (conditionChild conditionSource).bind fun value =>
      EmittedProfileRun.ifThen value (yesChild env yesSource loop [] false)
  | some no =>
    obtain ⟨noType, noSource⟩ := otherwiseSource
    exact (conditionChild conditionSource).bind fun value => EmittedProfileRun.ifArms value
      (yesChild env yesSource loop [] false) (otherwiseChild no rfl env noSource loop [] false)

theorem profile_source_assert {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (origin : OriginId) (child : EmittedProfileSourceExpression env results condition) :
    EmittedProfileSourceStatement env results scope (.assertS condition origin) := by
  intro output start finish source loop
  refine (child (tyStmt_assert_children source).1).bind fun value => ?_
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.fork value).bind fun pair => (EmittedProfileRun.setCur _).bind fun _ =>
    (EmittedProfileRun.emitTerm (.abort .assert (some origin)) (by simp [EmittedProfileInst])).bind fun _ =>
      EmittedProfileRun.setCur _

end Goose.Lower.Validation
