import Goose.Lower.Validation.SnapshotContentsSourceControlHeaders
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem snapshot_source_while {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : SnapshotSourceExpression env results condition)
    (bodyChild : ∀ env, SnapshotSourceBlock env results body) :
    SnapshotSourceStatement env results scope (.while condition body origin) := by
  intro output start finish source loop before result after generated frames run
  obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  have checked := snapshot_control_header0
    (SnapshotSourceTrace.empty (lowerEnv env.mod env.vars results) before generated.dense) generated (Nat.le_refl _)
    (fun header => lowerWhile header (lowerExpr condition)
      (fun depth target => lowerBlock (some ⟨depth, target, .jump header⟩) [] false body))
    (fun header state trace generated fresh headerAt =>
      (snapshot_lowerWhile trace generated fresh header headerAt (lowerExpr condition)
        (fun depth target => lowerBlock (some ⟨depth, target, .jump header⟩) [] false body)
        (SnapshotSourceAction.lowerExpr condition (conditionChild conditionSource))
        (fun depth target => SnapshotSourceAction.lowerBlock _ [] false body
          (bodyChild { env with loops := env.loops + 1 } bodySource _ [] false))).1)
  change SnapshotSourceTrace (lowerEnv env.mod env.vars results) before.vals.size
    (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.vars results) before).2
    (lowerStmt loop (.while condition body origin) (lowerEnv env.mod env.vars results) before).2 at checked
  simpa only [run] using checked

theorem snapshot_source_forRange {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (lowChild : SnapshotSourceExpression env results lo) (highChild : SnapshotSourceExpression env results hi)
    (bodyChild : ∀ env, SnapshotSourceBlock env results body) :
    SnapshotSourceStatement env results scope (.forRange slot lo hi body origin) := by
  intro output start finish source loop before result after generated frames run
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, binderType, bodySource, _⟩ := tyStmt_forRange_children source
  change (do
    let low ← lowerExpr lo
    let high ← lowerExpr hi
    whenLive () fun _ => do
      let hint ← intTyOf low
      let (header, params) ← newBlock [.data (.int hint)]
      let counter := params.headD 0
      emitTerm (.br header [low])
      setCur (some header)
      lowerRange hint counter high header (fun depth target =>
        lowerBlock (some ⟨depth, target, .next header hint counter⟩) [(slot, counter, origin)] false body))
      (lowerEnv env.mod env.vars results) before = (result, after) at run
  obtain ⟨low, lowState, lowRun, high, highState, highRun, rest⟩ := by
    simpa only [bind_eq] using run
  have lowTrace := lowChild lowSource before low lowState generated trivial lowRun
  have lowGenerated := generated.lowerExpr lo lowRun
  have lowAdvance := advB_lowerExpr lo _ before low lowState lowRun
  have highTrace := (highChild highSource).continue (dense_lowerExpr hi) (advB_lowerExpr hi)
    (types_lowerExpr hi) (generatedTargetFrame_lowerExpr none hi) lowTrace lowGenerated trivial lowAdvance.vals highRun
  have highGenerated := lowGenerated.lowerExpr hi highRun
  have highFresh := Nat.le_trans lowAdvance.vals (advB_lowerExpr hi _ lowState high highState highRun).vals
  cases live : highState.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at rest
    obtain ⟨_, rfl⟩ := Prod.mk.inj rest
    exact highTrace
  | some current =>
    rw [whenLive_some _ _ _ live] at rest
    obtain ⟨hint, observed, observation, headerRun⟩ := bind_eq.mp rest
    have same := intTyOf_eq observation
    subst observed
    have checked := snapshot_control_header1 highTrace highGenerated highFresh hint low
      (fun header counter => lowerRange hint counter high header (fun depth target =>
        lowerBlock (some ⟨depth, target, .next header hint counter⟩) [(slot, counter, origin)] false body))
      (fun header counter state trace generated fresh headerAt =>
        (snapshot_lowerRange trace generated fresh hint counter high header headerAt
          (fun depth target => lowerBlock (some ⟨depth, target, .next header hint counter⟩)
            [(slot, counter, origin)] false body)
          (fun depth target => SnapshotSourceAction.lowerBlock _ [(slot, counter, origin)] false body
            (bodyChild { env with loops := env.loops + 1, visible := slot :: env.visible }
              bodySource _ [(slot, counter, origin)] false))).1)
    simpa only [headerRun] using checked

end Goose.Lower.Validation
