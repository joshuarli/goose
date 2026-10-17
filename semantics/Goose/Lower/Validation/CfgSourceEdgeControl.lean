import Goose.Lower.Validation.CfgSourceEdgeContracts
import Goose.Lower.Validation.SourceStatementTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem cfg_source_ifStatement {env : Core.TEnv} {results : List Ty} (condition : Expr)
    (yes : Core.Block) (no : Option Core.Block) (origin : OriginId)
    (conditionChild : CfgSourceExpression env results condition) (yesChild : CfgSourceBlock env results yes)
    (noChild : ∀ block, no = some block → CfgSourceBlock env results block) :
    CfgSourceStatement env results (.ifS condition yes no origin) := by
  cases no with
  | none =>
    intro output scope start finish source context
    obtain ⟨conditionFinish, yesTy, yesFinish, conditionSource, yesSource, _, _⟩ := tyStmt_if_children source
    exact ((conditionChild conditionSource).withLoop context).bind fun value =>
      generated_edge_ifS_none_core _ _ value (yesChild yesSource context [] false)
  | some no =>
    intro output scope start finish source context
    obtain ⟨conditionFinish, yesTy, yesFinish, conditionSource, yesSource, noSource, _⟩ := tyStmt_if_children source
    obtain ⟨noTy, noSource⟩ := noSource
    exact ((conditionChild conditionSource).withLoop context).bind fun value =>
      generated_edge_ifS_some_core _ _ value (yesChild yesSource context [] false) (noChild no rfl noSource context [] false)

theorem cfg_source_while {env : Core.TEnv} {results : List Ty} (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : CfgSourceExpression env results condition)
    (bodyChild : CfgSourceBlock { env with loops := env.loops + 1 } results body) :
    CfgSourceStatement env results (.while condition body origin) := by
  intro output scope start finish source context
  obtain ⟨conditionFinish, bodyTy, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  simp only [lowerStmt]
  apply generated_edge_emptyHeader _ context (body := fun header =>
    lowerWhile header (lowerExpr condition) (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body))
  intro header before result after run generated loop checked headerEdge
  exact generated_edge_lowerWhile_at _ context header ((conditionChild conditionSource).withLoop context)
    (fun depth exit => bodyChild bodySource (some ⟨depth, exit, .jump header⟩) [] false)
    before after result run generated loop checked headerEdge

theorem cfg_source_range {env : Core.TEnv} {results : List Ty} (x : VarId) (lo hi : Expr)
    (body : Core.Block) (origin : OriginId) (loChild : CfgSourceExpression env results lo)
    (hiChild : CfgSourceExpression env results hi)
    (bodyChild : CfgSourceBlock { env with loops := env.loops + 1, visible := x :: env.visible } results body) :
    CfgSourceStatement env results (.forRange x lo hi body origin) := by
  intro output scope start finish source context
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyTy, _, loSource, hiSource, _, bodySource, _⟩ :=
    tyStmt_forRange_children source
  intro before result after run generated loop checked
  obtain ⟨initial, lowerEnd, loRun, bound, upperEnd, hiRun, tail⟩ := (by simpa only [lowerStmt, bind_eq] using run)
  obtain ⟨lowerGenerated, loExtension, lowerChecked⟩ := (loChild loSource).withLoop context before initial lowerEnd loRun generated loop checked
  obtain ⟨upperGenerated, hiExtension, upperChecked⟩ := (hiChild hiSource).withLoop context lowerEnd bound upperEnd hiRun
    lowerGenerated (loop.extend loExtension) lowerChecked
  have throughBounds := loExtension.trans hiExtension
  cases current : upperEnd.cur with
  | none =>
    rw [whenLive_none _ _ _ current] at tail
    obtain ⟨_, rfl⟩ := Prod.mk.inj tail
    exact ⟨upperGenerated, throughBounds, upperChecked⟩
  | some block =>
    have live : upperEnd.cur.isSome = true := by simp [current]
    have lowerLive := (dead_lowerExpr hi).live_before hiRun live
    have lowerTyped := lowerExpr_generated_typed lo loSource loRun lowerLive generated
    have initialTyped := hiExtension.types initial (.data (.int integer)) lowerTyped
    have readTy : intTyOf initial (lowerEnv env.mod env.vars results) upperEnd = (integer, upperEnd) := by
      simp only [intTyOf, valTy, bind_run, get_apply, initialTyped, pure_run]
    rw [whenLive_some _ _ _ current] at tail
    obtain ⟨ty, selected, readRun, headerRun⟩ := bind_eq.mp tail
    rw [readTy] at readRun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj readRun
    obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_counterHeader_at _ context integer initial
      (fun header counter before result after lowered generated loop checked current frame typed =>
        generated_edge_lowerRange_at _ context integer counter bound header
          (fun depth exit => bodyChild bodySource (some ⟨depth, exit, .next header integer counter⟩) [(x, counter, origin)] false)
          before after result lowered generated loop checked current frame typed)
      upperEnd after result headerRun upperGenerated (loop.extend throughBounds) upperChecked initialTyped
    exact ⟨afterGenerated, throughBounds.trans finalExtension, afterChecked⟩

end Goose.Lower.Validation
