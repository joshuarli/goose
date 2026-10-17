import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlSetups

namespace Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl

open Goose.Core Goose.GIR ReturnFrames

private theorem absent_loopPrefix {avoid : List ValueId × Option OriginId} (condition : ValueId) :
    ReturnAbsentRun (avoid := avoid) (loopPrefix condition) := by
  unfold loopPrefix
  refine ReturnAbsentRun.bind returnAbsent_get fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_fork condition) fun _ => ?_
  exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => returnAbsent_pure _

private theorem absent_whileSetup {avoid : List ValueId × Option OriginId} {condition : Expr}
    (free : ReturnFreeExpr condition) : ReturnAbsentRun (avoid := avoid) (whileSetup condition) := by
  unfold whileSetup
  refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro _ _ same; cases same)) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_lowerExpr condition free) fun value => ?_
  apply returnAbsent_whenLive
  intro _
  exact ReturnAbsentRun.bind (absent_loopPrefix value) fun _ => returnAbsent_pure _

private theorem absent_rangeSetup {avoid : List ValueId × Option OriginId} {lo hi : Expr}
    (lowerFree : ReturnFreeExpr lo) (upperFree : ReturnFreeExpr hi) :
    ReturnAbsentRun (avoid := avoid) (rangeSetup lo hi) := by
  unfold rangeSetup
  refine ReturnAbsentRun.bind (returnAbsent_lowerExpr lo lowerFree) fun lower => ?_
  refine ReturnAbsentRun.bind (returnAbsent_lowerExpr hi upperFree) fun _ => ?_
  apply returnAbsent_whenLive
  intro _
  refine ReturnAbsentRun.bind (returnAbsent_intTyOf lower) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_newBlock _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro _ _ same; cases same)) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun condition => ?_
  exact ReturnAbsentRun.bind (absent_loopPrefix condition) fun _ => returnAbsent_pure _

private theorem absent_eachSetup {avoid : List ValueId × Option OriginId} {view : View}
    (free : ReturnFreeView view) : ReturnAbsentRun (avoid := avoid) (eachSetup view) := by
  unfold eachSetup
  refine ReturnAbsentRun.bind (returnAbsent_lowerEachSource view free) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_regrowOf pair.1) fun regrow => ?_
  refine ReturnAbsentRun.bind (returnAbsent_eachSampled regrow pair.2) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => ?_
  apply returnAbsent_whenLive
  intro _
  refine ReturnAbsentRun.bind (returnAbsent_newBlock _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro _ _ same; cases same)) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_eachLen _ _ _) fun _ => ?_
  refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun condition => ?_
  exact ReturnAbsentRun.bind (absent_loopPrefix condition) fun _ => returnAbsent_pure _

theorem while_origin {sourceEnv : TEnv} {condition : Expr} {body : Core.Block} {sourceOrigin : OriginId}
    {type : Ty} {start finish : Nat} {env : LEnv} {initial final : LS} {result : Unit}
    {values : List ValueId} {origin : Option OriginId} (loop : Option LoopCtx)
    (source : Core.tyExpr sourceEnv condition start = .ok (type, finish))
    (run : lowerStmt loop (.while condition body sourceOrigin) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨ Nonempty (ActiveReturnCheckpoint (whileSetup condition)
      (fun (header, depth, exit) => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
      env initial values origin) := by
  rw [while_factor] at run
  exact optional_origin (env := env) (initial := initial) (final := final) (result := result)
    (child := fun (header, depth, exit) => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)
    (suffix := fun (arguments : BlockId × Nat × BlockId) (_ : ValueId) => do
    emitTerm (.br arguments.1 []); setCur (some arguments.2.2))
    (frame _ (fun _ => absent_whileSetup (tyExpr_returnFree condition source)))
    (fun arguments _ => frame_bind (frame _ (fun _ => returnAbsent_emitTerm _ (by intro _ _ same; cases same)))
      (fun _ => frame _ (fun _ => returnAbsent_setCur _))) (by
      simp only [bind_run] at run ⊢
      generalize selection : (whileSetup condition) env initial = pair at run ⊢
      obtain ⟨selected, state⟩ := pair
      cases selected with
      | none => exact run
      | some arguments => obtain ⟨header, depth, exit⟩ := arguments; exact run) member

theorem range_origin {sourceEnv : TEnv} {x : VarId} {lo hi : Expr} {body : Core.Block} {sourceOrigin : OriginId}
    {lowerType upperType : Ty} {lowerStart lowerFinish upperStart upperFinish : Nat}
    {env : LEnv} {initial final : LS} {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (loop : Option LoopCtx)
    (lowerSource : Core.tyExpr sourceEnv lo lowerStart = .ok (lowerType, lowerFinish))
    (upperSource : Core.tyExpr sourceEnv hi upperStart = .ok (upperType, upperFinish))
    (run : lowerStmt loop (.forRange x lo hi body sourceOrigin) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨ Nonempty (ActiveReturnCheckpoint (rangeSetup lo hi)
      (fun (type, counter, _, header, depth, exit) =>
        lowerBlock (some ⟨depth, exit, .next header type counter⟩) [(x, counter, sourceOrigin)] false body)
      env initial values origin) := by
  rw [range_factor] at run
  exact optional_origin (env := env) (initial := initial) (final := final) (result := result)
    (child := fun (type, counter, _, header, depth, exit) => lowerBlock (some ⟨depth, exit, .next header type counter⟩) [(x, counter, sourceOrigin)] false body)
    (suffix := fun (arguments : IntTy × ValueId × ValueId × BlockId × Nat × BlockId) (_ : ValueId) => do
    rangeBack arguments.1 arguments.2.1 arguments.2.2.2.1; setCur (some arguments.2.2.2.2.2))
    (frame _ (fun _ => absent_rangeSetup (tyExpr_returnFree lo lowerSource) (tyExpr_returnFree hi upperSource)))
    (fun arguments _ => frame_bind (frame _ (fun _ => returnAbsent_rangeBack arguments.1 arguments.2.1 arguments.2.2.2.1))
      (fun _ => frame _ (fun _ => returnAbsent_setCur _))) (by
      simp only [bind_run] at run ⊢
      generalize selection : (rangeSetup lo hi) env initial = pair at run ⊢
      obtain ⟨selected, state⟩ := pair
      cases selected with
      | none => exact run
      | some arguments => obtain ⟨type, counter, upper, header, depth, exit⟩ := arguments; exact run) member

theorem each_origin {sourceEnv : TEnv} {x : VarId} {index : Option VarId} {view : View}
    {byRef : Bool} {body : Core.Block} {sourceOrigin : OriginId} {info : Ty × Bool} {start finish : Nat}
    {env : LEnv} {initial final : LS} {result : Unit} {values : List ValueId} {origin : Option OriginId}
    (loop : Option LoopCtx)
    (source : Core.tyView sourceEnv view start = .ok (info, finish))
    (run : lowerStmt loop (.forEach x index view byRef body sourceOrigin) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    .term (.ret values origin) ∈ initial.insts ∨ Nonempty (ActiveReturnCheckpoint (eachSetup view)
      (eachBody x index byRef body sourceOrigin) env initial values origin) := by
  rw [each_factor] at run
  exact optional_origin (env := env) (initial := initial) (final := final) (result := result)
    (child := eachBody x index byRef body sourceOrigin)
    (suffix := fun (arguments : ValueId × ValueId × BlockId × Nat × BlockId) (_ : ValueId) => do
    rangeBack .i64 arguments.2.1 arguments.2.2.1; setCur (some arguments.2.2.2.2))
    (frame _ (fun _ => absent_eachSetup (tyView_returnFree view source)))
    (fun arguments _ => frame_bind (frame _ (fun _ => returnAbsent_rangeBack .i64 arguments.2.1 arguments.2.2.1))
      (fun _ => frame _ (fun _ => returnAbsent_setCur _))) (by
      simp only [bind_run] at run ⊢
      generalize selection : (eachSetup view) env initial = pair at run ⊢
      obtain ⟨selected, state⟩ := pair
      cases selected with
      | none => exact run
      | some arguments => exact run) member

end Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl
