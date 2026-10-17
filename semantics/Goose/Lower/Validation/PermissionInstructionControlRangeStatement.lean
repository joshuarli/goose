import Goose.Lower.Validation.PermissionInstructionControlRangeHeader

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private def rangeStatementTail (slot : VarId) (origin : OriginId) (body : Core.Block)
    (initial bound : ValueId) : B Unit :=
  whenLive () fun _ => do
    let hint ← intTyOf initial
    let (header,ids) ← newBlock [.data (.int hint)]
    let counter := ids.headD 0
    emitTerm (.br header [initial])
    setCur (some header)
    lowerRange hint counter bound header (fun depth exit =>
      lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body)

private theorem rangeStatementTail_dense (slot : VarId) (origin : OriginId) (body : Core.Block)
    (initial bound : ValueId) : DenseRun (rangeStatementTail slot origin body initial bound) := by
  unfold rangeStatementTail
  refine dense_whenLive _ fun _ => DenseRun.bind (dense_intTyOf _) fun hint => ?_
  exact dense_header1 (.data (.int hint)) initial
    (tail := fun header counter => lowerRange hint counter bound header (fun depth exit =>
      lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body))
    (fun header counter => dense_lowerRange hint counter bound header
      (fun depth exit => dense_lowerBlock _ [(slot,counter,origin)] false body))

private theorem rangeStatementTail_advance (slot : VarId) (origin : OriginId) (body : Core.Block)
    (initial bound : ValueId) : AdvB (rangeStatementTail slot origin body initial bound) := by
  unfold rangeStatementTail
  refine advB_whenLive _ fun _ => AdvB.bind (advB_intTyOf _) fun hint => ?_
  exact advB_header1 (.data (.int hint)) initial
    (tail := fun header counter => lowerRange hint counter bound header (fun depth exit =>
      lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body))
    (fun header counter => advB_lowerRange hint counter bound header
      (fun depth exit => advB_lowerBlock _ [(slot,counter,origin)] false body))

private theorem rangeStatementTail_types (slot : VarId) (origin : OriginId) (body : Core.Block)
    (initial bound : ValueId) : TypeRun (rangeStatementTail slot origin body initial bound) := by
  unfold rangeStatementTail
  refine types_whenLive _ fun _ => TypeRun.bind (types_intTyOf _) fun hint => ?_
  exact types_header1 (.data (.int hint)) initial
    (tail := fun header counter => lowerRange hint counter bound header (fun depth exit =>
      lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body))
    (fun header counter => types_lowerRange hint counter bound header
      (fun depth exit => types_lowerBlock _ [(slot,counter,origin)] false body))

private theorem rangeStatementTail_frames (slot : VarId) (origin : OriginId) (body : Core.Block)
    (initial bound : ValueId) : GeneratedTargetFrameRun none (rangeStatementTail slot origin body initial bound) := by
  unfold rangeStatementTail
  refine generatedTargetFrame_whenLive none _ fun _ =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_intTyOf none _) fun hint => ?_
  exact generatedTargetFrame_header1 none hint initial
    (tail := fun header counter => lowerRange hint counter bound header (fun depth exit =>
      lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body)) (by
    intro header counter base env current after result baseCurrent frames terms fresh headerAt run
    exact generatedTargetFrame_lowerRangeFresh none hint counter bound header
      (fun depth exit => generatedTargetFrame_lowerBlock _ [(slot,counter,origin)] false body)
      baseCurrent frames terms fresh headerAt run)

theorem forRange_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat} {before after : LS} {result : Unit}
    {loop : Option LoopCtx} {slot : VarId} {lo hi : Expr} {body : Core.Block} {origin : OriginId}
    (generated : GeneratedBuilderState before) (lower : first ≤ before.vals.size)
    (loNew : ∀ input value output, GeneratedBuilderState input → first ≤ input.vals.size →
      lowerExpr lo le input = (value,output) → NewPermissionInstructions module func le first input output)
    (hiNew : ∀ input value output, GeneratedBuilderState input → first ≤ input.vals.size →
      lowerExpr hi le input = (value,output) → NewPermissionInstructions module func le first input output)
    (bodyNew : ∀ hint header counter depth exit input value output,
      GeneratedBuilderState input → input.cur.isSome = true → LoopBuilderFrames (some ⟨depth,exit,.next header hint counter⟩) input →
      first ≤ input.vals.size →
      lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body le input = (value,output) →
      NewPermissionInstructions module func le first input output)
    (run : lowerStmt loop (.forRange slot lo hi body origin) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerStmt,bind_eq] at run
  obtain ⟨initial,loState,loRun,bound,hiState,hiRun,tailRun⟩ := run
  have loGenerated := generated.lowerExpr lo loRun
  have hiGenerated := loGenerated.lowerExpr hi hiRun
  have loLower := Nat.le_trans lower (advB_lowerExpr lo le before initial loState loRun).vals
  have hiLower := Nat.le_trans loLower (advB_lowerExpr hi le loState bound hiState hiRun).vals
  have prior := (loNew before initial loState generated lower loRun).compose_framed
    (hiNew loState bound hiState loGenerated loLower hiRun) hiRun (dense_lowerExpr hi)
    (advB_lowerExpr hi) (types_lowerExpr hi) (generatedTargetFrame_lowerExpr none hi) loGenerated trivial
  have tailRules : NewPermissionInstructions module func le first hiState after := by
    cases current : hiState.cur with
    | none =>
      rw [whenLive_none _ _ le current] at tailRun
      obtain ⟨_,rfl⟩ := Prod.mk.inj tailRun
      exact .of_blocks_eq rfl
    | some currentBlock =>
      rw [whenLive_some _ _ le current] at tailRun
      obtain ⟨hint,typed,typeRun,headerRun⟩ := bind_eq.mp tailRun
      have typedSame := intTyOf_eq typeRun
      subst typed
      have actualHeader : (do
          let (header,ids) ← newBlock [.data (.int hint)]
          let counter := ids.headD 0
          emitTerm (.br header [initial])
          setCur (some header)
          lowerRange hint counter bound header (fun depth exit =>
            lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body))
          le hiState = (result,after) := by
        have pairAction (action : B (BlockId × List ValueId)) (tail : BlockId → List ValueId → B Unit) :
            (do let (header,ids) ← action; tail header ids) =
              action >>= fun pair => tail pair.1 pair.2 := by
          congr 1
        exact (congrArg (fun action : B Unit => action le hiState)
          (pairAction (newBlock [.data (.int hint)]) (fun header ids => do
            let counter := ids.headD 0
            emitTerm (.br header [initial])
            setCur (some header)
            lowerRange hint counter bound header (fun depth exit =>
              lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body)))).trans headerRun
      apply header1_newPermissionInstructions (hint := hint) (initial := initial)
        (tail := fun header counter => lowerRange hint counter bound header (fun depth exit =>
          lowerBlock (some ⟨depth,exit,.next header hint counter⟩) [(slot,counter,origin)] false body))
        hiGenerated hiLower ?_ actualHeader
      intro header counter input output inputGenerated inputLower headerAt _ _ _ _ _ bodyRun
      exact lowerRange_newPermissionInstructions inputGenerated inputLower headerAt
        (fun depth exit => dense_lowerBlock _ [(slot,counter,origin)] false body)
        (fun depth exit => advB_lowerBlock _ [(slot,counter,origin)] false body)
        (fun depth exit => types_lowerBlock _ [(slot,counter,origin)] false body)
        (fun depth exit => generatedTargetFrame_lowerBlock _ [(slot,counter,origin)] false body)
        (fun depth exit input value output gen live frames lower _ _ _ _ run =>
          bodyNew hint header counter depth exit input value output gen live frames lower run) bodyRun
  exact prior.compose_framed tailRules (show rangeStatementTail slot origin body initial bound le hiState = (result,after) from tailRun)
    (rangeStatementTail_dense _ _ _ _ _) (rangeStatementTail_advance _ _ _ _ _)
    (rangeStatementTail_types _ _ _ _ _) (rangeStatementTail_frames _ _ _ _ _) hiGenerated trivial

#print axioms forRange_newPermissionInstructions

end Goose.Lower.Validation
