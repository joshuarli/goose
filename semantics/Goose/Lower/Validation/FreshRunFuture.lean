import Goose.Lower.Validation.FreshRunJoins

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def OwnerLiteralRows (func : Func) (types : Array (Option VTy)) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ value ty values,
    Inst.def value (.arrLit ty values) ∈ block.insts → isLiteralRunType ty = true →
      types[value]? = some (some (.data ty))

def FutureLiteralValue (before captured : LS) (value : ValueId) : Prop :=
  ∀ (loop : Option LoopCtx) (after : LS) (func : Func) (types : Array (Option VTy)),
    LoopBuilderFrames loop before → TermEdgesFramed loop captured after → captured.Ext after →
    (∀ body ∈ after.blocks.toList, ClosedBlock body) →
    func.blocks = finishBlocks after.blocks →
    (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues) →
    OwnerLiteralRows func types → FreshLiteralValue func types value

theorem FutureLiteralValue.weaken {before childStart childEnd captured : LS} {value : ValueId}
    (child : FutureLiteralValue childStart childEnd value)
    (startExtension : before.Ext childStart) (suffix : childEnd.Ext captured)
    (framedSuffix : TermEdgesFramed none childEnd captured) :
    FutureLiteralValue before captured value := by
  intro loop after func types frames framed extension closed blocks dense rows
  apply child loop after func types (frames.mono startExtension) _ (suffix.trans extension) closed blocks dense rows
  have oldFrames : TermEdgesFramed loop childEnd captured :=
    framedSuffix.weakenLoop (by intro target impossible; cases impossible)
  exact TermEdgesFramed.rebase oldFrames framed suffix (by intro target loopTarget; exact Or.inl loopTarget)

theorem futureLiteralValue_arrLit {env : LEnv} {before captured : LS}
    {ty : Ty} {exprs : List Expr} {value : ValueId}
    (run : lowerExpr (.arrLit ty exprs) env before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before)
    (runType : isLiteralRunType ty = true) : FutureLiteralValue before captured value := by
  intro loop after func types frames framed extension closed blocks dense rows
  simp only [lowerExpr] at run
  obtain ⟨values, middle, childrenRun, literalRun⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef (.arrLit ty values)).live_before literalRun live
  have middleGenerated := generated.lowerExprs exprs childrenRun
  cases current : middle.cur with
  | none => simp [current] at middleLive
  | some block =>
    obtain ⟨body, bodyMember, definition⟩ := emitted_definition_retained current
      (middleGenerated.live block current) literalRun extension blocks
    apply lowerExpr_arrLit_fresh (bind_eq.mpr ⟨values, middle, childrenRun, literalRun⟩)
      live generated extension blocks dense runType
    exact rows body bodyMember value ty values definition runType

end Goose.Lower.Validation
