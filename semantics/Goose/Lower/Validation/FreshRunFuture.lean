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

theorem futureLiteralValue_joinAt {env : LEnv} {before current captured : LS}
    {pending : List (BlockId × ValueId)} {value : ValueId}
    (run : (do
      let ty ← valTy (pending.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join pending
      setCur (some join)
      pure (params.headD 0)) env current = (value, captured))
    (bounded : TargetsBounded current) (pendingNonempty : pending ≠ [])
    (pendingBounds : ∀ item ∈ pending, item.1 < current.blocks.size)
    (startExtension : before.Ext current)
    (inputs : ∀ item ∈ pending, FutureLiteralValue before captured item.2) :
    FutureLiteralValue before captured value := by
  intro loop after func types frames framed extension closed blocks dense rows
  simp only [bind_eq] at run
  obtain ⟨ty, typedState, typeRun, ⟨join, params⟩, allocated, allocation,
    _, patched, patch, _, resumed, resume, final⟩ := run
  have typedSame : typedState = current := by
    have same := valTy_run (pending.headD (0, 0)).2 env current
    rw [typeRun] at same
    exact same
  subst typedState
  have shape := allocation
  rw [newBlock1_run] at shape
  obtain ⟨pair, state⟩ := Prod.mk.inj shape
  obtain ⟨joinEq, paramsEq⟩ := Prod.mk.inj pair
  subst join
  subst params
  rw [setCur_run] at resume
  obtain ⟨_, rfl⟩ := Prod.mk.inj resume
  obtain ⟨rfl, rfl⟩ := pure_eq.mp final
  apply freshLiteralValue_joinAt allocation patch bounded pendingNonempty pendingBounds
    (frames.mono startExtension) framed extension closed blocks
  intro item member
  exact inputs item member loop after func types frames framed extension closed blocks dense rows

theorem futureLiteralValue_joinValue {env : LEnv} {before current captured : LS}
    {yes no : Option BlockId} {yesValue noValue value : ValueId}
    (run : joinValue yes yesValue no noValue env current = (value, captured))
    (live : captured.cur.isSome = true) (bounded : TargetsBounded current)
    (yesBound : ∀ block, yes = some block → block < current.blocks.size)
    (noBound : ∀ block, no = some block → block < current.blocks.size)
    (startExtension : before.Ext current)
    (yesFresh : yes.isSome = true → FutureLiteralValue before captured yesValue)
    (noFresh : no.isSome = true → FutureLiteralValue before captured noValue) :
    FutureLiteralValue before captured value := by
  unfold joinValue at run
  cases yes <;> cases no
  · obtain ⟨_, middle, change, final⟩ := bind_eq.mp run
    rw [setCur_run] at change
    obtain ⟨_, rfl⟩ := Prod.mk.inj change
    obtain ⟨_, rfl⟩ := pure_eq.mp final
    simp at live
  all_goals
    refine futureLiteralValue_joinAt run bounded (by simp) ?_ startExtension ?_
    · intro item member
      simp at member
      rcases member with rfl | rfl <;> first | exact yesBound _ rfl | exact noBound _ rfl
    · intro item member
      simp at member
      rcases member with rfl | rfl <;> first | exact yesFresh rfl | exact noFresh rfl

end Goose.Lower.Validation
