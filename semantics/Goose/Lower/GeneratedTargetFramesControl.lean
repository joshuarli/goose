import Goose.Lower.GeneratedTargetFrames

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem generatedTargetFrame_curBlock (loop : Option LoopCtx) :
    GeneratedTargetFrameRun loop curBlock := by
  intro base env current result after baseCurrent frames terms run
  rw [curBlock_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_isLive (loop : Option LoopCtx) :
    GeneratedTargetFrameRun loop isLive := by
  unfold isLive
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun _ =>
    generatedTargetFrame_pure loop _

theorem generatedTargetFrame_whenLive (loop : Option LoopCtx) (fallback : α)
    {action : BlockId → B α}
    (body : ∀ block, GeneratedTargetFrameRun loop (action block)) :
    GeneratedTargetFrameRun loop (whenLive fallback action) := by
  unfold whenLive
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun current =>
    match current with
    | none => generatedTargetFrame_pure loop fallback
    | some block => body block

theorem newBlock_fresh {base state : LS} {types : List VTy}
    {env : LEnv} {result : BlockId × List ValueId} {after : LS}
    (baseState : base.Ext state)
    (run : newBlock types env state = (result, after)) :
    base.blocks.size ≤ result.1 := by
  rw [newBlock_run_general] at run
  rcases Prod.mk.inj run with ⟨resultEq, _⟩
  have id := congrArg Prod.fst resultEq
  rw [← id]
  exact baseState.1

theorem generatedTargetFrame_fork (loop : Option LoopCtx) (condition : ValueId) :
    GeneratedTargetFrameRun loop (fork condition) := by
  intro base env current result after baseCurrent frames terms run
  unfold fork at run
  simp only [bind_eq] at run
  obtain ⟨⟨yes, yesParams⟩, first, firstRun, tail⟩ := run
  obtain ⟨⟨no, noParams⟩, second, secondRun, tail⟩ := tail
  obtain ⟨ignored, branched, branchRun, finished⟩ := tail
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have firstChecked := generatedTargetFrame_newBlock loop [] base env current (yes, yesParams)
    first baseCurrent frames terms firstRun
  have secondChecked := generatedTargetFrame_newBlock loop [] base env first (no, noParams)
    second (baseCurrent.trans firstChecked.2) frames firstChecked.1 secondRun
  have yesFresh := newBlock_fresh baseCurrent firstRun
  have noFresh := newBlock_fresh (baseCurrent.trans firstChecked.2) secondRun
  have branchFrames := secondChecked.1.emitTermAt branchRun (by
    intro target successor targetBound
    simp only [Term.successors] at successor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at successor
    rcases successor with isYes | isNo
    · subst target
      exact False.elim (Nat.not_lt_of_ge (by simpa using yesFresh) targetBound)
    · subst target
      exact False.elim (Nat.not_lt_of_ge (by simpa using noFresh) targetBound))
  have branchExt := (advB_emitTerm (.condbr condition yes [] no []) env second () branched branchRun).ext
  exact ⟨branchFrames,
    firstChecked.2.trans (secondChecked.2.trans branchExt)⟩

theorem generatedTargetFrame_valTy (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetFrameRun loop (valTy value) := by
  intro base env current result after baseCurrent frames terms run
  have same := valTy_run value env current
  rw [run] at same
  change after = current at same
  subst after
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_intTyOf (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetFrameRun loop (intTyOf value) := by
  unfold intTyOf
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> first | exact generatedTargetFrame_pure loop _ | exact generatedTargetFrame_pure loop _
  | view _ _ => exact generatedTargetFrame_pure loop _

theorem generatedTargetFrame_freezeTo (loop : Option LoopCtx) (mutability : Mutability)
    (value : ValueId) : GeneratedTargetFrameRun loop (freezeTo mutability value) := by
  unfold freezeTo
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  cases mutability <;> cases ty <;> first
    | exact generatedTargetFrame_pure loop _
    | (rename_i ty; cases ty <;> first
        | exact generatedTargetFrame_pure loop _
        | (rename_i m' _; cases m' <;> first
            | exact generatedTargetFrame_pure loop _
            | exact generatedTargetFrame_emitDef loop _))

theorem generatedTargetFrame_coerceTo (loop : Option LoopCtx) (target : Ty)
    (value : ValueId) (origin : OriginId) :
    GeneratedTargetFrameRun loop (coerceTo target value origin) := by
  unfold coerceTo
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun source => ?_
  split
  · exact generatedTargetFrame_emitDef loop _
  · exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef loop _) fun _ =>
      generatedTargetFrame_emitDef loop _
  · exact generatedTargetFrame_pure loop _

theorem generatedTargetFrame_coerceSlot (loop : Option LoopCtx) (slot : SlotId)
    (value : ValueId) (origin : OriginId) :
    GeneratedTargetFrameRun loop (coerceSlot slot value origin) := by
  unfold coerceSlot
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env =>
    match env.slots[slot]? with
    | none => generatedTargetFrame_pure loop _
    | some destination => generatedTargetFrame_coerceTo loop destination.ty value origin

theorem generatedTargetFrame_coerceResult (loop : Option LoopCtx) (value : ValueId)
    (origin : OriginId) : GeneratedTargetFrameRun loop (coerceResult value origin) := by
  unfold coerceResult
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env =>
    match env.results.head? with
    | none => generatedTargetFrame_pure loop _
    | some destination => generatedTargetFrame_coerceTo loop destination value origin

theorem generatedTargetFrame_growOwner (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetFrameRun loop (growOwner value) := by
  unfold growOwner
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  cases ty with
  | data ty => cases ty with
    | ref _ referent => cases referent with
      | grow _ => exact generatedTargetFrame_pure loop true
      | growshrink _ => exact generatedTargetFrame_pure loop true
      | _ => exact generatedTargetFrame_pure loop false
    | _ => exact generatedTargetFrame_pure loop false
  | view _ _ => exact generatedTargetFrame_pure loop false

theorem generatedTargetFrame_leaveAll (loop : Option LoopCtx) : ∀ scopes,
    GeneratedTargetFrameRun loop (leaveAll scopes)
  | [] => generatedTargetFrame_pure loop _
  | scope :: rest => by
      unfold leaveAll
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect loop _) fun _ =>
        generatedTargetFrame_leaveAll loop rest

theorem generatedTargetFrame_leaveTo (loop : Option LoopCtx) (depth : Nat) :
    GeneratedTargetFrameRun loop (leaveTo depth) := by
  unfold leaveTo
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_get loop) fun state =>
    generatedTargetFrame_leaveAll loop _

theorem generatedTargetFrame_initSlots (loop : Option LoopCtx) : ∀ slots,
    GeneratedTargetFrameRun loop (initSlots slots)
  | [] => generatedTargetFrame_pure loop _
  | slot :: rest => by
      unfold initSlots
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect loop _) fun _ =>
        generatedTargetFrame_initSlots loop rest

end Goose.Lower
