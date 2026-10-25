import Goose.Lower.GeneratedIntervalFramesRun

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem IntervalEdgesFramed.appendInst {before captured current : LS}
    (framed : IntervalEdgesFramed before captured current) (block : BlockId) (inst : Inst)
    (outside : ∀ term, inst = .term term → ∀ target ∈ term.successors,
      target < before.blocks.size ∨ captured.blocks.size ≤ target) :
    IntervalEdgesFramed before captured (current.appendInst block inst) := by
  apply framed.extend
  intro source body term target row member successor lower upper
  change (current.blocks.modify block fun body => { body with insts := body.insts.push inst })[source]? = some body at row
  rw [Array.getElem?_modify] at row
  by_cases same : block = source
  · subst source
    simp only [↓reduceIte, Option.map_eq_some_iff] at row
    obtain ⟨old, oldRow, rfl⟩ := row
    rcases List.mem_append.mp (by simpa only [Array.toList_push] using member) with oldMember | added
    · exact ⟨old, oldRow, oldMember⟩
    · have equal : inst = .term term := (List.mem_singleton.mp added).symm
      rcases outside term equal target successor with earlier | later
      · exact False.elim (Nat.not_lt_of_ge lower earlier)
      · exact False.elim (Nat.not_lt_of_ge later upper)
  · simp only [same, ite_false] at row
    exact ⟨body, row, member⟩

theorem IntervalEdgesFramed.emitTermAt {before captured current after : LS} {env : LEnv}
    {result : Unit} {term : Term} (framed : IntervalEdgesFramed before captured current)
    (run : emitTerm term env current = (result, after))
    (outside : ∀ target ∈ term.successors, target < before.blocks.size ∨ captured.blocks.size ≤ target) :
    IntervalEdgesFramed before captured after := by
  cases live : current.cur with
  | none => rw [emitTerm_none term env live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact framed
  | some block =>
    rw [emitTerm_run term env live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    apply framed.appendInst block (.term term)
    intro actual equal target successor
    cases equal
    exact outside target successor

theorem IntervalEdgesFramed.patchTermAt {before captured current after : LS} {env : LEnv}
    {result : Unit} {block : BlockId} {term : Term} (framed : IntervalEdgesFramed before captured current)
    (run : patchTerm block term env current = (result, after))
    (outside : ∀ target ∈ term.successors, target < before.blocks.size ∨ captured.blocks.size ≤ target) :
    IntervalEdgesFramed before captured after := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  apply framed.appendInst block (.term term)
  intro actual equal target successor
  cases equal
  exact outside target successor

theorem IntervalEdgesFramed.emitDefAt {before captured current after : LS} {env : LEnv}
    {result : ValueId} {op : Op} (framed : IntervalEdgesFramed before captured current)
    (run : emitDef op env current = (result, after)) : IntervalEdgesFramed before captured after := by
  cases live : current.cur with
  | none => rw [emitDef_none op env live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact framed
  | some block =>
    rw [emitDef_run op env live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact framed.appendInst block (.def current.vals.size op) (by intro term equal; cases equal)

theorem IntervalEdgesFramed.emitEffectAt {before captured current after : LS} {env : LEnv}
    {result : Unit} {effect : Effect} (framed : IntervalEdgesFramed before captured current)
    (run : emitEffect effect env current = (result, after)) : IntervalEdgesFramed before captured after := by
  cases live : current.cur with
  | none => rw [emitEffect_none effect env live] at run; obtain ⟨_, rfl⟩ := Prod.mk.inj run; exact framed
  | some block =>
    rw [emitEffect_run effect env live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact framed.appendInst block (.eff effect) (by intro term equal; cases equal)

theorem IntervalEdgesFramed.newBlockAt {before captured current after : LS} {env : LEnv}
    {result : BlockId × List ValueId} {types : List VTy} (framed : IntervalEdgesFramed before captured current)
    (run : newBlock types env current = (result, after)) : IntervalEdgesFramed before captured after := by
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  apply framed.extend
  intro source body term target row member successor lower upper
  simp only [Array.getElem?_push] at row
  split at row
  · obtain rfl := Option.some.inj row
    cases member
  · exact ⟨body, row, member⟩

theorem GeneratedIntervalFrameRun.emitTerm {loop : Option LoopCtx} {deferred : List BlockId} (term : Term)
    (targets : ∀ target ∈ term.successors, target ∈ deferred ++ LoopBuilderFrameTargets loop) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.emitTerm term) := by
  intro before captured env current result after extension frames avoids terms run
  exact ⟨terms.emitTermAt run (fun target member => avoids target (targets target member)),
    (advB_emitTerm term env current result after run).ext⟩

theorem GeneratedIntervalFrameRun.patchTerm {loop : Option LoopCtx} {deferred : List BlockId}
    (block : BlockId) (term : Term)
    (targets : ∀ target ∈ term.successors, target ∈ deferred ++ LoopBuilderFrameTargets loop) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.patchTerm block term) := by
  intro before captured env current result after extension frames avoids terms run
  exact ⟨terms.patchTermAt run (fun target member => avoids target (targets target member)), patchTerm_ext run⟩

theorem GeneratedIntervalFrameRun.pure (loop : Option LoopCtx) (deferred : List BlockId) (value : α) :
    GeneratedIntervalFrameRun loop deferred (pure value) := .of_frames (generatedTargetFrame_pure loop value) deferred

theorem GeneratedIntervalFrameRun.emitDef (loop : Option LoopCtx) (deferred : List BlockId) (op : Op) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.emitDef op) := .of_frames (generatedTargetFrame_emitDef loop op) deferred

theorem GeneratedIntervalFrameRun.emitEffect (loop : Option LoopCtx) (deferred : List BlockId) (effect : Effect) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.emitEffect effect) := .of_frames (generatedTargetFrame_emitEffect loop effect) deferred

theorem GeneratedIntervalFrameRun.newBlock (loop : Option LoopCtx) (deferred : List BlockId) (types : List VTy) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.newBlock types) := .of_frames (generatedTargetFrame_newBlock loop types) deferred

theorem GeneratedIntervalFrameRun.setCur (loop : Option LoopCtx) (deferred : List BlockId) (current : Option BlockId) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.setCur current) := .of_frames (generatedTargetFrame_setCur loop current) deferred

structure GeneratedIntervalFrame (targets : List BlockId) (before captured current : LS) : Prop where
  extension : captured.Ext current
  edges : IntervalEdgesFramed before captured current
  avoids : IntervalTargetsAvoid before captured targets

theorem GeneratedIntervalFrame.initial (targets : List BlockId) (before captured : LS)
    (bounded : ∀ target ∈ targets, target < before.blocks.size) :
    GeneratedIntervalFrame targets before captured captured :=
  ⟨.refl _, .refl _ _, fun target member => Or.inl (bounded target member)⟩

theorem GeneratedIntervalFrame.weaken {first second : List BlockId} {before captured current : LS}
    (frame : GeneratedIntervalFrame first before captured current)
    (included : ∀ target ∈ second, target ∈ first) : GeneratedIntervalFrame second before captured current :=
  ⟨frame.extension, frame.edges, frame.avoids.mono included⟩

theorem GeneratedIntervalFrame.reserve {targets : List BlockId} {before captured current : LS}
    (frame : GeneratedIntervalFrame targets before captured current) {target : BlockId}
    (fresh : current.blocks.size ≤ target) : GeneratedIntervalFrame (target :: targets) before captured current :=
  ⟨frame.extension, frame.edges, frame.avoids.cons (Or.inr (Nat.le_trans frame.extension.1 fresh))⟩

theorem GeneratedIntervalFrame.run {loop : Option LoopCtx} {deferred : List BlockId}
    {before captured current after : LS} {env : LEnv} {action : B α} {result : α}
    (frame : GeneratedIntervalFrame (deferred ++ LoopBuilderFrameTargets loop) before captured current)
    (checked : GeneratedIntervalFrameRun loop deferred action) (loopFrames : LoopBuilderFrames loop current)
    (run : action env current = (result, after)) :
    GeneratedIntervalFrame (deferred ++ LoopBuilderFrameTargets loop) before captured after := by
  obtain ⟨edges, extension⟩ := checked before captured env current result after frame.extension loopFrames frame.avoids frame.edges run
  exact ⟨frame.extension.trans extension, edges, frame.avoids⟩

theorem GeneratedIntervalFrameRun.read (loop : Option LoopCtx) (deferred : List BlockId)  :
    GeneratedIntervalFrameRun loop deferred (read : B LEnv) :=
  .of_frames (generatedTargetFrame_read loop ) deferred

theorem GeneratedIntervalFrameRun.get (loop : Option LoopCtx) (deferred : List BlockId)  :
    GeneratedIntervalFrameRun loop deferred (get : B LS) :=
  .of_frames (generatedTargetFrame_get loop ) deferred

theorem GeneratedIntervalFrameRun.curBlock (loop : Option LoopCtx) (deferred : List BlockId)  :
    GeneratedIntervalFrameRun loop deferred Goose.Lower.curBlock :=
  .of_frames (generatedTargetFrame_curBlock loop ) deferred

theorem GeneratedIntervalFrameRun.isLive (loop : Option LoopCtx) (deferred : List BlockId)  :
    GeneratedIntervalFrameRun loop deferred Goose.Lower.isLive :=
  .of_frames (generatedTargetFrame_isLive loop ) deferred

theorem GeneratedIntervalFrameRun.intTyOf (loop : Option LoopCtx) (deferred : List BlockId) (value : ValueId) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.intTyOf value) :=
  .of_frames (generatedTargetFrame_intTyOf loop value) deferred

theorem GeneratedIntervalFrameRun.valTy (loop : Option LoopCtx) (deferred : List BlockId) (value : ValueId) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.valTy value) :=
  .of_frames (generatedTargetFrame_valTy loop value) deferred

theorem GeneratedIntervalFrameRun.fork (loop : Option LoopCtx) (deferred : List BlockId) (condition : ValueId) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.fork condition) :=
  .of_frames (generatedTargetFrame_fork loop condition) deferred


theorem GeneratedIntervalFrameRun.whenLive {loop : Option LoopCtx} {deferred : List BlockId}
    (fallback : α) {action : BlockId → B α}
    (child : ∀ block, GeneratedIntervalFrameRun loop deferred (action block)) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.whenLive fallback action) := by
  unfold Goose.Lower.whenLive
  apply (GeneratedIntervalFrameRun.curBlock loop deferred).bind
  intro current
  cases current with
  | none => exact GeneratedIntervalFrameRun.pure loop deferred fallback
  | some block => exact child block

theorem GeneratedIntervalFrame.retarget {first second : List BlockId} {before captured current : LS}
    (frame : GeneratedIntervalFrame first before captured current)
    (avoids : IntervalTargetsAvoid before captured second) : GeneratedIntervalFrame second before captured current :=
  ⟨frame.extension, frame.edges, avoids⟩

end Goose.Lower
