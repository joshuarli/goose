import Goose.Lower.GeneratedTargetsSource

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

def LoopBuilderFrames (loop : Option LoopCtx) (state : LS) : Prop :=
  match loop with
  | none => True
  | some context =>
      (∃ block, state.blocks[context.breakTo]? = some block ∧ block.params = []) ∧
      match context.cont with
      | .jump header => ∃ block, state.blocks[header]? = some block ∧ block.params = []
      | .next header ty counter =>
          ∃ block, state.blocks[header]? = some block ∧
            block.params = [(counter, .data (.int ty))]

def LoopBuilderFrameTarget (loop : Option LoopCtx) (target : BlockId) : Prop :=
  match loop with
  | none => False
  | some context => target = context.breakTo ∨
      match context.cont with
      | .jump header => target = header
      | .next header _ _ => target = header

theorem LoopBuilderFrames.targetBound {loop : Option LoopCtx} {state : LS}
    (frames : LoopBuilderFrames loop state) {target : BlockId}
    (isTarget : LoopBuilderFrameTarget loop target) : target < state.blocks.size := by
  cases loop with
  | none => cases isTarget
  | some context =>
      cases kind : context.cont with
      | jump header =>
          simp only [LoopBuilderFrameTarget, kind] at isTarget
          simp only [LoopBuilderFrames, kind] at frames
          rcases frames with ⟨⟨exit, exitAt, _⟩, ⟨head, headAt, _⟩⟩
          rcases isTarget with isExit | isHeader
          · subst target
            exact (Array.getElem?_eq_some_iff.mp exitAt).1
          · subst target
            exact (Array.getElem?_eq_some_iff.mp headAt).1
      | next header ty counter =>
          simp only [LoopBuilderFrameTarget, kind] at isTarget
          simp only [LoopBuilderFrames, kind] at frames
          rcases frames with ⟨⟨exit, exitAt, _⟩, ⟨head, headAt, _⟩⟩
          rcases isTarget with isExit | isHeader
          · subst target
            exact (Array.getElem?_eq_some_iff.mp exitAt).1
          · subst target
            exact (Array.getElem?_eq_some_iff.mp headAt).1

theorem LoopBuilderFrames.toTargets {loop : Option LoopCtx} {state : LS}
    (frames : LoopBuilderFrames loop state) : LoopBuilderTargets loop state := by
  cases loop with
  | none => trivial
  | some context =>
      cases kind : context.cont with
      | jump header =>
          simp only [LoopBuilderTargets, kind]
          exact ⟨frames.targetBound (target := context.breakTo) (by simp [LoopBuilderFrameTarget]),
            frames.targetBound (target := header) (by simp [LoopBuilderFrameTarget, kind])⟩
      | next header ty counter =>
          simp only [LoopBuilderTargets, kind]
          exact ⟨frames.targetBound (target := context.breakTo) (by simp [LoopBuilderFrameTarget]),
            frames.targetBound (target := header) (by simp [LoopBuilderFrameTarget, kind])⟩

theorem LoopBuilderFrames.mono {loop : Option LoopCtx} {before after : LS}
    (frames : LoopBuilderFrames loop before) (extension : before.Ext after) :
    LoopBuilderFrames loop after := by
  cases loop with
  | none => trivial
  | some context =>
      cases kind : context.cont with
      | jump header =>
        simp only [LoopBuilderFrames, kind] at frames ⊢
        rcases frames with ⟨⟨exit, exitAt, exitParams⟩, ⟨block, blockAt, blockParams⟩⟩
        have exitAfter := extension.2 context.breakTo exit exitAt
        rcases exitAfter with ⟨exit', exitAt', exitParams', _⟩
        have blockAfter := extension.2 header block blockAt
        rcases blockAfter with ⟨block', blockAt', blockParams', _⟩
        exact ⟨⟨exit', exitAt', exitParams'.trans exitParams⟩,
          ⟨block', blockAt', blockParams'.trans blockParams⟩⟩

      | next header ty counter =>
        simp only [LoopBuilderFrames, kind] at frames ⊢
        rcases frames with ⟨⟨exit, exitAt, exitParams⟩, ⟨block, blockAt, blockParams⟩⟩
        have exitAfter := extension.2 context.breakTo exit exitAt
        rcases exitAfter with ⟨exit', exitAt', exitParams', _⟩
        have blockAfter := extension.2 header block blockAt
        rcases blockAfter with ⟨block', blockAt', blockParams', _⟩
        exact ⟨⟨exit', exitAt', exitParams'.trans exitParams⟩,
          ⟨block', blockAt', blockParams'.trans blockParams⟩⟩

theorem LoopBuilderFrames.of_blocks {loop : Option LoopCtx} {before after : LS}
    (frames : LoopBuilderFrames loop before) (same : after.blocks = before.blocks) :
    LoopBuilderFrames loop after := by
  cases loop with
  | none => trivial
  | some context =>
      cases kind : context.cont with
      | jump header =>
          simp only [LoopBuilderFrames, kind] at frames ⊢
          rcases frames with ⟨⟨exit, exitAt, exitParams⟩, ⟨block, blockAt, blockParams⟩⟩
          exact ⟨⟨exit, by rw [same]; exact exitAt, exitParams⟩,
            ⟨block, by rw [same]; exact blockAt, blockParams⟩⟩
      | next header ty counter =>
          simp only [LoopBuilderFrames, kind] at frames ⊢
          rcases frames with ⟨⟨exit, exitAt, exitParams⟩, ⟨block, blockAt, blockParams⟩⟩
          exact ⟨⟨exit, by rw [same]; exact exitAt, exitParams⟩,
            ⟨block, by rw [same]; exact blockAt, blockParams⟩⟩

theorem loopBuilderFrames_jump {state : LS} {depth exit header : Nat}
    {exitBlock headerBlock : BlockB}
    (exitAt : state.blocks[exit]? = some exitBlock) (exitParams : exitBlock.params = [])
    (headerAt : state.blocks[header]? = some headerBlock) (headerParams : headerBlock.params = []) :
    LoopBuilderFrames (some ⟨depth, exit, .jump header⟩) state :=
  ⟨⟨exitBlock, exitAt, exitParams⟩, headerBlock, headerAt, headerParams⟩

theorem loopBuilderFrames_next {state : LS} {depth exit header : Nat} {counter : ValueId}
    {ty : IntTy} {exitBlock headerBlock : BlockB}
    (exitAt : state.blocks[exit]? = some exitBlock) (exitParams : exitBlock.params = [])
    (headerAt : state.blocks[header]? = some headerBlock)
    (headerParams : headerBlock.params = [(counter, .data (.int ty))]) :
    LoopBuilderFrames (some ⟨depth, exit, .next header ty counter⟩) state :=
  ⟨⟨exitBlock, exitAt, exitParams⟩, headerBlock, headerAt, headerParams⟩

theorem LoopBuilderFrames.targetParams {loop : Option LoopCtx} {state : LS}
    (frames : LoopBuilderFrames loop state) {target : BlockId}
    (isTarget : LoopBuilderFrameTarget loop target) :
    ∃ block, state.blocks[target]? = some block ∧
      (block.params = [] ∨ ∃ id ty, block.params = [(id, .data (.int ty))]) := by
  cases loop with
  | none => cases isTarget
  | some context =>
      cases kind : context.cont with
      | jump header =>
          simp only [LoopBuilderFrameTarget, kind] at isTarget
          simp only [LoopBuilderFrames, kind] at frames
          rcases frames with ⟨⟨exit, exitAt, exitParams⟩, ⟨head, headAt, headParams⟩⟩
          rcases isTarget with isExit | isHeader
          · subst target
            exact ⟨exit, exitAt, Or.inl exitParams⟩
          · subst target
            exact ⟨head, headAt, Or.inl headParams⟩
      | next header ty counter =>
          simp only [LoopBuilderFrameTarget, kind] at isTarget
          simp only [LoopBuilderFrames, kind] at frames
          rcases frames with ⟨⟨exit, exitAt, exitParams⟩, ⟨head, headAt, headParams⟩⟩
          rcases isTarget with isExit | isHeader
          · subst target
            exact ⟨exit, exitAt, Or.inl exitParams⟩
          · subst target
            exact ⟨head, headAt, Or.inr ⟨counter, ty, headParams⟩⟩

def TermEdgesFramed (loop : Option LoopCtx) (base state : LS) : Prop :=
  ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
    state.blocks[source]? = some body →
    Inst.term term ∈ body.insts.toList → target ∈ term.successors →
    target < base.blocks.size →
    (∃ old, base.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
      LoopBuilderFrameTarget loop target

theorem TermEdgesFramed.refl (loop : Option LoopCtx) (state : LS) :
    TermEdgesFramed loop state state := by
  intro source body term target row member successor targetBound
  exact Or.inl ⟨body, row, member⟩

theorem TermEdgesFramed.of_blocks {loop : Option LoopCtx} {base before after : LS}
    (framed : TermEdgesFramed loop base before) (same : after.blocks = before.blocks) :
    TermEdgesFramed loop base after := by
  intro source body term target row member successor targetBound
  rw [same] at row
  exact framed source body term target row member successor targetBound

theorem TermEdgesFramed.weakenLoop {inner outer : Option LoopCtx} {base state : LS}
    (framed : TermEdgesFramed inner base state)
    (fresh : ∀ target, LoopBuilderFrameTarget inner target → base.blocks.size ≤ target) :
    TermEdgesFramed outer base state := by
  intro source body term target row member successor targetBound
  rcases framed source body term target row member successor targetBound with old | innerFrame
  · exact Or.inl old
  · exact False.elim (Nat.not_lt_of_ge (fresh target innerFrame) targetBound)

def GeneratedTargetFrameRun (loop : Option LoopCtx) (action : B α) : Prop :=
  ∀ base env current result after, base.Ext current → LoopBuilderFrames loop base →
    TermEdgesFramed loop base current → action env current = (result, after) →
    TermEdgesFramed loop base after ∧ current.Ext after

theorem TermEdgesFramed.extend {loop : Option LoopCtx} {base current after : LS}
    (oldFrames : TermEdgesFramed loop base current)
    (newTargets : ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
      after.blocks[source]? = some body →
      Inst.term term ∈ body.insts.toList → target ∈ term.successors →
      target < base.blocks.size →
      (∃ old, current.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
        LoopBuilderFrameTarget loop target) :
    TermEdgesFramed loop base after := by
  intro source body term target row instMember successor targetBound
  rcases newTargets source body term target row instMember successor targetBound with old | frame
  · rcases old with ⟨previous, previousRow, previousTerm⟩
    exact oldFrames source previous term target previousRow previousTerm successor targetBound
  · exact Or.inr frame

theorem TermEdgesFramed.rebase {outer inner : Option LoopCtx} {base middle after : LS}
    (oldFrames : TermEdgesFramed outer base middle)
    (newFrames : TermEdgesFramed inner middle after)
    (extension : base.Ext middle)
    (transfer : ∀ target, LoopBuilderFrameTarget inner target →
      LoopBuilderFrameTarget outer target ∨ base.blocks.size ≤ target) :
    TermEdgesFramed outer base after := by
  intro source body term target row member successor targetBound
  have middleBound := Nat.lt_of_lt_of_le targetBound extension.1
  rcases newFrames source body term target row member successor middleBound with previous | innerTarget
  · rcases previous with ⟨old, oldRow, oldMember⟩
    exact oldFrames source old term target oldRow oldMember successor targetBound
  · rcases transfer target innerTarget with outerTarget | fresh
    · exact Or.inr outerTarget
    · exact False.elim (Nat.not_lt_of_ge fresh targetBound)

theorem TermEdgesFramed.compose {loop : Option LoopCtx} {base current after : LS}
    (oldFrames : TermEdgesFramed loop base current)
    (newFrames : TermEdgesFramed none current after)
    (baseCurrent : base.Ext current) : TermEdgesFramed loop base after := by
  apply TermEdgesFramed.extend oldFrames
  intro source body term target row member successor targetBound
  have currentBound := Nat.lt_of_lt_of_le targetBound baseCurrent.1
  rcases newFrames source body term target row member successor currentBound with old | impossible
  · exact Or.inl old
  · cases impossible

theorem TermEdgesFramed.emitTermAt {loop : Option LoopCtx} {base current after : LS}
    {env : LEnv} {result : Unit} {term : Term}
    (oldFrames : TermEdgesFramed loop base current)
    (run : emitTerm term env current = (result, after))
    (targets : ∀ target, target ∈ term.successors → target < base.blocks.size →
      LoopBuilderFrameTarget loop target) : TermEdgesFramed loop base after := by
  have afterEq : after = (emitTerm term env current).2 := (congrArg Prod.snd run).symm
  cases currentBlock : current.cur with
  | none =>
      rw [emitTerm_none term env currentBlock] at afterEq
      subst after
      exact oldFrames
  | some block =>
      rw [emitTerm_run term env currentBlock] at afterEq
      apply TermEdgesFramed.extend oldFrames
      intro source body emitted target row member successor targetBound
      rw [afterEq] at row
      simp only [Array.getElem?_modify] at row
      by_cases same : block = source
      · subst source
        simp only [↓reduceIte, Option.map_eq_some_iff] at row
        obtain ⟨old, oldAt, rfl⟩ := row
        rcases List.mem_append.mp (by simpa only [Array.toList_push] using member) with oldMember | addedMember
        · exact Or.inl ⟨old, oldAt, oldMember⟩
        · simp at addedMember
          subst emitted
          exact Or.inr (targets target successor targetBound)
      · simp only [same, ite_false] at row
        exact Or.inl ⟨body, row, member⟩

theorem TermEdgesFramed.patchTermAt {loop : Option LoopCtx} {base current after : LS}
    {env : LEnv} {result : Unit} {block : BlockId} {term : Term}
    (oldFrames : TermEdgesFramed loop base current)
    (run : patchTerm block term env current = (result, after))
    (targets : ∀ target, target ∈ term.successors → target < base.blocks.size →
      LoopBuilderFrameTarget loop target) : TermEdgesFramed loop base after := by
  have afterEq : after = (patchTerm block term env current).2 := (congrArg Prod.snd run).symm
  rw [patchTerm_run] at afterEq
  apply TermEdgesFramed.extend oldFrames
  intro source body emitted target row member successor targetBound
  rw [afterEq] at row
  rw [Array.getElem?_modify] at row
  by_cases same : block = source
  · subst source
    simp only [↓reduceIte, Option.map_eq_some_iff] at row
    obtain ⟨old, oldAt, rfl⟩ := row
    rcases List.mem_append.mp (by simpa only [Array.toList_push] using member) with oldMember | addedMember
    · exact Or.inl ⟨old, oldAt, oldMember⟩
    · simp at addedMember
      subst emitted
      exact Or.inr (targets target successor targetBound)
  · simp only [same, ite_false] at row
    exact Or.inl ⟨body, row, member⟩

theorem patchTerm_ext {state : LS} {block : BlockId} {term : Term}
    {env : LEnv} {result : Unit} {after : LS}
    (run : patchTerm block term env state = (result, after)) : state.Ext after := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨by simp, fun index old oldAt => ?_⟩
  by_cases same : block = index
  · subst index
    refine ⟨{ old with insts := old.insts.push (.term term) }, ?_, rfl,
      [Inst.term term], ?_⟩
    · rw [Array.getElem?_modify]
      simp [oldAt]
    · simp [Array.toList_push, List.append_assoc]
  · rw [Array.getElem?_modify]
    simp [same, oldAt]

theorem GeneratedTargetFrameRun.bind {loop : Option LoopCtx} {first : B α} {next : α → B β}
    (one : GeneratedTargetFrameRun loop first)
    (two : ∀ value, GeneratedTargetFrameRun loop (next value)) :
    GeneratedTargetFrameRun loop (first >>= next) := by
  intro base env current result after baseCurrent frames terms run
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have firstResult := one base env current value middle baseCurrent frames terms firstRun
  have baseMiddle := baseCurrent.trans firstResult.2
  have nextResult := two value base env middle result after baseMiddle frames firstResult.1 nextRun
  exact ⟨nextResult.1, firstResult.2.trans nextResult.2⟩

theorem GeneratedTargetFrameRun.withLoop {action : B α} {outer : Option LoopCtx}
    (checked : GeneratedTargetFrameRun none action) : GeneratedTargetFrameRun outer action := by
  intro base env current result after baseCurrent frames terms run
  have result := checked current env current result after (.refl _) trivial
    (TermEdgesFramed.refl none current) run
  exact ⟨terms.compose result.1 baseCurrent, result.2⟩

theorem generatedTargetFrame_pure (loop : Option LoopCtx) (value : α) :
    GeneratedTargetFrameRun loop (pure value) := by
  intro base env current result after baseCurrent frames terms run
  rw [pure_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_read (loop : Option LoopCtx) :
    GeneratedTargetFrameRun loop (read : B LEnv) := by
  intro base env current result after baseCurrent frames terms run
  rw [read_apply] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_get (loop : Option LoopCtx) :
    GeneratedTargetFrameRun loop (get : B LS) := by
  intro base env current result after baseCurrent frames terms run
  rw [get_apply] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_emitTerm (loop : Option LoopCtx) (term : Term)
    (targets : ∀ (base : LS) (target : BlockId), target ∈ term.successors →
      target < base.blocks.size →
      LoopBuilderFrameTarget loop target) :
    GeneratedTargetFrameRun loop (emitTerm term) := by
  intro base env current result after baseCurrent frames oldFrames run
  have advancing := (advB_emitTerm term env current result after run).ext
  exact ⟨oldFrames.emitTermAt run (fun target successor targetBound =>
    targets base target successor targetBound), advancing⟩

theorem generatedTargetFrame_emitNoSuccessors (loop : Option LoopCtx) (term : Term)
    (noSuccessors : term.successors = []) : GeneratedTargetFrameRun loop (emitTerm term) := by
  apply generatedTargetFrame_emitTerm loop term
  intro base target successor targetBound
  rw [noSuccessors] at successor
  cases successor

theorem generatedTargetFrame_emitDef (loop : Option LoopCtx) (op : Op) :
    GeneratedTargetFrameRun loop (emitDef op) := by
  intro base env current result after baseCurrent frames oldFrames run
  have advancing := (advB_emitDef op env current result after run).ext
  have afterEq : after = (emitDef op env current).2 := (congrArg Prod.snd run).symm
  cases currentBlock : current.cur with
  | none =>
      rw [emitDef_none op env currentBlock] at afterEq
      subst after
      exact ⟨oldFrames, advancing⟩
  | some block =>
      rw [emitDef_run op env currentBlock] at afterEq
      have newTargets : ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
          after.blocks[source]? = some body →
          Inst.term term ∈ body.insts.toList → target ∈ term.successors →
          target < base.blocks.size →
          (∃ old, current.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
            LoopBuilderFrameTarget loop target := by
        intro source body term target row member successor targetBound
        rw [afterEq] at row
        rw [Array.getElem?_modify] at row
        by_cases same : block = source
        · subst source
          simp only [↓reduceIte, Option.map_eq_some_iff] at row
          obtain ⟨old, oldAt, rfl⟩ := row
          rcases List.mem_append.mp (by simpa only [Array.toList_push] using member) with oldMember | addedMember
          · exact Or.inl ⟨old, oldAt, oldMember⟩
          · simp at addedMember
        · simp only [same, ite_false] at row
          exact Or.inl ⟨body, row, member⟩
      exact ⟨TermEdgesFramed.extend oldFrames newTargets, advancing⟩

theorem generatedTargetFrame_emitEffect (loop : Option LoopCtx) (effect : Effect) :
    GeneratedTargetFrameRun loop (emitEffect effect) := by
  intro base env current result after baseCurrent frames oldFrames run
  have advancing := (advB_emitEffect effect env current result after run).ext
  have afterEq : after = (emitEffect effect env current).2 := (congrArg Prod.snd run).symm
  cases currentBlock : current.cur with
  | none =>
      rw [emitEffect_none effect env currentBlock] at afterEq
      subst after
      exact ⟨oldFrames, advancing⟩
  | some block =>
      rw [emitEffect_run effect env currentBlock] at afterEq
      have newTargets : ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
          after.blocks[source]? = some body →
          Inst.term term ∈ body.insts.toList → target ∈ term.successors →
          target < base.blocks.size →
          (∃ old, current.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
            LoopBuilderFrameTarget loop target := by
        intro source body term target row member successor targetBound
        rw [afterEq] at row
        rw [Array.getElem?_modify] at row
        by_cases same : block = source
        · subst source
          simp only [↓reduceIte, Option.map_eq_some_iff] at row
          obtain ⟨old, oldAt, rfl⟩ := row
          rcases List.mem_append.mp (by simpa only [Array.toList_push] using member) with oldMember | addedMember
          · exact Or.inl ⟨old, oldAt, oldMember⟩
          · simp at addedMember
        · simp only [same, ite_false] at row
          exact Or.inl ⟨body, row, member⟩
      exact ⟨TermEdgesFramed.extend oldFrames newTargets, advancing⟩

theorem generatedTargetFrame_newBlock (loop : Option LoopCtx) (types : List VTy) :
    GeneratedTargetFrameRun loop (newBlock types) := by
  intro base env current result after baseCurrent frames oldFrames run
  have afterEq : after = (newBlock types env current).2 := (congrArg Prod.snd run).symm
  have advancing : current.Ext after := by
    have generated := newBlock_run_general types env current
    rw [generated] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact (LS.Adv.newBlk current ⟨(paramIds types current.vals).zip types, #[]⟩
      (vs := pushParamTypes types current.vals) (by
        rw [array_size_pushParamTypes]
        omega)).ext
  have newTargets : ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
      after.blocks[source]? = some body → Inst.term term ∈ body.insts.toList →
      target ∈ term.successors → target < base.blocks.size →
      (∃ old, current.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
        LoopBuilderFrameTarget loop target := by
    intro source body term target row member successor targetBound
    rw [afterEq, newBlock_run_general] at row
    simp only [Array.getElem?_push] at row
    by_cases fresh : source = current.blocks.size
    · simp [fresh] at row
      subst body
      simp at member
    · simp [fresh] at row
      exact Or.inl ⟨body, row, member⟩
  exact ⟨TermEdgesFramed.extend oldFrames newTargets, advancing⟩

theorem generatedTargetFrame_setCur (loop : Option LoopCtx) (currentBlock : Option BlockId) :
    GeneratedTargetFrameRun loop (setCur currentBlock) := by
  intro base env current result after baseCurrent frames oldFrames run
  have afterEq : after = (setCur currentBlock env current).2 := (congrArg Prod.snd run).symm
  have advancing : current.Ext after := by
    rw [setCur_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .refl _
  have newTargets : ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
      after.blocks[source]? = some body → Inst.term term ∈ body.insts.toList →
      target ∈ term.successors → target < base.blocks.size →
      (∃ old, current.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
        LoopBuilderFrameTarget loop target := by
    intro source body term target row member successor targetBound
    rw [afterEq, setCur_run] at row
    exact Or.inl ⟨body, row, member⟩
  exact ⟨TermEdgesFramed.extend oldFrames newTargets, advancing⟩

end Goose.Lower
