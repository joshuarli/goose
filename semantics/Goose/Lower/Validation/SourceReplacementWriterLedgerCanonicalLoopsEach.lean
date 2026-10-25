import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsEachGrowth
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsEachBody
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsEachPrelude
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsEachSource
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalLoopsSourcePaths
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEachStages
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsFacts
import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open ReplacementContentFlowSource Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

open SummaryPreservation.ReplayBuilder

private theorem canonical_each_regrow_state (owner : Option ValueId) (le : LEnv) (state : LS) :
    (regrowOf owner le state).2 = state := by
  cases owner with
  | none => rfl
  | some value =>
    simp only [regrowOf, growOwner, bind_run, valTy_run]
    cases (valTy value le state).1 with
    | view _ _ => rfl
    | data type => cases type <;> rfl

private theorem canonical_each_sample_cur (regrow : Bool) (view : ValueId) (le : LEnv) (state : LS) :
    (eachSampled regrow view le state).2.cur = state.cur := by
  cases regrow <;> cases current : state.cur <;> simp [eachSampled, emitDef_run, emitDef_none, pure_run, current]



theorem canonical_typedEachOccurrence {typingEnv output : TEnv} {env : PEnv} {variableId : VarId} {indexVar : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId}
    {scope start finish : Nat} {before after : RState} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {ls : LS} {upper : Prov}
    (loop : Option LoopCtx) (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (annotations : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (location : ∃ path, DemandNodeAt siteRoot path (.statement (.forEach variableId indexVar view byRef body origin)))
    (sourceCursor : ∃ path, SourceLoweringAt ownerRoot (lowerEnv env.mod env.impl.vars env.impl.results.toList) ownerInitial path (.statement loop (.forEach variableId indexVar view byRef body origin)) ls)
    (source : tyStmt typingEnv scope (.forEach variableId indexVar view byRef body origin) start = .ok (output, finish))
    (replayed : rpStmt env (.forEach variableId indexVar view byRef body origin) before = .ok ((), after))
    (wholeEffect : EffectRefinement (lowerContextAt env.mod env.ctx env.impl) after.eff target)
    (scopes : SourceScopesWithin scopeCount (Core.blockScopes none body))
    (stackBounds : typingEnv.inExpr = false → ∀ entered ∈ ls.stack, entered < scopeCount)
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (ready : ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
      (typedContextSlotUpper env.mod env.ctx env.impl) ls upper)
    (sites : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls (lowerContextAt env.mod env.ctx env.impl) vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt (lowerStmt loop (.forEach variableId indexVar view byRef body origin)
      (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot
      (lowerContextAt env.mod env.ctx env.impl)
      (lowerStmt loop (.forEach variableId indexVar view byRef body origin)
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (continuation : NativeBuilderContinuation (lowerContextAt env.mod env.ctx env.impl)
      (lowerStmt loop (.forEach variableId indexVar view byRef body origin)
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2)
    (placeChild : ∀ place, view = .of place → CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place ls upper)
    (expressionChild : ∀ expression, view = .val expression → CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression ls upper)
    (bodyChild : ∀ targets depth header exit counter value state provenance,
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let sampled := lowerEachSource view le ls
      let regrow := (regrowOf sampled.1.1 le sampled.2).1
      let prelude := nativeEachPrefix regrow sampled.1.2 le sampled.2
      let entry := eachLoopBodyEntry regrow sampled.1.1 prelude.sampled prelude.counter le prelude.state
      let address := Goose.Lower.emitDef (.refElem sampled.1.2 counter) le entry
      let produced := eachElemValue variableId byRef address.1 le address.2
      header = prelude.header → counter = prelude.counter → value = produced.1 → state = produced.2 →
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline {typingEnv with loops := typingEnv.loops + 1, visible := variableId :: indexVar.toList ++ typingEnv.visible}
        env results vt target scopeCount siteRoot targets (some ⟨depth, exit, .next header .i64 counter⟩)
        ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body state provenance) :
    ∃ next, ReplayBuilder (lower env.mod) results vt (lowerContextAt env.mod env.ctx env.impl) target
        (lowerEnv env.mod env.impl.vars env.impl.results.toList) scopeCount
        (typedContextSlotUpper env.mod env.ctx env.impl)
        (lowerStmt loop (.forEach variableId indexVar view byRef body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved (contextTypedResultUpper env.mod env.ctx) ls upper
        (lowerStmt loop (.forEach variableId indexVar view byRef body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 next ∧
      OccurrenceLedger env (.statement (.forEach variableId indexVar view byRef body origin)) (lowerContextAt env.mod env.ctx env.impl) vt next ls
        (lowerStmt loop (.forEach variableId indexVar view byRef body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2 ∧
      CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env siteRoot siteTargets (lowerEnv env.mod env.impl.vars env.impl.results.toList)
        (lowerStmt loop (.forEach variableId indexVar view byRef body origin) (lowerEnv env.mod env.impl.vars env.impl.results.toList) ls).2
        (lowerContextAt env.mod env.ctx env.impl) vt next := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let expected := contextTypedResultUpper env.mod env.ctx
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declaration, indexDeclaration, viewTyping, variableTyping, bodyTyping, _⟩ := tyStmt_forEach_children source
  obtain ⟨sourceStart, sourceRoots, viewState, boundState, bodyRoots, bodyRange, bodyState,
    viewReplay, bindingReplay, bodyReplay, afterEq⟩ := rpStmt_each_children replayed
  have viewEffect := each_view_effect_bound bindingReplay bodyReplay afterEq wholeEffect
  let sampledSource := lowerEachSource view le ls
  let regrow := (regrowOf sampledSource.1.1 le sampledSource.2).1
  let bodyAction := fun depth header exit counter => do
    let address ← Goose.Lower.emitDef (.refElem sampledSource.1.2 counter)
    let value ← eachElemValue variableId byRef address
    lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
      ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body
  let tail : B Unit := do
    let regrow ← regrowOf sampledSource.1.1
    let sampled ← eachSampled regrow sampledSource.1.2
    let initial ← Goose.Lower.emitDef (.constInt .i64 0)
    whenLive () fun _ => do
      let (header, parameters) ← newBlock [.data (.int .i64)]
      let counter := parameters.headD 0
      Goose.Lower.emitTerm (.br header [initial])
      Goose.Lower.setCur (some header)
      lowerEach regrow sampledSource.1.1 sampled header counter (fun depth exit => bodyAction depth header exit counter)
  have whole : lowerStmt loop (.forEach variableId indexVar view byRef body origin) le ls = tail le sampledSource.2 := by
    simp only [lowerStmt, tail, bind_run]
    cases indexVar <;> rfl
  have bodyAdvance : ∀ depth header exit counter, AdvB (bodyAction depth header exit counter) := by
    intro depth header exit counter
    exact AdvB.bind (advB_emitDef (.refElem sampledSource.1.2 counter)) (fun address =>
      AdvB.bind (advB_eachElemValue variableId byRef address) (fun value =>
        advB_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body))
  have bodyTypes : ∀ depth header exit counter, TypeRun (bodyAction depth header exit counter) := by
    intros
    exact TypeRun.bind (types_emitDef _) (fun address => TypeRun.bind (types_eachElemValue _ _ address) (fun _ => types_lowerBlock _ _ _ _))
  have tailTypes : TypeRun tail := by
    apply TypeRun.bind (types_regrowOf _)
    intro growing
    apply TypeRun.bind (types_eachSampled _ _)
    intro sampled
    apply TypeRun.bind (types_emitDef _)
    intro initial
    apply types_whenLive
    intro _
    apply TypeRun.bind (types_newBlock _)
    intro pair
    rcases pair with ⟨header, parameters⟩
    exact TypeRun.bind (types_emitTerm _) (fun _ => TypeRun.bind (types_setCur _)
      (fun _ => types_lowerEach _ _ _ _ _ (fun depth exit => bodyTypes depth header exit (parameters.headD 0))))
  have tailAdvance : AdvB tail := by
    apply AdvB.bind (advB_regrowOf _)
    intro growing
    apply AdvB.bind (advB_eachSampled _ _)
    intro sampled
    apply AdvB.bind (advB_emitDef _)
    intro initial
    apply advB_whenLive ()
    intro _
    exact advB_header1 (.data (.int .i64)) initial
      (tail := fun header counter => lowerEach growing sampledSource.1.1 sampled header counter
        (fun depth exit => bodyAction depth header exit counter))
      (fun _ _ => advB_lowerEach _ _ _ _ _ (fun depth exit => bodyAdvance depth _ exit _))
  have sourceProjects := projects.of_advance
    (tailAdvance le sampledSource.2 _ _ (by rw [whole]))
  have sourceContinuation := continuation.of_advance
    (tailAdvance le sampledSource.2 _ _ (by rw [whole]))
  have sourceNative : NativeRows vt sampledSource.2 := by
    apply native.of_prefix
    rw [whole]
    exact tailTypes le sampledSource.2 _ _ rfl
  have viewAt : DemandNodeAt (.statement (.forEach variableId indexVar view byRef body origin)) [0] (.view view) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have bodyAt : DemandNodeAt (.statement (.forEach variableId indexVar view byRef body origin)) [1] (.block body) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  have viewSource : ∃ path, DemandNodeAt siteRoot path (.view view) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [0], sourcePath_append parent viewAt⟩
  have bodySource : ∃ path, DemandNodeAt siteRoot path (.block body) := by
    obtain ⟨path, parent⟩ := location
    exact ⟨path ++ [1], sourcePath_append parent bodyAt⟩
  let sourceView : canonical_ViewOccurrenceSource env (.statement (.forEach variableId indexVar view byRef body origin)) sourceRoots :=
    ⟨[0], view, sourceStart, viewState, viewAt, viewReplay⟩
  obtain ⟨sourceProv, sourceReady, sourceValue, sourceGrowth, sourceLedger, sourceSites⟩ :=
    canonical_typedEachSourceOccurrence tables viewSource (by
      obtain ⟨path, located⟩ := sourceCursor
      exact ⟨path ++ [0], located.child rfl⟩) viewTyping viewReplay viewEffect closed ready sites targetBounds
      generated sourceNative sourceProjects sourceContinuation placeChild expressionChild
  have sourceAdv := advB_lowerEachSource view le ls sampledSource.1 sampledSource.2 rfl
  have sourceGenerated := generated.lowerEachSource view (rfl : lowerEachSource view le ls = sampledSource)
  have sourceReturns : ReturnMembershipFrame ls sampledSource.2 :=
    returnFrame_lowerEachSource view (tyView_returnFree view viewTyping) le ls sampledSource.1 sampledSource.2 rfl
  have sourceTransfer : ReturnBoundsPreserved expected ls upper sampledSource.2 sourceProv :=
    .frame ready.symbols ready.roots.valueSize sourceGrowth sourceReturns
  have regrowRun : regrowOf sampledSource.1.1 le sampledSource.2 = (regrow, sampledSource.2) := Prod.ext rfl (canonical_each_regrow_state _ _ _)
  cases current : sampledSource.2.cur with
  | none =>
    have stopped : lowerStmt loop (.forEach variableId indexVar view byRef body origin) le ls = ((), sampledSource.2) := by
      rw [whole]
      simp only [tail, bind_run, regrowRun]
      cases regrow <;> simp [eachSampled, pure_run, emitDef_none _ _ current, whenLive_none _ _ _ current]
    exact ⟨sourceProv, by rw [stopped]; exact sourceReady, sourceGrowth, by rw [stopped]; exact sourceTransfer,
      by rw [stopped]; exact sourceLedger.underRoot viewAt, by rw [stopped]; exact sourceSites⟩
  | some block =>
    have sourceLive : sampledSource.2.cur.isSome = true := by simp [current]
    have same : lowerStmt loop (.forEach variableId indexVar view byRef body origin) le ls =
        nativeEachPrelude regrow sampledSource.1.1 sampledSource.1.2 bodyAction le sampledSource.2 := by
      rw [whole]
      simp only [tail, bind_run, regrowRun, nativeEachPrelude]
      let sampled := eachSampled regrow sampledSource.1.2 le sampledSource.2
      let initial := Goose.Lower.emitDef (.constInt .i64 0) le sampled.2
      have sampleCurrent : sampled.2.cur = some block := (canonical_each_sample_cur _ _ _ _).trans current
      have initialCurrent : initial.2.cur = some block := by simp [initial, emitDef_run _ _ sampleCurrent, sampleCurrent]
      change whenLive () _ le initial.2 = _
      rw [whenLive_some _ _ _ initialCurrent]
      rfl
    have nativePrelude : NativeRows vt (nativeEachPrelude regrow sampledSource.1.1 sampledSource.1.2 bodyAction le sampledSource.2).2 := by rw [same] at native; exact native
    have preludeProjects := projects
    rw [same] at preludeProjects
    have preludeContinuation := continuation
    rw [same] at preludeContinuation
    have actualView := native_eachSource_view_row tables generated viewTyping sourceLive
    have row : typingEnv.vars[variableId]? = some localVar := (declare_ok _ _ _ _ _ declaration).2.1
    have sourceRow : env.impl.vars[variableId]? = some localVar := by simpa only [tables.variablesEq] using row
    have actualRow : le.vars[variableId]? = some localVar := by simpa [le, lowerEnv, tables.variablesEq] using row
    have flat := source_view_element_flat view checked viewTyping
    have nonref : element.isRefLike = false := by cases element <;> simp_all [Ty.flat, Ty.isRefLike]
    have reference : byRef = true → ∃ lv mu, le.vars[variableId]? = some lv ∧ lv.ty = .ref mu element := by
      intro active
      obtain ⟨mu, type⟩ := (by simpa only [active, ite_true] using (loopVarOk_ok _ _ _ _ _ _ variableTyping).2 : ∃ mu, localVar.ty = .ref mu element)
      exact ⟨localVar, mu, actualRow, type⟩
    have owner : regrow = true → sampledSource.1.1.isSome = true := by
      intro active
      cases ownerEq : sampledSource.1.1 with
      | some address => rfl
      | none => simp [regrow, ownerEq, regrowOf] at active
    have ownerView : regrow = true → ∃ place, view = .of place := by
      intro active
      cases view with
      | of place => exact ⟨place, rfl⟩
      | val expression =>
        have ownerNone : sampledSource.1.1 = none := by simp [sampledSource, lowerEachSource, bind_run, pure_run]
        have impossible := owner active
        simp [ownerNone] at impossible
    have reads : byRef = false ∨ regrow = true →
        ∀ item ∈ (lowerContextAt env.mod env.ctx env.impl).storageTargets (rootsTargets sourceRoots),
          item ∈ (lowerContextAt env.mod env.ctx env.impl).storageTargets target.reads := by
      intro required
      apply each_source_read_bound viewReplay bindingReplay bodyReplay afterEq wholeEffect
      exact required.elim Or.inl (fun active => Or.inr (ownerView active))
    have binding : byRef = true → ∀ actual, Goose.GIR.RootsRefine (lowerContextAt env.mod env.ctx env.impl) actual sourceRoots →
        ∀ root ∈ actual, root ∈ rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId := by
      intro active actual refined
      obtain ⟨lv, mu, localRow, localType⟩ := reference active
      have sameVar : lv = localVar := Option.some.inj (localRow.symm.trans actualRow)
      subst lv
      have ordinary : localVar.ty.isRefSlice = false := by rw [localType]; cases element <;> simp_all [Ty.flat, Ty.isRefSlice]
      exact each_source_binding_bound annotations sourceRow ordinary (by simpa only [active, ite_true] using bindingReplay) refined
    have originBound : origin < env.mod.origins.size := by
      obtain ⟨_, _, originCheck, _⟩ := (st_bind_ok _ _ _ _).mp source
      simpa only [tables.moduleEq] using ((checkOrg_ok _ _ _ _).mp originCheck).1
    obtain ⟨_, boundVar, boundRow, _, indexRows⟩ := tyStmt_forEach_bindings source
    have variableBound : variableId < env.impl.vars.size := by simpa only [tables.variablesEq] using (Array.getElem?_eq_some_iff.mp boundRow).1
    have indexBound : ∀ index ∈ indexVar.toList, index < env.impl.vars.size := by
      intro index member
      cases indexVar with
      | none => cases member
      | some j =>
        have indexEq : index = j := by simpa only [Option.toList, List.mem_singleton] using member
        subst index
        obtain ⟨_, indexVariable, indexRow, _⟩ := indexRows j rfl
        simpa only [tables.variablesEq] using (Array.getElem?_eq_some_iff.mp indexRow).1
    obtain ⟨next, nextReady, growth, transfer, preludeLedger, preludeSites⟩ := canonical_eachPreludeOccurrence
      (root := .statement (.forEach variableId indexVar view byRef body origin)) sourceReady sourceSites
      (targetBounds.mono sourceAdv.ext) expected regrow sampledSource.1.1 sampledSource.1.2
      element sourceRoots bodyAction sourceView (by simpa only [sourceView] using ownerView) sourceLive (sourceValue sourceLive) closed owner (fun active => reads (Or.inr active))
      actualView sourceGenerated nativePrelude preludeProjects preludeContinuation
      bodyAdvance
      bodyTypes
      (by
        intro provenance
        dsimp only
        intro entryReady entrySites entryBounds entryGenerated entryNative headerBound exitBound counterBound counterEmpty viewBound viewRefined viewRow counterRow entryProjects entryContinuation
        let prelude := nativeEachPrefix regrow sampledSource.1.2 le sampledSource.2
        let length := eachLen regrow sampledSource.1.1 prelude.sampled le prelude.state
        let compared := Goose.Lower.emitDef (.cmp .lt .i64 prelude.counter length.1) le length.2
        let split := fork compared.1 le compared.2
        let entry := eachLoopBodyEntry regrow sampledSource.1.1 prelude.sampled prelude.counter le prelude.state
        have counterTyped : vt[prelude.counter]? = some (some (.data (.int .i64))) :=
          (entryNative.of_prefix (bodyTypes compared.2.stack.length prelude.header split.1.2 prelude.counter le entry _ _ rfl)) _ _ counterRow
        apply canonical_eachBodyOccurrence entryReady entrySites entryBounds expected variableId indexVar byRef sampledSource.1.2 prelude.counter element sourceRoots origin
          compared.2.stack.length prelude.header split.1.2 body sourceView (by rfl) viewBound counterBound viewRefined counterEmpty closed reference
          (fun inactive => reads (Or.inl inactive)) nonref binding viewRow counterRow entryGenerated entryNative entryProjects entryContinuation
        intro producedProv
        dsimp only
        intro producedReady producedSites producedBounds producedGenerated producedNative blocks values roots bodyProjects bodyContinuation
        let address := Goose.Lower.emitDef (.refElem sampledSource.1.2 prelude.counter) le entry
        let produced := eachElemValue variableId byRef address.1 le address.2
        have targets : LoopBuilderTargets (some ⟨compared.2.stack.length, split.1.2, .next prelude.header .i64 prelude.counter⟩) produced.2 :=
          ⟨Nat.lt_of_lt_of_le exitBound blocks, Nat.lt_of_lt_of_le headerBound blocks⟩
        have replayBounds : LoopReplayBounds (some ⟨compared.2.stack.length, split.1.2, .next prelude.header .i64 prelude.counter⟩)
            scopeCount produced.2 := by
          have addressAdv := advB_emitDef (.refElem sampledSource.1.2 prelude.counter) le entry address.1 address.2 rfl
          have valueAdv := advB_eachElemValue variableId byRef address.1 le address.2 produced.1 produced.2 rfl
          refine ⟨Nat.lt_of_lt_of_le counterBound (Nat.le_trans addressAdv.vals valueAdv.vals), ?_⟩
          have stackEq : produced.2.stack = compared.2.stack :=
            (advB_eachElemValue variableId byRef address.1 le address.2 produced.1 produced.2 rfl).stack.trans
              ((advB_emitDef (.refElem sampledSource.1.2 prelude.counter) le entry address.1 address.2 rfl).stack.trans
                (native_loopBody_entry_stack compared.1 le compared.2))
          rw [stackEq]
          simp
        obtain ⟨next, nextReady, _, retained, bodyTransfer, bodyLedger, bodySites⟩ := bodyChild
          (split.1.2 :: prelude.header :: siteTargets) compared.2.stack.length prelude.header split.1.2 prelude.counter produced.1 produced.2 producedProv
          rfl rfl rfl rfl bodySource (by
            obtain ⟨path, located⟩ := sourceCursor
            refine ⟨path ++ [1], located.child ?_⟩
            exact canonical_each_body_child le ls loop variableId indexVar view byRef body origin sourceLive) bodyType viewFinish finish boundState bodyState bodyRoots bodyRange bodyTyping bodyReplay
          (by simpa only [afterEq] using wholeEffect) scopes
          (by
            intro item member
            simp only [List.mem_cons, List.mem_map] at member
            rcases member with rfl | ⟨j, member, rfl⟩
            · exact ⟨variableBound, originBound⟩
            · exact ⟨indexBound j member, originBound⟩)
          (fun _ => values) roots
          (by
            intro plain entered member
            apply stackBounds plain entered
            change entered ∈ produced.2.stack at member
            have valueStack := (advB_eachElemValue variableId byRef address.1 le address.2 produced.1 produced.2 rfl).stack
            have addressStack := (advB_emitDef (.refElem sampledSource.1.2 prelude.counter) le entry address.1 address.2 rfl).stack
            rw [valueStack, addressStack, native_each_entry_stack, native_each_prefix_stack, sourceAdv.stack] at member
            exact member)
          producedReady producedSites producedBounds producedGenerated targets replayBounds counterTyped
          (by
            intro target member
            change target ∈ [split.1.2, prelude.header] at member
            rcases List.mem_cons.mp member with first | rest
            · exact List.mem_cons.mpr (Or.inl first)
            · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp rest))))
          producedNative bodyProjects bodyContinuation
        exact ⟨next, nextReady, retained, bodyTransfer, bodyLedger.underRoot bodyAt, bodySites⟩)
    refine ⟨next, by rw [same]; exact nextReady, ?_, ?_, ?_, ?_⟩
    · intro old bound
      have sourceBound : old < sourceProv.vals.size := by
        rw [sourceReady.roots.valueSize]
        exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) sourceAdv.vals
      rw [growth old sourceBound, sourceGrowth old bound]
    · rw [same]
      exact sourceTransfer.trans transfer
    · rw [same]
      have nextGrowth : sourceProv.vals.size ≤ next.vals.size := by
        rw [sourceReady.roots.valueSize, nextReady.roots.valueSize]
        have actualGrowth := occurrenceEachPrelude_values regrow sampledSource.1.1 sampledSource.1.2 bodyAction bodyAdvance le sampledSource.2
        simpa only [le, sampledSource] using actualGrowth
      exact ((sourceLedger.underRoot viewAt).retained nextGrowth growth).trans preludeLedger
    · rw [same]
      exact preludeSites

theorem canonical_statementOccurrence_each {typingEnv : TEnv} {env : PEnv} {variableId : VarId} {indexVar : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff}
    {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {loop : Option LoopCtx} {scope : ScopeId} {ls : LS} {upper : Prov}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (annotations : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (closed : ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl))
    (placeChild : ∀ place, view = .of place → CanonicalPlaceOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets place ls upper)
    (expressionChild : ∀ expression, view = .val expression → CanonicalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets expression ls upper)
    (bodyChild : ∀ targets depth header exit counter value state provenance,
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let sampled := lowerEachSource view le ls
      let regrow := (regrowOf sampled.1.1 le sampled.2).1
      let prelude := nativeEachPrefix regrow sampled.1.2 le sampled.2
      let entry := eachLoopBodyEntry regrow sampled.1.1 prelude.sampled prelude.counter le prelude.state
      let address := Goose.Lower.emitDef (.refElem sampled.1.2 counter) le entry
      let produced := eachElemValue variableId byRef address.1 le address.2
      header = prelude.header → counter = prelude.counter → value = produced.1 → state = produced.2 →
      CanonicalBlockOccurrenceReplayAt ownerRoot ownerInitial baseline {typingEnv with loops := typingEnv.loops + 1, visible := variableId :: indexVar.toList ++ typingEnv.visible}
        env results vt target scopeCount siteRoot targets (some ⟨depth, exit, .next header .i64 counter⟩)
        ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body state provenance) :
    CanonicalStatementOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt target scopeCount siteRoot siteTargets loop scope
      (.forEach variableId indexVar view byRef body origin) ls upper := by
  intro location sourceCursor output start finish before after typed replay ceiling scopes stack ready sites targetBounds
    generated loopTargets loopReplay counterTyped included native projects continuation
  have bodyScopes : SourceScopesWithin scopeCount (Core.blockScopes none body) := by
    apply scopes.of_subset
    intro entry member
    exact List.mem_append_right _ member
  exact canonical_typedEachOccurrence loop checked tables annotations location sourceCursor typed replay ceiling bodyScopes stack closed
    ready sites targetBounds generated native projects continuation placeChild expressionChild bodyChild

#print axioms canonical_statementOccurrence_each

#print axioms canonical_typedEachOccurrence

end Goose.Lower.Validation.SourceReplacementWriterLedger
