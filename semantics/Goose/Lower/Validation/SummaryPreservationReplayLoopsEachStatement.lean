import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachPrelude
import Goose.Lower.Validation.SourceReadable
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem each_regrow_state (owner : Option ValueId) (le : LEnv) (state : LS) :
    (regrowOf owner le state).2 = state := by
  cases owner with
  | none => rfl
  | some value =>
    simp only [regrowOf, growOwner, bind_run, valTy_run]
    cases (valTy value le state).1 with
    | view _ _ => rfl
    | data type => cases type <;> rfl

private theorem each_flat_nonref {element : Ty} (flat : element.flat = true) :
    element.isRefLike = false ∧ element.isSlice = false := by
  cases element <;> simp_all [Ty.flat, Ty.isRefLike, Ty.isSlice]

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

set_option maxHeartbeats 1400000

theorem each_statement {tenv output : TEnv} {env : PEnv} {variableId : VarId} {indexVar : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId}
    {scope start finish : Nat} {before after : RState}
    (loop : Option LoopCtx)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (typing : Core.tyStmt tenv scope (.forEach variableId indexVar view byRef body origin) start = .ok (output, finish))
    (source : rpStmt env (.forEach variableId indexVar view byRef body origin) before = .ok ((), after))
    (checked : SourceReadableEnvironment tenv)
    (annotations : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variables : le.vars = tenv.vars) (sourceVariables : tenv.vars = env.impl.vars)
    (function : func = lowerContextAt env.mod env.ctx env.impl)
    (slotRoots : slots = typedContextSlotUpper env.mod env.ctx env.impl)
    (closed : ParameterRootsClosed func) (wholeEffect : EffectRefinement func after.eff target)
    (sourceStep : ∀ element writable typeStart typeFinish sourceBefore sourceAfter sourceRoots state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      Core.tyView tenv view typeStart = .ok ((element, writable), typeFinish) →
      rpView env view sourceBefore = .ok (sourceRoots, sourceAfter) →
      EffectRefinement func sourceAfter.eff target →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (lowerEachSource view le state).2 next ∧
        ((lowerEachSource view le state).2.cur.isSome = true →
          ReplayEachSource func next (lowerEachSource view le state).2 (lowerEachSource view le state).1 sourceRoots element) ∧
        ∀ i, i < provenance.vals.size → rootsAt next.vals i = rootsAt provenance.vals i)
    (copyScalar : byRef = false →
      let source := lowerEachSource view le ls
      let regrow := (regrowOf source.1.1 le source.2).1
      source.2.cur.isSome = true →
        valRefLike vt ((eachPreludeBodyEntry regrow source.1.1 source.1.2 le source.2).vals.size + 1) = false)
    (bodyStep : ∀ depth header exit counter value typeStart bodyType sourceBefore sourceAfter bodyRoots bodyRange state provenance,
      ReplayBuilder module results vt func target le scopeCount slots state provenance →
      header < state.blocks.size → exit < state.blocks.size →
      (∀ item ∈ (variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin)), item.2.1 < state.vals.size) →
      (∀ item ∈ (variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin)),
        ∀ root ∈ rootsAt provenance.vals item.2.1, root ∈ rootsAt slots item.1) →
      Core.tyBlock { tenv with loops := tenv.loops + 1, visible := variableId :: indexVar.toList ++ tenv.visible }
        [] body typeStart = .ok (bodyType, finish) →
      rpBlockValue env [] body sourceBefore = .ok ((bodyRoots, bodyRange), sourceAfter) →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body le state).2 next ∧
        ∀ i, i < provenance.vals.size → rootsAt next.vals i = rootsAt provenance.vals i) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
      (lowerStmt loop (.forEach variableId indexVar view byRef body origin) le ls).2 next ∧
      ∀ i, i < upper.vals.size → rootsAt next.vals i = rootsAt upper.vals i := by
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declaration, indexDeclaration, viewTyping, variableTyping, bodyTyping, _⟩ := tyStmt_forEach_children typing
  obtain ⟨sourceStart, sourceRoots, viewState, boundState, bodyRoots, bodyRange, bodyState,
    viewReplay, bindingReplay, bodyReplay, afterEq⟩ := rpStmt_each_children source
  have viewEffect := each_view_effect_bound bindingReplay bodyReplay afterEq wholeEffect
  let sampledSource := lowerEachSource view le ls
  obtain ⟨sourceProv, sourceReady, sourceValue, sourceGrowth⟩ := sourceStep element writable viewStart viewFinish
    sourceStart viewState sourceRoots ls upper ready viewTyping viewReplay viewEffect
  have sourceAdv := advB_lowerEachSource view le ls sampledSource.1 sampledSource.2 rfl
  let regrow := (regrowOf sampledSource.1.1 le sampledSource.2).1
  have regrowRun : regrowOf sampledSource.1.1 le sampledSource.2 = (regrow, sampledSource.2) :=
    Prod.ext rfl (each_regrow_state _ _ _)
  have whole : lowerStmt loop (.forEach variableId indexVar view byRef body origin) le ls =
      ((do
        let sampled ← eachSampled regrow sampledSource.1.2
        let startAt ← Goose.Lower.emitDef (.constInt .i64 0)
        whenLive () fun _ => do
          let (header, parameters) ← newBlock [.data (.int .i64)]
          let counter := parameters.headD 0
          emitTerm (.br header [startAt])
          Goose.Lower.setCur (some header)
          lowerEach regrow sampledSource.1.1 sampled header counter (fun depth exit => do
            let address ← Goose.Lower.emitDef (.refElem sampledSource.1.2 counter)
            let value ← eachElemValue variableId byRef address
            lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
              ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body)) le sampledSource.2) := by
    simp only [lowerStmt, bind_run]
    change _ = _
    rw [regrowRun]
    cases indexVar <;> rfl
  cases current : sampledSource.2.cur with
  | none =>
    have stopped : (lowerStmt loop (.forEach variableId indexVar view byRef body origin) le ls).2 = sampledSource.2 := by
      rw [whole]
      cases regrow <;> simp [eachSampled, bind_run, pure_run, emitDef_none _ _ current, whenLive_none _ _ _ current]
    exact ⟨sourceProv, by simpa only [stopped] using sourceReady, sourceGrowth⟩
  | some block =>
    have live : sampledSource.2.cur.isSome = true := by simp [current]
    have row : tenv.vars[variableId]? = some localVar := (declare_ok _ _ _ _ _ declaration).2.1
    have sourceRow : env.impl.vars[variableId]? = some localVar := by simpa only [sourceVariables] using row
    have actualRow : le.vars[variableId]? = some localVar := by simpa only [variables] using row
    have flat := source_view_element_flat view checked viewTyping
    have nonref := (each_flat_nonref flat).1
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
        ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads := by
      intro required
      apply each_source_read_bound viewReplay bindingReplay bodyReplay afterEq wholeEffect
      exact required.elim Or.inl (fun active => Or.inr (ownerView active))
    have binding : byRef = true → ∀ actual, RootsRefine func actual sourceRoots → ∀ root ∈ actual, root ∈ rootsAt slots variableId := by
      intro active actual refined
      obtain ⟨_, mu, actualRow, localType⟩ := reference active
      have ordinary : localVar.ty.isRefSlice = false := by
        have same : _ = localVar := Option.some.inj (actualRow.symm.trans (by simpa only [variables] using row))
        subst same
        rw [localType]
        cases element <;> simp_all [Ty.flat, Ty.isRefSlice]
      rw [slotRoots]
      apply each_source_binding_bound annotations sourceRow ordinary
        (by simpa only [active, ite_true] using bindingReplay)
      simpa only [function] using refined
    obtain ⟨next, nextReady, growth⟩ := sourceReady.eachPrelude regrow sampledSource.1.1 sampledSource.1.2 element sourceRoots
      (fun depth header exit counter => do
        let address ← Goose.Lower.emitDef (.refElem sampledSource.1.2 counter)
        let value ← eachElemValue variableId byRef address
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body)
      live (sourceValue live) closed owner (fun active => reads (Or.inr active))
      (fun depth header exit counter => AdvB.bind (advB_emitDef _) fun address =>
        AdvB.bind (advB_eachElemValue _ _ _) fun value => advB_lowerBlock _ _ _ _)
      (by
        intro depth header exit counter state provenance stateReady stateEq stateLive headerBound exitBound counterBound counterEmpty viewBound viewRefined
        apply stateReady.loopEachBody variableId indexVar byRef sampledSource.1.2 counter element sourceRoots origin depth header exit body
          stateLive viewBound counterBound viewRefined counterEmpty closed reference (fun inactive => reads (Or.inl inactive))
          (by
            intro inactive
            obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp stateLive
            simp only [emitDef_run _ _ current, Array.size_push]
            rw [stateEq]
            exact copyScalar inactive live) nonref binding
        intro value state provenance stateReady blocks values rootBounds
        exact bodyStep depth header exit counter value viewFinish bodyType boundState bodyState bodyRoots bodyRange
          state provenance stateReady
          (Nat.lt_of_lt_of_le headerBound blocks) (Nat.lt_of_lt_of_le exitBound blocks)
          values rootBounds bodyTyping bodyReplay)
    refine ⟨next, by simpa only [whole] using nextReady, ?_⟩
    intro i bound
    have sourceBound : i < sourceProv.vals.size := by
      rw [sourceReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) sourceAdv.vals
    rw [growth i sourceBound, sourceGrowth i bound]

#print axioms each_statement

end ReplayBuilder
end Goose.Lower.Validation.SummaryPreservation
