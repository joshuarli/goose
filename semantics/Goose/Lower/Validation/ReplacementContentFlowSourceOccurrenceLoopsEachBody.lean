import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLoopsEachOps
import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsControl
import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachBody

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}
  {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}

set_option maxHeartbeats 1200000

theorem eachBodyOccurrence (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le ls func vt upper)
    (targetBounds : ReplacementTargetsBound siteTargets ls)
    (expected : List RootRef) (variableId : VarId) (indexVar : Option VarId) (byRef : Bool)
    (view counter : ValueId) (element : Ty) (sourceRoots : List RootRef) (origin : OriginId)
    (depth : Nat) (header exit : BlockId) (body : Core.Block)
    (sourceView : ViewOccurrenceSource env root sourceRoots)
    (live : ls.cur.isSome = true) (viewBound : view < ls.vals.size) (counterBound : counter < ls.vals.size)
    (refined : Goose.GIR.RootsRefine func (rootsAt upper.vals view) sourceRoots) (counterScalar : rootsAt upper.vals counter = [])
    (closed : ParameterRootsClosed func)
    (reference : byRef = true → ∃ localVar mu, le.vars[variableId]? = some localVar ∧ localVar.ty = .ref mu element)
    (reads : byRef = false → ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads)
    (flat : element.isRefLike = false)
    (binding : byRef = true → ∀ actual, Goose.GIR.RootsRefine func actual sourceRoots → ∀ root ∈ actual, root ∈ rootsAt slots variableId)
    (viewRow : ∃ mu, ls.vals[view]? = some (some (.view mu element)))
    (counterRow : ls.vals[counter]? = some (some (.data (.int .i64))))
    (generated : GeneratedBuilderState ls)
    (native : NativeRows vt ((do
      let address ← Goose.Lower.emitDef (.refElem view counter)
      let value ← eachElemValue variableId byRef address
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2)
    (projects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func ((do
      let address ← Goose.Lower.emitDef (.refElem view counter)
      let value ← eachElemValue variableId byRef address
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2)
    (continuation : NativeBuilderContinuation func ((do
      let address ← Goose.Lower.emitDef (.refElem view counter)
      let value ← eachElemValue variableId byRef address
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2)
    (bodyStep : ∀ provenance,
      let address := Goose.Lower.emitDef (.refElem view counter) le ls
      let value := eachElemValue variableId byRef address.1 le address.2
      let bindings := (variableId, value.1, origin) :: indexVar.toList.map (fun j => (j, counter, origin))
      ReplayBuilder module results vt func target le scopeCount slots value.2 provenance →
      OccurrenceSitesBuilder env siteRoot siteTargets le value.2 func vt provenance →
      ReplacementTargetsBound siteTargets value.2 →
      GeneratedBuilderState value.2 → NativeRows vt (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 →
      ls.blocks.size ≤ value.2.blocks.size →
      (∀ item ∈ bindings, item.2.1 < value.2.vals.size) →
      (∀ item ∈ bindings, ∀ root ∈ rootsAt provenance.vals item.2.1, root ∈ rootsAt slots item.1) →
      SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
        (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 →
      NativeBuilderContinuation func
        (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 next ∧
        (∀ old, old < provenance.vals.size → rootsAt next.vals old = rootsAt provenance.vals old) ∧
        ReturnBoundsPreserved expected value.2 provenance
          (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 next ∧
        OccurrenceLedger env root func vt next value.2
          (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 ∧
        OccurrenceSitesBuilder env siteRoot siteTargets le
          (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        ((do
          let address ← Goose.Lower.emitDef (.refElem view counter)
          let value ← eachElemValue variableId byRef address
          lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
            ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2 next ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ReturnBoundsPreserved expected ls upper
        ((do
          let address ← Goose.Lower.emitDef (.refElem view counter)
          let value ← eachElemValue variableId byRef address
          lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
            ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2 next ∧
      OccurrenceLedger env root func vt next ls
        ((do
          let address ← Goose.Lower.emitDef (.refElem view counter)
          let value ← eachElemValue variableId byRef address
          lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
            ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le
        ((do
          let address ← Goose.Lower.emitDef (.refElem view counter)
          let value ← eachElemValue variableId byRef address
          lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
            ((variableId, value, origin) :: indexVar.toList.map (fun j => (j, counter, origin))) false body) le ls).2 func vt next := by
  let address := Goose.Lower.emitDef (.refElem view counter) le ls
  let value := eachElemValue variableId byRef address.1 le address.2
  let bindings := (variableId, value.1, origin) :: indexVar.toList.map (fun j => (j, counter, origin))
  have bodyNative : NativeRows vt (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 := native
  have valueNative : NativeRows vt value.2 := bodyNative.of_prefix (types_lowerBlock _ _ _ _ le value.2 _ _ rfl)
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  obtain ⟨mu, typedView⟩ := viewRow
  have addressType : (Op.refElem view counter).resultTy (tyEnv le ls) = .ok (.data (.ref mu element)) := by
    simp [Op.resultTy, TyEnv.viewTy, TyEnv.intTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, typedView, counterRow,
      bind, Except.bind, pure, Except.pure]
  have recorded := emitDef_recorded (le := le) current addressType
  have addressRow : address.2.vals[address.1]? = some (some (.data (.ref mu element))) := recorded.2.2.1
  have addressCurrent : address.2.cur = some block := recorded.2.1.trans current
  have scalarType : byRef = false → valRefLike vt address.2.vals.size = false := by
    intro inactive
    subst byRef
    have loadNative : NativeRows vt (Goose.Lower.emitDef (.load address.1) le address.2).2 := valueNative
    have loadLive : (Goose.Lower.emitDef (.load address.1) le address.2).2.cur.isSome = true := by
      simp [emitDef_run _ _ addressCurrent, addressCurrent]
    have actualRow := loadNative.load addressRow rfl loadLive
    have fresh : (Goose.Lower.emitDef (.load address.1) le address.2).1 = address.2.vals.size := by rw [emitDef_run _ _ addressCurrent]
    change vt[(Goose.Lower.emitDef (.load address.1) le address.2).1]? = some (some (.data element)) at actualRow
    rw [fresh] at actualRow
    simp only [valRefLike, actualRow, VTy.refLike, flat]
  obtain ⟨addressProv, addressReady, addressValue, addressGrowth⟩ := ready.loopEachAddress view counter element sourceRoots viewBound counterBound refined
  have addressLive : address.2.cur.isSome = true := by simp [addressCurrent]
  obtain ⟨valueProv, valueReady, valueLive, valueBound, valueReference, valueScalar, valueGrowth⟩ :=
    addressReady.loopEachValue variableId address.1 byRef element sourceRoots addressLive
      ⟨(addressValue addressLive).bound, (addressValue addressLive).refined⟩ closed reference reads (fun inactive => scalarType inactive) flat
  have addressAdv := advB_emitDef (.refElem view counter) le ls address.1 address.2 rfl
  have valueAdv := advB_eachElemValue variableId byRef address.1 le address.2 value.1 value.2 rfl
  have valueGenerated := (generated.emitDef _ (rfl : Goose.Lower.emitDef (.refElem view counter) le ls = address)).eachElemValue
    variableId byRef address.1 (rfl : eachElemValue variableId byRef address.1 le address.2 = value)
  have counterOld : counter < upper.vals.size := by simpa only [ready.roots.valueSize] using counterBound
  have counterAddress : counter < addressProv.vals.size := by
    rw [addressReady.roots.valueSize]
    exact Nat.lt_of_lt_of_le counterBound addressAdv.vals
  have counterEmpty : rootsAt valueProv.vals counter = [] :=
    (valueGrowth counter counterAddress).trans ((addressGrowth counter counterOld).trans counterScalar)
  have producedGrowth : ∀ old, old < upper.vals.size → rootsAt valueProv.vals old = rootsAt upper.vals old := by
    intro old bound
    have middleBound : old < addressProv.vals.size := by
      rw [addressReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) addressAdv.vals
    rw [valueGrowth old middleBound, addressGrowth old bound]
  have addressGhostGrowth := accessRootsGrowth ready addressReady addressAdv.vals
  have valueGhostGrowth := accessRootsGrowth addressReady valueReady valueAdv.vals
  have inputNative := valueNative.of_prefix ((types_emitDef (.refElem view counter) le ls _ _ rfl).trans
    (types_eachElemValue variableId byRef address.1 le address.2 _ _ rfl))
  have scalarCounter : valRefLike vt counter = false := by
    simp only [valRefLike, inputNative _ _ counterRow, VTy.refLike, Ty.isRefLike]
  have addressContinuation : NativeBuilderContinuation func address.2 := continuation.of_advance
    (valueAdv.trans (advB_lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2 _ _ rfl))
  have consumedAddress : ConsumedReferenceOccurrence env root func vt valueProv address.1 :=
    addressContinuation.consumedBacking rfl live generated (.element view counter)
      (inputNative view (.view mu element) typedView) (.view mu element)
  have addressLedger : OccurrenceLedger env root func vt addressProv ls address.2 := by
    apply accessEmitDefinition rfl
    intro active
    refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
    · intro operand member reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · apply sourceView.operand (Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using viewBound) addressGhostGrowth)
        rw [addressGrowth _ (by simpa only [ready.roots.valueSize] using viewBound)]
        exact refined
      · rw [scalarCounter] at reference
        cases reference
    · intro value address same; cases same
    · intro value callee args origin same; cases same
    · intro operand member mutability payload row
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [inputNative _ (.view mu element) typedView] at row
        cases row
      · rw [inputNative _ (.data (.int .i64)) counterRow] at row
        cases row
  have addressSites := sites.emitDef_replay ready addressReady rfl addressGrowth
  have valueLedger : OccurrenceLedger env root func vt valueProv address.2 value.2 := by
    cases byRef with
    | true =>
      obtain ⟨localVar, mutability, row, type⟩ := reference rfl
      apply occurrenceLedger_borrowTo (mutability := mutability) (value := address.1) (result := value.1) (le := le)
      simp only [value, eachElemValue, ite_true, bind_run, read_apply, row, type]
    | false =>
      apply occurrence_emitDef_live rfl
      intro active
      refine ⟨?_, ?_, ?_, InstructionOccurrences.no_store (by intros; intro same; cases same), ?_⟩
      · intro operand member isReference
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst operand
        have bound : address.1 < addressProv.vals.size := by simpa only [addressReady.roots.valueSize] using (addressValue addressLive).bound
        apply sourceView.operand (Nat.lt_of_lt_of_le bound valueGhostGrowth)
        rw [valueGrowth address.1 bound]
        exact (addressValue addressLive).refined
      · intro found pointer same isReference
        have index := (Inst.def.inj same).1
        subst found
        rw [scalarType rfl] at isReference
        cases isReference
      · intro found callee args origin same
        cases (Inst.def.inj same).2
      · intro operand member mutability payload row
        have same : operand = address.1 := by simpa [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses] using member
        subst operand
        exact consumedAddress
  have valueSites : OccurrenceSitesBuilder env siteRoot siteTargets le value.2 func vt valueProv := by
    cases byRef with
    | true =>
      obtain ⟨localVar, mutability, row, type⟩ := reference rfl
      apply occurrenceSites_borrowTo (mutability := mutability) (value := address.1) (result := value.1) addressSites ?_ valueGhostGrowth valueGrowth
      simp only [value, eachElemValue, ite_true, bind_run, read_apply, row, type]
      rfl
    | false => exact addressSites.emitDef rfl valueGhostGrowth valueGrowth
  have emittedLedger : OccurrenceLedger env root func vt valueProv ls value.2 :=
    (addressLedger.retained valueGhostGrowth valueGrowth).trans valueLedger
  have bodyProjects : SourceCanonicalRootFloors.RecipeMetadataProjects env siteRoot func
      (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2).2 := projects
  obtain ⟨next, nextReady, bodyGrowth, bodyTransfer, bodyLedger, bodySites⟩ :=
    bodyStep valueProv valueReady valueSites (targetBounds.mono (addressAdv.ext.trans valueAdv.ext)) valueGenerated bodyNative
    (Nat.le_trans addressAdv.ext.1 valueAdv.ext.1)
    (by
      intro item member
      simp only [List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨j, _, rfl⟩
      · exact valueBound
      · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le counterBound addressAdv.vals) valueAdv.vals)
    (by
      intro item member root rootMember
      simp only [List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨j, _, rfl⟩
      · cases byRef with
        | true => exact binding rfl _ (valueReference rfl) root rootMember
        | false =>
          have empty := valueScalar rfl
          change rootsAt valueProv.vals value.1 = [] at empty
          rw [empty] at rootMember
          exact False.elim (List.not_mem_nil rootMember)
      · rw [counterEmpty] at rootMember
        exact False.elim (List.not_mem_nil rootMember)) bodyProjects continuation
  have emittedReturns : ReturnMembershipFrame ls value.2 := by
    apply ReturnFrameRun.of_absence (fun _ => ReturnFrames.ReturnAbsentRun.bind
      (ReturnFrames.returnAbsent_emitDef (.refElem view counter)) (fun result => ReturnFrames.returnAbsent_eachElemValue variableId byRef result))
      le ls value.1 value.2 rfl
  have emittedTransfer : ReturnBoundsPreserved expected ls upper value.2 valueProv :=
    .frame ready.symbols ready.roots.valueSize producedGrowth emittedReturns
  refine ⟨next, nextReady, ?_, emittedTransfer.trans bodyTransfer, ?_, bodySites⟩
  · intro old bound
    have valueBound : old < valueProv.vals.size := by
      rw [valueReady.roots.valueSize]
      exact Nat.lt_of_lt_of_le (by simpa only [ready.roots.valueSize] using bound) (Nat.le_trans addressAdv.vals valueAdv.vals)
    rw [bodyGrowth old valueBound, producedGrowth old bound]
  · have finalGrowth := accessRootsGrowth valueReady nextReady (advB_lowerBlock
      (some ⟨depth, exit, .next header .i64 counter⟩) bindings false body le value.2 _ _ rfl).vals
    exact (emittedLedger.retained finalGrowth bodyGrowth).trans bodyLedger

#print axioms eachBodyOccurrence

end Goose.Lower.Validation.ReplacementContentFlowSource
