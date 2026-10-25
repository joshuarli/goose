import Goose.Lower.Validation.SourceReplacementLexicalWritersEmissionSpans
import Goose.Lower.Validation.SourceCanonicalRootFloorsNativeDefinitions
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadBounds
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem emitted_definition_liveBound {env : LEnv} {before after : LS} {op : Op}
    {value : ValueId} {func : Func} (bounded : LiveBound before)
    (run : emitDef op env before = (value, after)) (live : after.cur.isSome = true)
    (continuation : NativeBuilderContinuation func after) :
    ∃ block ∈ func.blocks.toList, Inst.def value op ∈ block.insts := by
  have beforeLive := (dead_emitDef op).live_before run live
  cases current : before.cur with
  | none => simp [current] at beforeLive
  | some block =>
    obtain ⟨completed, extension, blocks⟩ := continuation
    exact emitted_definition_retained current (bounded block current) run extension blocks

theorem emitted_slotAddr_native_floor {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    (facts : FunctionCanonicalFacts module func types provenance results)
    {env : LEnv} {before after : LS} {slot : SlotId} {address : ValueId}
    (bounded : LiveBound before)
    (run : emitDef (.slotAddr slot) env before = (address, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after) :
    RootRef.local slot ∈ rootsAt provenance.vals address := by
  obtain ⟨block, member, definition⟩ := emitted_definition_liveBound bounded run live continuation
  apply provStep_def_roots (by rw [facts.valuesSize]; exact facts.definitions _ member _ _ definition)
    (facts.quiet _ member _ definition)
  simp [rootsOfDef]

theorem readVar_native_definitions_liveBound {env : LEnv} {before after : LS}
    {slot : VarId} {value : ValueId} {func : Func} (bounded : LiveBound before)
    (run : lowerExpr (.read (.var slot)) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after) :
    ∃ address addressBlock loadBlock,
      addressBlock ∈ func.blocks.toList ∧ loadBlock ∈ func.blocks.toList ∧
      Inst.def address (.slotAddr slot) ∈ addressBlock.insts ∧
      Inst.def value (.load address) ∈ loadBlock.insts := by
  simp only [lowerExpr] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨loaded, emitted, loadRun, run⟩ := bind_eq.mp run
  obtain ⟨recordResult, recorded, recordRun, run⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := pure_eq.mp run
  have emittedLive := (dead_recordReadValueRootRecipe loaded (.var slot)).live_before recordRun live
  have middleLive := (dead_emitDef (.load address)).live_before loadRun emittedLive
  have emittedContinuation := continuation.of_advance
    (advB_recordReadValueRootRecipe loaded (.var slot) _ _ _ _ recordRun)
  have middleContinuation := emittedContinuation.of_advance (adv_emitDef loadRun)
  obtain ⟨addressBlock, addressMember, addressDef⟩ :=
    emitted_definition_liveBound bounded placeRun middleLive middleContinuation
  have middleBound : LiveBound middle := by
    have valid := liveBound_of_advB (advB_emitDef (.slotAddr slot)) env before bounded
    change LiveBound (lowerPlace (.var slot) env before).2 at valid
    rw [placeRun] at valid
    exact valid
  obtain ⟨loadBlock, loadMember, loadDef⟩ :=
    emitted_definition_liveBound middleBound loadRun emittedLive emittedContinuation
  exact ⟨address, addressBlock, loadBlock, addressMember, loadMember, addressDef, loadDef⟩

theorem readVar_parameter_native_floor {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    (facts : FunctionCanonicalFacts module func types provenance results)
    {env : LEnv} {before after : LS} {slot : VarId} {value parameter : Nat}
    (bounded : LiveBound before)
    (run : lowerExpr (.read (.var slot)) env before = (value, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (reference : valRefLike types value = true)
    (seed : RootRef.param parameter ∈ rootsAt provenance.slots slot) :
    RootRef.param parameter ∈ rootsAt provenance.vals value := by
  obtain ⟨address, addressBlock, loadBlock, addressMember, loadMember, addressDef, loadDef⟩ :=
    readVar_native_definitions_liveBound bounded run live continuation
  have addressFloor : RootRef.local slot ∈ rootsAt provenance.vals address := by
    apply provStep_def_roots (by rw [facts.valuesSize]; exact facts.definitions _ addressMember _ _ addressDef)
      (facts.quiet _ addressMember _ addressDef)
    simp [rootsOfDef]
  exact load_local_parameter_seed
    (by rw [facts.valuesSize]; exact facts.definitions _ loadMember _ _ loadDef)
    (facts.quiet _ loadMember _ loadDef) reference addressFloor seed

private theorem emitted_reference_input {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    (facts : FunctionCanonicalFacts module func types provenance results)
    {env : LEnv} {before after : LS} {input value : ValueId} {op : Op}
    (bounded : LiveBound before) (run : emitDef op env before = (value,after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (operation : op = .refFreeze input ∨ op = .ownerBorrow input) : valRefLike types input = true := by
  obtain ⟨block,member,definition⟩ := emitted_definition_liveBound bounded run live continuation
  have typed := facts.typing _ member _ definition
  cases typed with
  | definition _ _ type checked canonical =>
    rcases operation with rfl | rfl
    all_goals
      cases found : ({ module.tyEnv func with vals := types } : TyEnv).refTy input with
      | error message => simp [Op.resultTy,found,bind,Except.bind] at checked
      | ok pair =>
        obtain ⟨mu,payload⟩ := pair
        have row := TyEnv.refTy_known found
        simp [valRefLike,row,VTy.refLike,Ty.isRefLike]

theorem borrowTo_input_reference {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    (facts : FunctionCanonicalFacts module func types provenance results)
    {env : LEnv} {before after : LS} {input value : ValueId} {mode : Mutability}
    (bounded : LiveBound before)
    (run : borrowTo mode input env before = (value,after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (reference : valRefLike types value = true) : valRefLike types input = true := by
  simp only [borrowTo] at run
  obtain ⟨queriedEnv,queriedState,queried,run⟩ := bind_eq.mp run
  simp only [read_apply,Prod.mk.injEq] at queried
  obtain ⟨rfl,rfl⟩ := queried
  obtain ⟨type,middle,typeRun,run⟩ := bind_eq.mp run
  have same := valTy_run input env before
  rw [typeRun] at same
  dsimp only at same
  subst middle
  let owner := match type with
    | .data (.ref .mutable (.grow _)) | .data (.ref .mutable (.growshrink _)) |
      .data (.ref .mutable (.limited _ _)) => true
    | _ => false
  change (if mode == .mutable && env.mod.profile == .shrink && owner then
    emitDef (.ownerBorrow input) else freezeTo mode input) env before = (value,after) at run
  split at run
  · exact emitted_reference_input facts bounded run live continuation (Or.inr rfl)
  · simp only [freezeTo] at run
    obtain ⟨actual,classified,classify,run⟩ := bind_eq.mp run
    have unchanged := valTy_run input env before
    rw [classify] at unchanged
    dsimp only at unchanged
    subst classified
    split at run
    · exact emitted_reference_input facts bounded run live continuation (Or.inl rfl)
    · obtain ⟨rfl,_⟩ := pure_eq.mp run
      exact reference

theorem physical_local_slotAddr_identity {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {provenance : Prov} {results : Array (List RootRef)}
    (facts : FunctionCanonicalFacts module func types provenance results)
    {env : LEnv} {before after : LS} {slot tracked : SlotId} {address : ValueId}
    {sourceEnv : PEnv} {sourcePlace : Place} {physicalRoots : List RootRef}
    (bounded : LiveBound before)
    (run : emitDef (.slotAddr slot) env before = (address, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation func after)
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (below : rootsAt provenance.vals address ⊆ physicalRoots)
    (trackedMember : RootRef.local tracked ∈ rootsAt provenance.vals address) : slot = tracked := by
  have floor := emitted_slotAddr_native_floor facts bounded run live continuation
  have upper := physical.local_upper below trackedMember
  simpa only [List.mem_singleton,RootRef.local.injEq] using upper floor

theorem physical_local_parameter_impossible {sourceEnv : PEnv} {sourcePlace : Place}
    {physicalRoots actual : List RootRef} {tracked parameter : Nat}
    (physical : ReadAddressPhysical sourceEnv sourcePlace physicalRoots)
    (below : actual ⊆ physicalRoots) (trackedMember : RootRef.local tracked ∈ actual)
    (parameterMember : RootRef.param parameter ∈ actual) : False := by
  have upper := physical.local_upper below trackedMember
  have impossible := List.mem_singleton.mp (upper parameterMember)
  cases impossible

#print axioms borrowTo_input_reference
#print axioms emitted_definition_liveBound
#print axioms readVar_native_definitions_liveBound
#print axioms readVar_parameter_native_floor
#print axioms emitted_slotAddr_native_floor
#print axioms physical_local_slotAddr_identity
#print axioms physical_local_parameter_impossible

end Goose.Lower.Validation.SourceReplacementLexicalWriters
