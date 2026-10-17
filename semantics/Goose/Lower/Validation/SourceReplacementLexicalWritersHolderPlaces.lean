import Goose.Lower.Validation.SourceReplacementLexicalWritersPhysics
import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.SourceReadablePlaceShape
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyArgumentRoots
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsCheckpoints

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem typed_variable_place_visible {typing : TEnv} {slot : VarId} {info : PlaceInfo}
    {start finish : Nat}
    (source : Core.tyPlace typing (.var slot) start = .ok (info, finish)) : slot ∈ typing.visible := by
  simp only [Core.tyPlace] at source
  obtain ⟨localVar, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact ((varOf_ok _ _ _ _).mp checked).1

theorem holder_place_local_of_native_local (facts : SourceReadyFunction)
    {typing : TEnv} (tables : SourceRootTables typing facts.source)
    {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace typing place start = .ok (info, finish))
    (readable : info.ty.readable = true) (reference : info.ty.isRefLike = true)
    {returnTypes : List Ty} {before after : LS} {address : ValueId}
    (bounded : LiveBound before)
    (run : lowerPlace place (lowerEnv typing.mod typing.vars returnTypes) before = (address, after))
    (live : after.cur.isSome = true) (continuation : NativeBuilderContinuation facts.func after)
    (nativeReference : valRefLike facts.types address = true)
    {physicalEnv : PEnv} {physicalPlace : Place}
    (physical : ReadAddressPhysical physicalEnv physicalPlace (rootsAt facts.upper.vals address))
    {tracked : VarId} (trackedMember : RootRef.local tracked ∈ rootsAt facts.provenance.vals address) :
    place = .var tracked ∧ tracked ∈ typing.visible := by
  rcases source_readable_place_shape (facts.readable tables) source readable reference with direct | formal
  · obtain ⟨slot, localVar, rfl, row, type⟩ := direct
    have same := physical_local_slotAddr_identity facts.native bounded run live continuation physical
      (facts.below address) trackedMember
    subst slot
    exact ⟨rfl, typed_variable_place_visible source⟩
  · obtain ⟨slot, localVar, mu, sliceMu, element, rfl, row, type, target, flat⟩ := formal
    have localReference : localVar.ty.isRefSlice = true := by rw [type]; exact flat
    have seed := facts.sourceSlotSeeds tables slot localVar row localReference
    have floor := readVar_parameter_native_floor facts.native bounded
      (show lowerExpr (.read (.var slot)) (lowerEnv typing.mod typing.vars returnTypes) before =
        (address, after) from run) live continuation nativeReference seed
    exact False.elim (physical_local_parameter_impossible physical (facts.below address) trackedMember floor)

theorem byRef_holder_place_local_of_native_local (facts : SourceReadyFunction)
    {typing : TEnv} (tables : SourceRootTables typing facts.source)
    {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace typing place start = .ok (info, finish))
    (readable : info.ty.readable = true) (reference : info.ty.isRefLike = true)
    {returnTypes : List Ty} {before after : LS} {argument : ValueId} {mode : Mutability}
    (bounded : LiveBound before)
    (run : lowerArg (.byRef mode place) (lowerEnv typing.mod typing.vars returnTypes) before =
      (argument, after))
    (live : after.cur.isSome = true) (extension : after.Ext facts.completed)
    (nativeReference : valRefLike facts.types argument = true)
    {physicalEnv : PEnv} {physicalPlace : Place}
    (physical : ReadAddressPhysical physicalEnv physicalPlace (rootsAt facts.upper.vals argument))
    {tracked : VarId} (trackedMember : RootRef.local tracked ∈ rootsAt facts.provenance.vals argument) :
    place = .var tracked ∧ tracked ∈ typing.visible := by
  have initialLive := (dead_lowerArg (.byRef mode place)).live_before run live
  rcases source_readable_place_shape (facts.readable tables) source readable reference with direct | formal
  · obtain ⟨slot, localVar, rfl, row, type⟩ := direct
    have floor := facts.frame.native_variable_argument_root facts.native.valuesSize
      facts.native.definitions facts.native.quiet run bounded initialLive extension
    have same : slot = tracked := by
      simpa only [List.mem_singleton,RootRef.local.injEq] using
        (physical.local_upper (facts.below argument) trackedMember) floor
    subst slot
    exact ⟨rfl,typed_variable_place_visible source⟩
  · obtain ⟨slot, localVar, mu, sliceMu, element, rfl, row, type, target, flat⟩ := formal
    obtain ⟨holder, middle, placeRun, borrowRun⟩ := bind_eq.mp run
    have middleLive := (dead_borrowTo mode holder).live_before borrowRun live
    have middleBound : LiveBound middle := by
      have valid := liveBound_of_advB (advB_lowerPlace (.deref (.read (.var slot))))
        (lowerEnv typing.mod typing.vars returnTypes) before bounded
      rw [placeRun] at valid
      exact valid
    have readRun : lowerExpr (.read (.var slot)) (lowerEnv typing.mod typing.vars returnTypes) before =
        (holder,middle) := placeRun
    have holderReference := borrowTo_input_reference facts.native middleBound borrowRun live
      ((NativeBuilderContinuation.of_blocks facts.frame.blocks).of_extension extension) nativeReference
    have localReference : localVar.ty.isRefSlice = true := by rw [type]; exact flat
    have seed := facts.sourceSlotSeeds tables slot localVar row localReference
    have middleContinuation : NativeBuilderContinuation facts.func middle :=
      (NativeBuilderContinuation.of_blocks facts.frame.blocks).of_extension
        ((advB_borrowTo mode holder _ _ _ _ borrowRun).ext.trans extension)
    have floor := readVar_parameter_native_floor facts.native bounded readRun middleLive
      middleContinuation holderReference seed
    have argumentFloor := facts.frame.native_borrowTo_root facts.native.valuesSize
      facts.native.definitions facts.native.quiet borrowRun middleBound middleLive extension floor
    exact False.elim (physical_local_parameter_impossible physical (facts.below argument)
      trackedMember argumentFloor)

theorem selected_holder_argument_visible (facts : SourceReadyFunction)
    {typing : TEnv} (tables : SourceRootTables typing facts.source)
    {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace typing place start = .ok (info, finish))
    (readable : info.ty.readable = true) (reference : info.ty.isRefLike = true)
    {returnTypes : List Ty} {before after : LS} {arguments : List Arg} {values : List ValueId}
    {index argument : Nat} {mode : Mutability}
    (bounded : LiveBound before)
    (run : lowerArgs arguments (lowerEnv typing.mod typing.vars returnTypes) before = (values,after))
    (sourceRow : arguments[index]? = some (.byRef mode place))
    (nativeRow : values[index]? = some argument)
    (live : after.cur.isSome = true) (extension : after.Ext facts.completed)
    (nativeReference : valRefLike facts.types argument = true)
    {physicalEnv : PEnv} {physicalPlace : Place}
    (physical : ReadAddressPhysical physicalEnv physicalPlace (rootsAt facts.upper.vals argument))
    {tracked : VarId} (trackedMember : RootRef.local tracked ∈ rootsAt facts.provenance.vals argument) :
    place = .var tracked ∧ tracked ∈ typing.visible := by
  obtain ⟨earlier,later,argumentAfter,split,length,selected,suffix,advance⟩ :=
    lowerArgs_argument_run run sourceRow nativeRow
  have argumentBound := liveBound_of_advB (advB_lowerArgs earlier)
    (lowerEnv typing.mod typing.vars returnTypes) before bounded
  have suffixRun : lowerArgs later (lowerEnv typing.mod typing.vars returnTypes) argumentAfter =
      ((lowerArgs later (lowerEnv typing.mod typing.vars returnTypes) argumentAfter).1,after) :=
    Prod.ext rfl suffix
  have argumentLive := (dead_lowerArgs later).live_before suffixRun live
  exact byRef_holder_place_local_of_native_local facts tables source readable reference
    argumentBound selected argumentLive (advance.ext.trans extension) nativeReference physical trackedMember

#print axioms selected_holder_argument_visible
#print axioms byRef_holder_place_local_of_native_local
#print axioms typed_variable_place_visible
#print axioms holder_place_local_of_native_local

end Goose.Lower.Validation.SourceReplacementLexicalWriters
