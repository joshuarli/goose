import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

theorem OperandOccurrence.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {upper : Prov} {value : ValueId} {outerPath : List Nat}
    (source : DemandNodeAt root outerPath parent)
    (origin : OperandOccurrence env parent func upper value) :
    OperandOccurrence env root func upper value := by
  obtain ⟨path, node, start, roots, finish, inner, replay, bounded, refined⟩ := origin
  exact ⟨outerPath ++ path, node, start, roots, finish, sourcePath_append source inner,
    replay, bounded, refined⟩

theorem ReadOccurrence.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {upper : Prov} {value address : ValueId} {outerPath : List Nat}
    (source : DemandNodeAt root outerPath parent)
    (origin : ReadOccurrence env parent func upper value address) :
    ReadOccurrence env root func upper value address := by
  obtain ⟨localEnv, path, place, start, placeRoots, placeAfter, valueRoots, finish, accessEq, inner,
    placeReplay, valueReplay, addressBound, valueBound, addressRefined, valueRefined, physical⟩ := origin
  exact ⟨localEnv, outerPath ++ path, place, start, placeRoots, placeAfter, valueRoots, finish,
    accessEq, sourcePath_append source inner, placeReplay, valueReplay,
    addressBound, valueBound, addressRefined, valueRefined, physical⟩

theorem CallOccurrence.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {upper : Prov} {value callee : Nat} {args : List ValueId} {origin : Option OriginId} {outerPath : List Nat}
    (source : DemandNodeAt root outerPath parent)
    (occurrence : CallOccurrence env parent func upper value callee args origin) :
    CallOccurrence env root func upper value callee args origin := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, start, argumentRoots, argumentsAfter, resultRoots,
    finish, accessEq, originEq, inner, argumentsReplay, contents, callReplay, valueBound,
    valueRefined, arguments, physical, trace⟩ := occurrence
  exact ⟨localEnv, outerPath ++ path, syntaxArgs, sourceOrigin, start, argumentRoots, argumentsAfter,
    resultRoots, finish, accessEq, originEq, sourcePath_append source inner, argumentsReplay,
    contents, callReplay, valueBound, valueRefined, arguments, physical, trace⟩

theorem StoreOccurrence.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {upper : Prov} {address value : ValueId} {origin : Option OriginId} {outerPath : List Nat}
    (source : DemandNodeAt root outerPath parent)
    (occurrence : StoreOccurrence env parent func upper address value origin) :
    StoreOccurrence env root func upper address value origin := by
  rcases occurrence with assigned | rebound
  · obtain ⟨assigned⟩ := assigned
    exact Or.inl ⟨{ assigned with
      path := outerPath ++ assigned.path
      source := sourcePath_append source assigned.source }⟩
  · obtain ⟨rebound⟩ := rebound
    exact Or.inr ⟨{ rebound with
      path := outerPath ++ rebound.path
      source := sourcePath_append source rebound.source }⟩

theorem InstructionOccurrences.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {inst : Inst} {outerPath : List Nat}
    (source : DemandNodeAt root outerPath parent)
    (origins : InstructionOccurrences env parent func types upper inst) :
    InstructionOccurrences env root func types upper inst :=
  ⟨fun value member reference => (origins.1 value member reference).underRoot source,
    fun value address same reference => (origins.2.1 value address same reference).underRoot source,
    fun value callee args origin same => (origins.2.2.1 value callee args origin same).underRoot source,
    fun address value origin same reference => (origins.2.2.2.1 address value origin same reference).underRoot source,
    fun value member mutability payload row =>
      (origins.2.2.2.2 value member mutability payload row).underRoot source⟩

theorem OccurrenceLedger.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {initial final : LS} {outerPath : List Nat}
    (source : DemandNodeAt root outerPath parent)
    (ledger : OccurrenceLedger env parent func types upper initial final) :
    OccurrenceLedger env root func types upper initial final := by
  refine ⟨ledger.blocks, ?_, ?_⟩
  · intro index body row
    obtain ⟨next, nextRow, params, tail, appended, origins⟩ := ledger.old index body row
    exact ⟨next, nextRow, params, tail, appended, fun inst member => (origins inst member).underRoot source⟩
  · intro index body row lower inst member
    exact (ledger.fresh index body row lower inst member).underRoot source

theorem InstructionOccurrences.access_eq {env nextEnv : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {inst : Inst}
    (same : env.access = nextEnv.access)
    (origins : InstructionOccurrences env root func types upper inst) :
    InstructionOccurrences nextEnv root func types upper inst := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [OperandOccurrence, same] using origins.1
  · simpa only [ReadOccurrence, same] using origins.2.1
  · simpa only [CallOccurrence, same] using origins.2.2.1
  · intro address value origin equality reference
    exact (origins.2.2.2.1 address value origin equality reference).access_eq same
  · intro value member mutability payload row
    exact (origins.2.2.2.2 value member mutability payload row).access_eq same

theorem OccurrenceLedger.access_eq {env nextEnv : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {initial final : LS}
    (same : env.access = nextEnv.access)
    (ledger : OccurrenceLedger env root func types upper initial final) :
    OccurrenceLedger nextEnv root func types upper initial final := by
  have properties : InstructionOccurrences env root func types upper =
      InstructionOccurrences nextEnv root func types upper := by
    funext inst
    exact propext ⟨fun origins => origins.access_eq same, fun origins => origins.access_eq same.symm⟩
  change EmitsOnly (InstructionOccurrences nextEnv root func types upper) initial final
  rw [← properties]
  exact ledger

#print axioms OccurrenceLedger.underRoot
#print axioms OccurrenceLedger.access_eq

end Goose.Lower.Validation.ReplacementContentFlowSource
