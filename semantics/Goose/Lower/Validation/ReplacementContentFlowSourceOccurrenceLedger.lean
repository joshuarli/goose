import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallTrace
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStores
import Goose.Lower.Validation.ReplacementContentFlowSourceConsumedReferences
import Goose.GIR.RootBounds
import Goose.GIR.ReplacementContentFlow
import Goose.Lower.Validation.ReplacementEmission

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

inductive SourceNodeRoots (access : AccessEnv) : DemandNode → RState → List RootRef → RState → Prop
  | expression {env expression before roots after} : env.access = access →
      rpExpr env expression before = .ok (roots, after) → SourceNodeRoots access (.expression expression) before roots after
  | place {env place before roots after} : env.access = access →
      rpPlace env place before = .ok (roots, after) → SourceNodeRoots access (.place place) before roots after
  | view {env view before roots after} : env.access = access →
      rpView env view before = .ok (roots, after) → SourceNodeRoots access (.view view) before roots after
  | rebindTarget {env varId expression origin before roots after} : env.access = access →
      rpPlace env (.var varId) before = .ok (roots, after) →
      SourceNodeRoots access (.statement (.rebind varId expression origin)) before roots after

def OperandOccurrence (env : PEnv) (root : DemandNode) (func : Func) (upper : Prov)
    (value : ValueId) : Prop :=
  ∃ path node before sourceRoots after,
    DemandNodeAt root path node ∧ SourceNodeRoots env.access node before sourceRoots after ∧
    value < upper.vals.size ∧ GIR.RootsRefine func (rootsAt upper.vals value) sourceRoots

inductive ReadAddressPhysical (env : PEnv) (place : Place) (roots : List RootRef) : Prop
  | local (variableId : VarId) (source : place = .var variableId)
      (exactRoots : roots = [.local variableId]) : ReadAddressPhysical env place roots
  | contents (variableId : VarId) (source : place = .deref (.read (.var variableId)))
      (reference : env.isRefSliceVar variableId = true)
      (exactRoots : roots = [.param variableId]) : ReadAddressPhysical env place roots

def ReadOccurrence (env : PEnv) (root : DemandNode) (func : Func) (upper : Prov)
    (value address : ValueId) : Prop :=
  ∃ localEnv path place before placeRoots placeAfter valueRoots after,
    localEnv.access = env.access ∧ DemandNodeAt root path (.expression (.read place)) ∧
    rpPlace localEnv place before = .ok (placeRoots, placeAfter) ∧
    rpExpr localEnv (.read place) before = .ok (valueRoots, after) ∧
    address < upper.vals.size ∧ value < upper.vals.size ∧
    GIR.RootsRefine func (rootsAt upper.vals address) placeRoots ∧
    GIR.RootsRefine func (rootsAt upper.vals value) valueRoots ∧
    ReadAddressPhysical localEnv place (rootsAt upper.vals address)

def CallArgumentPhysical (env : PEnv) (syntaxArg : Arg) (upper : Prov) (value : ValueId) : Prop :=
  ∀ (mutability : Mutability) (place : Place), syntaxArg = .byRef mutability place →
    (∃ varId, place = .var varId ∨
      (place = .deref (.read (.var varId)) ∧ env.isRefSliceVar varId = true ∧
        (env.cont varId).isSome = true)) →
    ReadAddressPhysical env place (rootsAt upper.vals value)

def CallArgumentsPhysical (env : PEnv) (upper : Prov) (syntaxArgs : List Arg) (args : List ValueId) : Prop :=
  ∀ (index : Nat) (argument : ValueId) (syntaxArg : Arg),
    args[index]? = some argument → syntaxArgs[index]? = some syntaxArg →
    CallArgumentPhysical env syntaxArg upper argument

theorem CallArgumentPhysical.retained {env : PEnv} {syntaxArg : Arg} {before after : Prov} {value : ValueId}
    (physical : CallArgumentPhysical env syntaxArg before value) (bounded : value < before.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    CallArgumentPhysical env syntaxArg after value := by
  intro mutability place source shape
  rw [retained value bounded]
  exact physical mutability place source shape

theorem CallArgumentsPhysical.retained {env : PEnv} {before after : Prov}
    {syntaxArgs : List Arg} {args : List ValueId}
    (physical : CallArgumentsPhysical env before syntaxArgs args)
    (bounded : ∀ (index : Nat) (argument : ValueId), args[index]? = some argument → argument < before.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    CallArgumentsPhysical env after syntaxArgs args := by
  intro index argument syntaxArg row source
  exact (physical index argument syntaxArg row source).retained (bounded index argument row) retained

def CallOccurrence (env : PEnv) (root : DemandNode) (func : Func) (upper : Prov)
    (value : ValueId) (callee : FnId) (args : List ValueId) (origin : Option OriginId) : Prop :=
  ∃ localEnv path syntaxArgs sourceOrigin before argumentRoots argumentsAfter resultRoots after,
    localEnv.access = env.access ∧ origin = some sourceOrigin ∧
    DemandNodeAt root path (.expression (.call callee syntaxArgs sourceOrigin)) ∧
    rpArgs localEnv syntaxArgs before = .ok (argumentRoots, argumentsAfter) ∧
    checkContents localEnv callee syntaxArgs argumentRoots = .ok () ∧
    rpCall localEnv callee argumentRoots argumentsAfter = .ok (resultRoots, after) ∧
    value < upper.vals.size ∧ GIR.RootsRefine func (rootsAt upper.vals value) resultRoots ∧
    (∀ (index : Nat) (argument : ValueId), args[index]? = some argument → argument < upper.vals.size ∧
      ∃ roots, argumentRoots[index]? = some roots ∧ GIR.RootsRefine func (rootsAt upper.vals argument) roots) ∧
    CallArgumentsPhysical localEnv upper syntaxArgs args ∧ CallArgumentsTrace localEnv syntaxArgs args func callee sourceOrigin

def InstructionOccurrences (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (inst : Inst) : Prop :=
  (∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands inst, valRefLike types value = true →
    OperandOccurrence env root func upper value) ∧
  (∀ value address, inst = .def value (.load address) → valRefLike types value = true →
    ReadOccurrence env root func upper value address) ∧
  (∀ value callee args origin, inst = .def value (.call callee args origin) →
    CallOccurrence env root func upper value callee args origin) ∧
  (∀ address value origin, inst = .eff (.store address value origin) → valRefLike types value = true →
    StoreOccurrence env root func upper address value origin) ∧
  (∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands inst, ∀ mutability payload,
    types[value]? = some (some (.data (.ref mutability payload))) →
      ConsumedReferenceOccurrence env root func types upper value)

theorem InstructionOccurrences.no_references {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {inst : Inst}
    (absent : ∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands inst, ∀ mutability payload,
      types[value]? ≠ some (some (.data (.ref mutability payload)))) :
    ∀ value ∈ GIR.ReplacementContentFlow.Model.accessOperands inst, ∀ mutability payload,
      types[value]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper value :=
  fun value member mutability payload row => False.elim (absent value member mutability payload row)

theorem InstructionOccurrences.no_store {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {inst : Inst}
    (absent : ∀ address value origin, inst ≠ .eff (.store address value origin)) :
    ∀ address value origin, inst = .eff (.store address value origin) → valRefLike types value = true →
      StoreOccurrence env root func upper address value origin :=
  fun address value origin same _ => False.elim (absent address value origin same)

abbrev OccurrenceLedger (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (before after : LS) : Prop :=
  EmitsOnly (InstructionOccurrences env root func types upper) before after

theorem OperandOccurrence.retained {env : PEnv} {root : DemandNode} {func : Func}
    {before after : Prov} {value : ValueId}
    (origin : OperandOccurrence env root func before value)
    (growth : before.vals.size ≤ after.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    OperandOccurrence env root func after value := by
  obtain ⟨path, node, start, roots, finish, source, replay, bounded, refined⟩ := origin
  refine ⟨path, node, start, roots, finish, source, replay, Nat.lt_of_lt_of_le bounded growth, ?_⟩
  rw [retained value bounded]
  exact refined

theorem ReadOccurrence.retained {env : PEnv} {root : DemandNode} {func : Func}
    {before after : Prov} {value address : ValueId}
    (origin : ReadOccurrence env root func before value address)
    (growth : before.vals.size ≤ after.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    ReadOccurrence env root func after value address := by
  obtain ⟨localEnv, path, place, start, placeRoots, placeAfter, valueRoots, finish, accessEq, source, placeReplay,
    valueReplay, addressBound, valueBound, addressRefined, valueRefined, physical⟩ := origin
  refine ⟨localEnv, path, place, start, placeRoots, placeAfter, valueRoots, finish, accessEq, source, placeReplay,
    valueReplay, Nat.lt_of_lt_of_le addressBound growth, Nat.lt_of_lt_of_le valueBound growth, ?_, ?_, ?_⟩
  · rw [retained address addressBound]; exact addressRefined
  · rw [retained value valueBound]; exact valueRefined
  · rw [retained address addressBound]; exact physical

theorem CallOccurrence.retained {env : PEnv} {root : DemandNode} {func : Func}
    {before after : Prov} {value callee : Nat} {args : List ValueId} {origin : Option OriginId}
    (occurrence : CallOccurrence env root func before value callee args origin)
    (growth : before.vals.size ≤ after.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    CallOccurrence env root func after value callee args origin := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, start, argumentRoots, argumentsAfter, resultRoots, finish,
    accessEq, originEq, source, argumentsReplay, contents, callReplay, valueBound, valueRefined, arguments, physical, trace⟩ := occurrence
  refine ⟨localEnv, path, syntaxArgs, sourceOrigin, start, argumentRoots, argumentsAfter, resultRoots, finish,
    accessEq, originEq, source, argumentsReplay, contents, callReplay, Nat.lt_of_lt_of_le valueBound growth, ?_, ?_, ?_, trace⟩
  · rw [retained value valueBound]; exact valueRefined
  · intro index argument row
    obtain ⟨bounded, roots, rootsRow, refined⟩ := arguments index argument row
    refine ⟨Nat.lt_of_lt_of_le bounded growth, roots, rootsRow, ?_⟩
    rw [retained argument bounded]; exact refined
  · exact physical.retained (fun index argument row => (arguments index argument row).1) retained

theorem InstructionOccurrences.retained {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {before after : Prov} {inst : Inst}
    (origins : InstructionOccurrences env root func types before inst)
    (growth : before.vals.size ≤ after.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    InstructionOccurrences env root func types after inst :=
  ⟨fun value member reference => (origins.1 value member reference).retained growth retained,
    fun value address same reference => (origins.2.1 value address same reference).retained growth retained,
    fun value callee args origin same => (origins.2.2.1 value callee args origin same).retained growth retained,
    fun address value origin same reference => (origins.2.2.2.1 address value origin same reference).retained growth retained,
    fun value member mutability payload row =>
      (origins.2.2.2.2 value member mutability payload row).retained growth retained⟩

theorem OccurrenceLedger.retained {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {before after : Prov} {initial final : LS}
    (ledger : OccurrenceLedger env root func types before initial final)
    (growth : before.vals.size ≤ after.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    OccurrenceLedger env root func types after initial final := by
  refine ⟨ledger.blocks, ?_, ?_⟩
  · intro index body row
    obtain ⟨next, nextRow, params, tail, appended, origins⟩ := ledger.old index body row
    exact ⟨next, nextRow, params, tail, appended,
      fun inst member => (origins inst member).retained growth retained⟩
  · intro index body row lower inst member
    exact (ledger.fresh index body row lower inst member).retained growth retained

#print axioms CallArgumentPhysical.retained
#print axioms CallArgumentsPhysical.retained
#print axioms OccurrenceLedger.retained
#print axioms sourcePath_append

#print axioms OperandOccurrence.retained

end Goose.Lower.Validation.ReplacementContentFlowSource
