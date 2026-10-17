import Goose.Lower.Validation.ReplacementAliases
import Goose.Lower.Validation.ReplacementParameterRoots
import Goose.Lower.Validation.ProvenanceConvergenceFixedPoint

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive RootForward : Op → ValueId → Prop
  | fieldAddr (value field) : RootForward (.fieldAddr value field) value
  | refElem (value index) : RootForward (.refElem value index) value
  | viewSlice (kind value lower upper origin) : RootForward (.viewSlice kind value lower upper origin) value
  | indexChecked (value index origin) : RootForward (.indexChecked value index origin) value
  | indexProven (value index) : RootForward (.indexProven value index) value
  | refFreeze (value) : RootForward (.refFreeze value) value
  | ownerBorrow (value) : RootForward (.ownerBorrow value) value
  | sliceView (value) : RootForward (.sliceView value) value
  | push (value element origin) : RootForward (.push value element origin) value
  | snapshot (ty value) : RootForward (.snapshot ty value) value

theorem provenance_closed_forward {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {provenance : Prov}
    (closed : ProvenanceConvergence.InstructionRootsClosed results types func provenance)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result input : ValueId} {op : Op} (definition : .def result op ∈ block.insts)
    (bounded : result < provenance.vals.size) (forward : RootForward op input) :
    rootsAt provenance.vals input ⊆ rootsAt provenance.vals result := by
  have generated := closed.definition blockMember definition bounded
  cases forward <;> exact generated

theorem provenance_closed_load_local {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {provenance : Prov}
    (closed : ProvenanceConvergence.InstructionRootsClosed results types func provenance)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {result address : ValueId} {slot : SlotId} (definition : .def result (.load address) ∈ block.insts)
    (bounded : result < provenance.vals.size) (reference : valRefLike types result = true)
    (addressRoot : RootRef.local slot ∈ rootsAt provenance.vals address) :
    rootsAt provenance.slots slot ⊆ rootsAt provenance.vals result := by
  intro root member
  apply closed.definition blockMember definition bounded
  simp only [rootsOfDef, reference, ite_true]
  apply (unionRoots_contains_prior _ _).subset
  exact List.mem_flatMap.mpr ⟨.local slot, addressRoot, member⟩

theorem provenance_closed_read_slot {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {provenance : Prov}
    (closed : ProvenanceConvergence.InstructionRootsClosed results types func provenance)
    {initBlock addressBlock loadBlock : GIR.Block}
    (initMember : initBlock ∈ func.blocks.toList) (addressMember : addressBlock ∈ func.blocks.toList)
    (loadMember : loadBlock ∈ func.blocks.toList)
    {input address result : ValueId} {slot : SlotId} {origin : OriginId}
    (initialized : .eff (.slotInit slot input origin) ∈ initBlock.insts)
    (addressed : .def address (.slotAddr slot) ∈ addressBlock.insts)
    (loaded : .def result (.load address) ∈ loadBlock.insts)
    (slotBound : slot < provenance.slots.size) (addressBound : address < provenance.vals.size)
    (resultBound : result < provenance.vals.size) (reference : valRefLike types result = true) :
    rootsAt provenance.vals input ⊆ rootsAt provenance.vals result := by
  have addressRoot : RootRef.local slot ∈ rootsAt provenance.vals address :=
    closed.definition addressMember addressed addressBound (by simp [rootsOfDef])
  intro root member
  exact provenance_closed_load_local closed loadMember loaded resultBound reference addressRoot
    (closed.slotInit initMember initialized slotBound member)

def ReplacementRootsWithin (query : ReplacementRootQuery) (source : List RootRef) : Prop :=
  ∃ roots, query = some roots ∧ roots ⊆ source

theorem replacementQueries_known_of_member (module : GIR.Module) (types : Array (Option VTy)) {func : Func} {provenance : Prov} {value : ValueId}
    {root : RootRef} (member : root ∈ rootsAt provenance.vals value) :
    ∃ roots, (replacementQueries module func types provenance).value value = some roots := by
  cases raw : rootsAt provenance.vals value with
  | nil => simp [raw] at member
  | cons first rest =>
    exact ⟨(first :: rest).flatMap func.expandParameterRoot, by
      simp only [replacementQueries_value, raw]⟩

theorem replacementRootsWithin_of_member (module : GIR.Module) (types : Array (Option VTy)) {func : Func} {provenance : Prov} {value : ValueId}
    {root : RootRef} {source : List RootRef} (member : root ∈ rootsAt provenance.vals value)
    (upper : (rootsAt provenance.vals value).flatMap func.expandParameterRoot ⊆ source) :
    ReplacementRootsWithin ((replacementQueries module func types provenance).value value) source := by
  obtain ⟨roots, known⟩ := replacementQueries_known_of_member module types member
  refine ⟨roots, known, ?_⟩
  have normalized := replacementQueries_values module func types provenance value
  rw [known] at normalized
  change roots = _ at normalized
  rw [normalized]
  exact upper

theorem replacementApart_of_source {queries : ReplacementQueries} {owner : ValueId}
    {query : ReplacementRootQuery} {ownerRoots sourceRoots : List RootRef}
    (ownerKnown : ReplacementRootsWithin (queries.value owner) ownerRoots)
    (sourceKnown : ReplacementRootsWithin query sourceRoots)
    (disjoint : DemandRootsDisjoint ownerRoots sourceRoots) :
    ReplacementApart queries owner query := by
  obtain ⟨ownerActual, ownerEqual, ownerUpper⟩ := ownerKnown
  obtain ⟨sourceActual, sourceEqual, sourceUpper⟩ := sourceKnown
  refine Or.inr (Or.inr ⟨sourceActual, ownerActual, sourceEqual, ownerEqual, ?_⟩)
  intro source sourceMember owner ownerMember
  have apart := disjoint owner (ownerUpper ownerMember) source (sourceUpper sourceMember)
  cases owner <;> cases source <;> simp_all [Goose.Core.rootsMayOverlap, BEq.beq, eq_comm]

theorem accepted_replacement_place_retains {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (shrink : module.profile = .shrink)
    {planOwner : Nat} (ownerBound : planOwner < module.contexts.size + module.globals.size)
    {expected : List DemandExpectedPoint} (walk : DemandNode.expectedPoints module planOwner = .ok expected)
    {occurrence : DemandExpectedPoint} (member : occurrence ∈ expected)
    {path : List Nat} {place : Place} {access : AccessEnv} {forbidden : DemandOwner}
    (source : DemandExpectedSourceAt module planOwner path (.place place) .place occurrence)
    (accessAt : demandAccess? module planOwner = some access) (inherited : forbidden ∈ occurrence.forbidden)
    {sourceRoots : List RootRef} (rootsAtSource : access.placeRoots place = .ok sourceRoots)
    {queries : ReplacementQueries} {owner : ValueId} {query : ReplacementRootQuery}
    (ownerKnown : ReplacementRootsWithin (queries.value owner) forbidden.roots)
    (sourceKnown : ReplacementRootsWithin query sourceRoots)
    {facts : List ValueId} (present : owner ∈ facts) :
    owner ∈ killEmptyFacts facts query queries := by
  obtain ⟨roots, rootsAtPlace, disjoint⟩ := accepted_replacement_place_disjoint
    accepted shrink ownerBound walk member source accessAt inherited
  have same : roots = sourceRoots := Except.ok.inj (rootsAtPlace.symm.trans rootsAtSource)
  subst roots
  exact killEmptyFacts_retains present (replacementApart_of_source ownerKnown sourceKnown disjoint)

end Goose.Lower.Validation
