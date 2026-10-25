import Goose.Construct.Eval
import Goose.Construct.Roots

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst Loc VarId)

structure RootInterpretation where
  environment : RuntimeActivation
  globalCount : Nat
  parameters : Nat → RootInst → Prop

inductive Instantiates (interpretation : RootInterpretation) : RootRef → RootInst → Prop
  | global (id : Nat) (declared : id < interpretation.globalCount) :
      Instantiates interpretation (.global id) (.global id)
  | static (id : Nat) (synthetic : interpretation.globalCount ≤ id) :
      Instantiates interpretation .static (.global id)
  | local (id : VarId) (descriptor : LocalVar) (scope : Nat)
      (declared : interpretation.environment.vars[id]? = some descriptor)
      (active : interpretation.environment.scopes.find? (fun entry => entry.1 == descriptor.scope) =
        some (descriptor.scope, scope)) :
      Instantiates interpretation (.local id) (.local interpretation.environment.act scope id)
  | parameter (id : Nat) (root : RootInst) (actual : interpretation.parameters id root) :
      Instantiates interpretation (.param id) root

def RootIn (interpretation : RootInterpretation) (roots : List RootRef) (actual : RootInst) : Prop :=
  ∃ symbolic ∈ roots, Instantiates interpretation symbolic actual

inductive DirectReference : Value → Loc → Prop
  | reference (location : Loc) : DirectReference (.ref location) location
  | slice (location : Loc) (start count : Nat) : DirectReference (.slice location start count) location

def DirectValueRooted (interpretation : RootInterpretation) (roots : List RootRef) (value : Value) : Prop :=
  ∀ location, DirectReference value location → RootIn interpretation roots location.root

def LocalValueRooted (interpretation : RootInterpretation) (context : Context) (id : VarId) (value : Value) : Prop :=
  ∀ location, DirectReference value location →
    ∃ roots, (context.varRoots.find? (·.1 == id)).map Prod.snd = some roots ∧
      RootIn interpretation roots location.root

def LocalRootCorrespondence (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (state : ExecutionState) : Prop :=
  ∀ id ∈ visible, ∀ root value,
    rootOf interpretation.environment id state = .ok root state →
    state.objects.lookup root = some value →
    LocalValueRooted interpretation context id value

theorem localValueRooted_empty (interpretation : RootInterpretation) (context : Context)
    (id : VarId) (value : Value) (rooted : DirectValueRooted interpretation [] value) :
    LocalValueRooted interpretation context id value := by
  intro location reference
  obtain ⟨symbolic, absent, _⟩ := rooted location reference
  cases absent

def ContentRootCorrespondence (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (fuel : Nat) (layout : LayoutEnv) (state : ExecutionState) : Prop :=
  ∀ id ∈ visible, ∀ root location value,
    rootOf interpretation.environment id state = .ok root state →
    state.objects.lookup root = some (.ref location) →
    readLoc fuel layout location state = .ok value state →
    ∀ interior, DirectReference value interior →
      ∃ roots, (context.contentRoots.find? (·.1 == id)).map Prod.snd = some roots ∧
        RootIn interpretation roots interior.root

theorem rootIn_mono {interpretation : RootInterpretation} {lower upper : List RootRef}
    {root : RootInst} (included : lower ⊆ upper) (actual : RootIn interpretation lower root) :
    RootIn interpretation upper root := by
  obtain ⟨symbolic, member, instantiated⟩ := actual
  exact ⟨symbolic, included member, instantiated⟩

theorem rootIn_append {interpretation : RootInterpretation} {left right : List RootRef}
    {root : RootInst} : RootIn interpretation (left ++ right) root ↔
      RootIn interpretation left root ∨ RootIn interpretation right root := by
  simp only [RootIn, List.mem_append]
  constructor
  · rintro ⟨symbolic, leftMember | rightMember, instantiated⟩
    · exact Or.inl ⟨symbolic, leftMember, instantiated⟩
    · exact Or.inr ⟨symbolic, rightMember, instantiated⟩
  · rintro (⟨symbolic, member, instantiated⟩ | ⟨symbolic, member, instantiated⟩)
    · exact ⟨symbolic, Or.inl member, instantiated⟩
    · exact ⟨symbolic, Or.inr member, instantiated⟩

theorem directValueRooted_mono {interpretation : RootInterpretation} {lower upper : List RootRef}
    {value : Value} (included : lower ⊆ upper) (rooted : DirectValueRooted interpretation lower value) :
    DirectValueRooted interpretation upper value := by
  intro location reference
  exact rootIn_mono included (rooted location reference)

theorem rootOf_instantiates (interpretation : RootInterpretation) (id : VarId)
    (state : ExecutionState) (root : RootInst)
    (resolved : rootOf interpretation.environment id state = .ok root state) :
    Instantiates interpretation (.local id) root := by
  unfold rootOf at resolved
  cases declared : interpretation.environment.vars[id]? with
  | none => simp [declared, fault, EvalM.stop] at resolved
  | some descriptor =>
    cases active : interpretation.environment.scopes.find? (fun entry => entry.1 == descriptor.scope) with
    | none => simp [declared, active, fault, EvalM.stop] at resolved
    | some entry =>
      obtain ⟨scopeId, scope⟩ := entry
      have matching : scopeId = descriptor.scope := by
        have predicate := List.find?_some active
        simpa using predicate
      subst scopeId
      simp only [declared, active, pure] at resolved
      cases resolved
      exact .local id descriptor scope declared active

theorem localRootCorrespondence_empty (interpretation : RootInterpretation) (context : Context)
    (state : ExecutionState) : LocalRootCorrespondence interpretation context [] state := by
  intro id member
  cases member

theorem rootOf_transfer (interpretation : RootInterpretation) (id : VarId)
    (before after : ExecutionState) (root : RootInst)
    (resolved : rootOf interpretation.environment id before = .ok root before) :
    rootOf interpretation.environment id after = .ok root after := by
  have actual := rootOf_instantiates interpretation id before root resolved
  cases actual with
  | «local» id descriptor scope declared active => simp only [rootOf, declared, active, pure]

theorem rootOf_variable (interpretation : RootInterpretation) (id : VarId)
    (state : ExecutionState) (root : RootInst)
    (resolved : rootOf interpretation.environment id state = .ok root state) :
    ∃ scope, root = .local interpretation.environment.act scope id := by
  have actual := rootOf_instantiates interpretation id state root resolved
  cases actual with
  | «local» id descriptor scope declared active => exact ⟨scope, rfl⟩

theorem rootOf_variable_injective (interpretation : RootInterpretation) (left right : VarId)
    (state : ExecutionState) (root : RootInst)
    (leftResolved : rootOf interpretation.environment left state = .ok root state)
    (rightResolved : rootOf interpretation.environment right state = .ok root state) : left = right := by
  obtain ⟨leftScope, equal⟩ := rootOf_variable interpretation left state root leftResolved
  obtain ⟨rightScope, other⟩ := rootOf_variable interpretation right state root rightResolved
  rw [equal] at other
  cases other
  rfl

theorem localRootCorrespondence_objects (interpretation : RootInterpretation) (context : Context)
    (visible : List VarId) (before after : ExecutionState)
    (same : before.objects = after.objects)
    (valid : LocalRootCorrespondence interpretation context visible before) :
    LocalRootCorrespondence interpretation context visible after := by
  intro id member root value resolved found location reference
  have beforeResolved := rootOf_transfer interpretation id after before root resolved
  exact valid id member root value beforeResolved (same ▸ found) location reference

theorem evalValue_visibleLocal_rooted (fuel : Nat) (config : EvalConfig)
    (interpretation : RootInterpretation) (context : Context) (visible : List VarId)
    (state : ExecutionState) (valid : LocalRootCorrespondence interpretation context visible state)
    (id : VarId) (member : id ∈ visible) (root : RootInst) (value : Value)
    (resolved : rootOf interpretation.environment id state = .ok root state)
    (found : state.objects.lookup root = some value) (location : Loc)
    (reference : DirectReference value location) :
    evalValue (fuel + 2) config interpretation.environment (.read (.var id)) state = .ok value state ∧
      ∃ roots, (context.varRoots.find? (·.1 == id)).map Prod.snd = some roots ∧
        RootIn interpretation roots location.root := by
  refine ⟨?_, valid id member root value resolved found location reference⟩
  simp only [evalValue, evalPlace, bind, resolved, pure, readLoc, EvalM.get, found, readValuePath]

theorem evalValue_localReference_rooted (fuel : Nat) (config : EvalConfig)
    (interpretation : RootInterpretation) (state : ExecutionState) (id : VarId)
    (mutability : Goose.Core.Mutability) (root : RootInst)
    (resolved : rootOf interpretation.environment id state = .ok root state) :
    evalValue (fuel + 2) config interpretation.environment (.ref mutability (.var id)) state =
      .ok (.ref ⟨root, []⟩) state ∧ RootIn interpretation [.local id] root := by
  refine ⟨?_, RootRef.local id, by simp, rootOf_instantiates interpretation id state root resolved⟩
  simp only [evalValue, evalPlace, bind, resolved, pure]

theorem evalValue_referenceSlice_rooted (fuel : Nat) (config : EvalConfig)
    (interpretation : RootInterpretation) (context : Context) (visible : List VarId) (state : ExecutionState)
    (valid : ContentRootCorrespondence interpretation context visible (fuel + 3) config.layout state)
    (id : VarId) (member : id ∈ visible) (root : RootInst) (location : Loc) (value : Value)
    (resolved : rootOf interpretation.environment id state = .ok root state)
    (found : state.objects.lookup root = some (.ref location))
    (read : readLoc (fuel + 3) config.layout location state = .ok value state)
    (interior : Loc) (reference : DirectReference value interior) :
    evalValue (fuel + 4) config interpretation.environment (.read (.deref (.read (.var id)))) state = .ok value state ∧
      ∃ roots, (context.contentRoots.find? (·.1 == id)).map Prod.snd = some roots ∧
        RootIn interpretation roots interior.root := by
  have holder : evalValue (fuel + 2) config interpretation.environment (.read (.var id)) state =
      .ok (.ref location) state := by
    simp only [evalValue, evalPlace, bind, resolved, pure, readLoc, EvalM.get, found, readValuePath]
  have address : evalPlace (fuel + 3) config interpretation.environment (.deref (.read (.var id))) state =
      .ok location state := by
    simp only [evalPlace, bind, holder, expectRef, pure]
  refine ⟨?_, valid id member root location value resolved found read interior reference⟩
  simp only [evalValue, bind, address, read]

def AliasComplete (interpretation : RootInterpretation) (aliases : List (RootRef × RootRef)) : Prop :=
  ∀ left right root, Instantiates interpretation left root → Instantiates interpretation right root →
    RootAlias aliases left right

theorem aliasComplete_mono (interpretation : RootInterpretation) (lower upper : List (RootRef × RootRef))
    (complete : AliasComplete interpretation lower) (included : lower ⊆ upper) : AliasComplete interpretation upper := by
  intro left right root leftInst rightInst
  rcases complete left right root leftInst rightInst with equal | forward | backward
  · exact Or.inl equal
  · exact Or.inr (.inl (included forward))
  · exact Or.inr (.inr (included backward))

def SymbolicDisjoint (aliases : List (RootRef × RootRef)) (left right : List RootRef) : Prop :=
  ∀ a ∈ left, ∀ b ∈ right, a ≠ b ∧ (a, b) ∉ aliases ∧ (b, a) ∉ aliases

theorem rooted_disjoint {interpretation : RootInterpretation} {aliases : List (RootRef × RootRef)}
    {left right : List RootRef} (complete : AliasComplete interpretation aliases)
    (disjoint : SymbolicDisjoint aliases left right) {a b : RootInst}
    (leftRoot : RootIn interpretation left a) (rightRoot : RootIn interpretation right b) : a ≠ b := by
  intro equal
  subst b
  obtain ⟨leftSymbol, leftMember, leftInst⟩ := leftRoot
  obtain ⟨rightSymbol, rightMember, rightInst⟩ := rightRoot
  obtain ⟨different, forward, backward⟩ := disjoint leftSymbol leftMember rightSymbol rightMember
  rcases complete leftSymbol rightSymbol a leftInst rightInst with equal | member | member
  · exact different equal
  · exact forward member
  · exact backward member

end Goose.Proofs.ConstructionRootCorrespondence
