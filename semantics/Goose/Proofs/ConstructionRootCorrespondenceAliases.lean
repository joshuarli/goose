import Goose.Proofs.ConstructionRootCorrespondenceCalls

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst)

theorem rootAlias_symm {aliases : List (RootRef × RootRef)} {left right : RootRef}
    (alias : RootAlias aliases left right) : RootAlias aliases right left := by
  rcases alias with equal | forward | backward
  · exact Or.inl equal.symm
  · exact Or.inr (.inr forward)
  · exact Or.inr (.inl backward)

theorem rootSetsOverlap_checked (aliases : List (RootRef × RootRef)) (left right : List RootRef) :
    RootSetsOverlap aliases left right ↔
      (left.any fun a => right.any fun b =>
        a == b || aliases.contains (a, b) || aliases.contains (b, a)) = true := by
  constructor
  · rintro ⟨a, aMember, b, bMember, alias⟩
    apply List.any_eq_true.mpr
    refine ⟨a, aMember, List.any_eq_true.mpr ⟨b, bMember, ?_⟩⟩
    simpa [RootAlias, or_assoc] using alias
  · intro checked
    obtain ⟨a, aMember, checked⟩ := List.any_eq_true.mp checked
    obtain ⟨b, bMember, alias⟩ := List.any_eq_true.mp checked
    exact ⟨a, aMember, b, bMember, by simpa [RootAlias, or_assoc] using alias⟩

theorem checkedRoots_disjoint (aliases : List (RootRef × RootRef)) (left right : List RootRef)
    (checked : (left.any fun a => right.any fun b =>
      a == b || aliases.contains (a, b) || aliases.contains (b, a)) = false) :
    SymbolicDisjoint aliases left right := by
  have excluded : ¬RootSetsOverlap aliases left right := by
    intro overlap
    have conflict := (rootSetsOverlap_checked aliases left right).mp overlap
    rw [checked] at conflict
    cases conflict
  intro a aMember b bMember
  exact ⟨fun equal => excluded ⟨a, aMember, b, bMember, Or.inl equal⟩,
    fun forward => excluded ⟨a, aMember, b, bMember, Or.inr (.inl forward)⟩,
    fun backward => excluded ⟨a, aMember, b, bMember, Or.inr (.inr backward)⟩⟩

theorem sharedRoot_overlap (interpretation : RootInterpretation) (aliases : List (RootRef × RootRef))
    (complete : AliasComplete interpretation aliases) (left right : List RootRef) (root : RootInst)
    (leftRoot : RootIn interpretation left root) (rightRoot : RootIn interpretation right root) :
    RootSetsOverlap aliases left right := by
  obtain ⟨a, aMember, aRoot⟩ := leftRoot
  obtain ⟨b, bMember, bRoot⟩ := rightRoot
  exact ⟨a, aMember, b, bMember, complete a b root aRoot bRoot⟩

def RootFrontier (interpretation : RootInterpretation) (nextAct : Nat) : Prop :=
  interpretation.environment.act < nextAct ∧
    ∀ index act scope variableId, interpretation.parameters index (.local act scope variableId) → act < nextAct

theorem instantiates_before {interpretation : RootInterpretation} {nextAct : Nat}
    (frontier : RootFrontier interpretation nextAct) (symbolic : RootRef) (act scope variableId : Nat)
    (instantiated : Instantiates interpretation symbolic (.local act scope variableId)) : act < nextAct := by
  cases instantiated with
  | «local» id descriptor scope declared active => exact frontier.1
  | parameter id root actual => exact frontier.2 id _ _ _ actual

theorem rootFrontier_mono {interpretation : RootInterpretation} {before after : Nat}
    (frontier : RootFrontier interpretation before) (advanced : before ≤ after) : RootFrontier interpretation after :=
  ⟨Nat.lt_of_lt_of_le frontier.1 advanced,
    fun index act scope variableId supplied => Nat.lt_of_lt_of_le (frontier.2 index act scope variableId supplied) advanced⟩

theorem call_rootFrontier (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (nextAct : Nat)
    (callerFrontier : RootFrontier caller callee.act) (calleeFrontier : callee.act < nextAct) :
    RootFrontier (CallInterpretation caller callee arguments) nextAct := by
  refine ⟨calleeFrontier, ?_⟩
  intro index act scope variableId supplied
  obtain ⟨roots, rootsAt, symbolic, member, actual⟩ := supplied
  exact Nat.lt_trans (instantiates_before callerFrontier symbolic act scope variableId actual) calleeFrontier

theorem freshAct_callFrontier (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (state : ExecutionState)
    (frontier : RootFrontier caller state.nextAct) :
    freshAct state = .ok state.nextAct { state with nextAct := state.nextAct + 1 } ∧
      RootFrontier caller (state.nextAct + 1) ∧
      RootFrontier (CallInterpretation caller { callee with act := state.nextAct } arguments) (state.nextAct + 1) := by
  refine ⟨?_, rootFrontier_mono frontier (Nat.le_succ _), ?_⟩
  · simp only [freshAct, bind, EvalM.get, EvalM.set, pure]
  · exact call_rootFrontier caller { callee with act := state.nextAct } arguments _ frontier (Nat.lt_succ_self _)

theorem mappedResultRoot_outsideActivation (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (declared mapped : List RootRef)
    (checked : mapResultRoots arguments [] declared = .ok mapped) (root : RootInst)
    (rooted : RootIn (CallInterpretation caller callee arguments) declared root)
    (frontier : RootFrontier caller callee.act) :
    ∀ scope variableId, root ≠ .local callee.act scope variableId := by
  have inherited := mapResultRoots_rooted caller callee arguments declared [] mapped checked root (Or.inr rooted)
  obtain ⟨symbolic, member, actual⟩ := inherited
  intro scope variableId equal
  rw [equal] at actual
  have before := instantiates_before frontier symbolic callee.act scope variableId actual
  exact Nat.lt_irrefl callee.act before

theorem call_aliasComplete (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (callerAliases calleeAliases : List (RootRef × RootRef))
    (complete : AliasComplete caller callerAliases)
    (coverage : AliasClosure callerAliases calleeAliases arguments caller.globalCount)
    (frontier : RootFrontier caller callee.act) :
    AliasComplete (CallInterpretation caller callee arguments) calleeAliases := by
  intro left right root leftInst rightInst
  cases leftInst with
  | global id declared =>
    cases rightInst with
    | global id declared => exact Or.inl rfl
    | static id synthetic => omega
    | parameter index root supplied =>
      obtain ⟨roots, rootsAt, rooted⟩ := supplied
      apply rootAlias_symm
      apply coverage.globals index roots id rootsAt declared
      exact sharedRoot_overlap caller callerAliases complete roots [.global id] _ rooted
        ⟨.global id, by simp, .global id declared⟩
  | static id synthetic =>
    cases rightInst with
    | global id declared => omega
    | static id synthetic => exact Or.inl rfl
    | parameter index root supplied =>
      obtain ⟨roots, rootsAt, rooted⟩ := supplied
      apply rootAlias_symm
      apply coverage.static index roots rootsAt
      exact sharedRoot_overlap caller callerAliases complete roots [.static] _ rooted
        ⟨.static, by simp, .static id synthetic⟩
  | «local» id descriptor scope declared active =>
    cases rightInst with
    | «local» id descriptor scope declared active => exact Or.inl rfl
    | parameter index root supplied =>
      obtain ⟨roots, rootsAt, symbolic, member, rooted⟩ := supplied
      have earlier := instantiates_before frontier symbolic callee.act scope id rooted
      exact (Nat.lt_irrefl callee.act earlier).elim
  | parameter index root supplied =>
    obtain ⟨roots, rootsAt, rooted⟩ := supplied
    cases rightInst with
    | global id declared =>
      apply coverage.globals index roots id rootsAt declared
      exact sharedRoot_overlap caller callerAliases complete roots [.global id] _ rooted
        ⟨.global id, by simp, .global id declared⟩
    | static id synthetic =>
      apply coverage.static index roots rootsAt
      exact sharedRoot_overlap caller callerAliases complete roots [.static] _ rooted
        ⟨.static, by simp, .static id synthetic⟩
    | «local» id descriptor scope declared active =>
      obtain ⟨symbolic, member, actual⟩ := rooted
      have earlier := instantiates_before frontier symbolic callee.act scope id actual
      exact (Nat.lt_irrefl callee.act earlier).elim
    | parameter other root supplied =>
      obtain ⟨otherRoots, otherAt, otherRooted⟩ := supplied
      exact coverage.parameters index other roots otherRoots rootsAt otherAt
        (sharedRoot_overlap caller callerAliases complete roots otherRoots root rooted otherRooted)

end Goose.Proofs.ConstructionRootCorrespondence
