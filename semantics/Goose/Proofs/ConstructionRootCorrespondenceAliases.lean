import Goose.Proofs.ConstructionRootCorrespondenceCalls

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (RootInst)

def MayAlias (aliases : List (RootRef × RootRef)) (left right : RootRef) : Prop :=
  left = right ∨ (left, right) ∈ aliases ∨ (right, left) ∈ aliases

theorem mayAlias_symm {aliases : List (RootRef × RootRef)} {left right : RootRef}
    (alias : MayAlias aliases left right) : MayAlias aliases right left := by
  rcases alias with equal | forward | backward
  · exact Or.inl equal.symm
  · exact Or.inr (.inr forward)
  · exact Or.inr (.inl backward)

def RootsOverlap (aliases : List (RootRef × RootRef)) (left right : List RootRef) : Prop :=
  ∃ a ∈ left, ∃ b ∈ right, MayAlias aliases a b

theorem sharedRoot_overlap (interpretation : RootInterpretation) (aliases : List (RootRef × RootRef))
    (complete : AliasComplete interpretation aliases) (left right : List RootRef) (root : RootInst)
    (leftRoot : RootIn interpretation left root) (rightRoot : RootIn interpretation right root) :
    RootsOverlap aliases left right := by
  obtain ⟨a, aMember, aRoot⟩ := leftRoot
  obtain ⟨b, bMember, bRoot⟩ := rightRoot
  exact ⟨a, aMember, b, bMember, complete a b root aRoot bRoot⟩

structure CallAliasCoverage (callerAliases calleeAliases : List (RootRef × RootRef))
    (arguments : List (List RootRef)) (globalCount : Nat) : Prop where
  parameters : ∀ left right a b, arguments[left]? = some a → arguments[right]? = some b →
    RootsOverlap callerAliases a b → MayAlias calleeAliases (.param left) (.param right)
  globals : ∀ index roots global, arguments[index]? = some roots → global < globalCount →
    RootsOverlap callerAliases roots [.global global] → MayAlias calleeAliases (.param index) (.global global)
  static : ∀ index roots, arguments[index]? = some roots →
    RootsOverlap callerAliases roots [.static] → MayAlias calleeAliases (.param index) .static

def RootFrontier (interpretation : RootInterpretation) (nextAct : Nat) : Prop :=
  interpretation.environment.act < nextAct ∧
    ∀ index act scope variableId, interpretation.parameters index (.local act scope variableId) → act < nextAct

theorem instantiates_before {interpretation : RootInterpretation} {nextAct : Nat}
    (frontier : RootFrontier interpretation nextAct) (symbolic : RootRef) (act scope variableId : Nat)
    (instantiated : Instantiates interpretation symbolic (.local act scope variableId)) : act < nextAct := by
  cases instantiated with
  | «local» id descriptor scope declared active => exact frontier.1
  | parameter id root actual => exact frontier.2 id _ _ _ actual

theorem call_aliasComplete (caller : RootInterpretation) (callee : RuntimeActivation)
    (arguments : List (List RootRef)) (callerAliases calleeAliases : List (RootRef × RootRef))
    (complete : AliasComplete caller callerAliases)
    (coverage : CallAliasCoverage callerAliases calleeAliases arguments caller.globalCount)
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
      apply mayAlias_symm
      apply coverage.globals index roots id rootsAt declared
      exact sharedRoot_overlap caller callerAliases complete roots [.global id] _ rooted
        ⟨.global id, by simp, .global id declared⟩
  | static id synthetic =>
    cases rightInst with
    | global id declared => omega
    | static id synthetic => exact Or.inl rfl
    | parameter index root supplied =>
      obtain ⟨roots, rootsAt, rooted⟩ := supplied
      apply mayAlias_symm
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
