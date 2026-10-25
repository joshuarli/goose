import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.Proofs.Memory Goose.Core.Sound

private theorem wholeReplacementTypeInputs
    {tenv tenv' : TEnv} {sc tn tn' : Nat} {owner : Place} {replacement : Expr}
    {org : OriginId}
    (ht : tyStmt tenv sc (.assignWhole owner replacement org) tn = .ok (tenv', tn')) :
    tenv.mod.profile = .shrink ∧ tenv' = tenv ∧
    ∃ element target binding contents middle last,
      (target = .grow element ∨ target = .growshrink element) ∧
      tyPlace tenv owner tn = .ok (⟨target, binding, contents⟩, middle) ∧
      tyExpr tenv replacement middle = .ok (target, last) ∧ tn' = last := by
  simp only [tyStmt] at ht
  inv at ht
  obtain ⟨first, hshrink, _, target, binding, contents, middle, hplace, htail⟩ := ht
  simp only [requireShrink] at hshrink
  inv at hshrink
  obtain ⟨hprofile, rfl⟩ := hshrink
  have hprofile' : tenv.mod.profile = .shrink := by simpa using hprofile
  cases target <;> simp only at htail <;> inv at htail
  case grow element =>
    obtain ⟨rt, last, hexpr, hsame, after, hrun, _, henv, htn⟩ := htail
    have hsame' : rt = .grow element := by simpa using hsame
    subst rt
    simp only [checkOwnerRun] at hrun
    inv at hrun
    obtain ⟨_, hrunEq⟩ := hrun
    exact ⟨hprofile', henv, element, .grow element, binding, contents, middle, last,
      Or.inl rfl, hplace, hexpr, htn.trans hrunEq⟩
  case growshrink element =>
    obtain ⟨rt, last, hexpr, hsame, after, hrun, _, henv, htn⟩ := htail
    have hsame' : rt = .growshrink element := by simpa using hsame
    subst rt
    simp only [checkOwnerRun] at hrun
    inv at hrun
    obtain ⟨_, hrunEq⟩ := hrun
    exact ⟨hprofile', henv, element, .growshrink element, binding, contents, middle, last,
      Or.inr rfl, hplace, hexpr, htn.trans hrunEq⟩

theorem StmtSource.assignWholeChildren {cfg : Cfg} {env : Env} {state : St}
    {owner : Place} {replacement : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assignWhole owner replacement origin) state) :
    ∃ destination : PlaceSource cfg env owner state,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      destination.world = source.world ∧ destination.observation = source.observation ∧
      ∀ fuel location afterPlace clear,
        evalPlace fuel cfg env owner state = .ok location afterPlace →
        afterPlace.store.truncate location 0 = .ok clear →
        ∃ child : ExprSource cfg env replacement { afterPlace with store := clear },
          child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
          child.world = source.world ∧ child.observation = source.observation ∧
          child.ty = destination.ty ∧
          Footprint (insts env) (Dset source.world) state { afterPlace with store := clear } := by
  obtain ⟨profile, _, element, target, binding, contents, middle, last,
    resizable, ownerTyped, replacementTyped, _⟩ := wholeReplacementTypeInputs source.typed
  have moduleProfile : cfg.mod.profile = .shrink :=
    (congrArg Module.profile source.frame.mod_t).symm.trans profile
  have rooted := source.rooted
  rw [rpStmt] at rooted
  obtain ⟨ownerRoots, r1, ownerRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, r2, reads, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, r3, shrinks, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨replacementRoots, r4, replacementRooted, rooted⟩ := (st_bind_ok _ _ _ _).1 rooted
  obtain ⟨_, r5, writes, grows⟩ := (st_bind_ok _ _ _ _).1 rooted
  have e4 := (PMono.addWrites ownerRoots r4 () r5 writes).2.trans
    ((PMono.addGrows ownerRoots r5 () source.rootsEnd grows).2.trans source.effects)
  have e3 := (rpExpr_mono replacementRooted).2.trans e4
  have e2 := (PMono.addShrinks ownerRoots r2 () r3 shrinks).2.trans e3
  have e1 := (PMono.addReads ownerRoots r1 () r2 reads).2.trans e2
  have recorded : ∀ t, t ∈ rootsTargets ownerRoots → t ∈ source.world.E.shrinks := by
    have members : ∀ t, t ∈ rootsTargets ownerRoots → t ∈ r3.eff.shrinks := by
      unfold addShrinks addRoots at shrinks
      rw [st_modify_ok] at shrinks
      cases shrinks
      exact addTargets_right _ _
    intro t member
    exact e3.2.2.2.1 t (members t member)
  have placeAt : (DemandNode.statement (.assignWhole owner replacement origin)).child? 0 =
      some (.place owner) := by simp [DemandNode.child?, DemandNode.children]
  obtain ⟨destination, typingEq, rootsEq, typeEq, worldEq, observationEq, outputEq, mayEq,
    _, _, ownerRootsEq⟩ := source.placeChildSource owner placeAt
      (by simp [DemandNode.visibleForChild])
      (by intro x member; simp [Stmt.variables, member])
      (fun parent => replacement.variables ++ parent.future)
      (by intro parent x member; simpa [Stmt.variables, List.append_assoc] using
        List.mem_append_right owner.variables member)
      (by intro access parent; simp [DemandNode.childExpectation?, DemandNode.childFuture, placeAt])
      source.typingStart middle target binding contents source.rootsStart r1 ownerRoots
      ownerTyped ownerRooted e1
  refine ⟨destination, typingEq, rootsEq, worldEq, observationEq, ?_⟩
  intro fuel location afterPlace clear done truncated
  have result := destination.result fuel location done
  have frame := result.frame
  rw [typingEq, rootsEq, worldEq, outputEq] at frame
  have observed := result.observed
  rw [worldEq, observationEq, mayEq] at observed
  have classified := result.classified
  rw [worldEq, observationEq] at classified
  have place := result.typed
  rw [worldEq, rootsEq, typeEq] at place
  have gam := result.rooted
  rw [worldEq, ownerRootsEq] at gam
  have ownerGam := result.ownerRooted
  rw [worldEq, typeEq, ownerRootsEq] at ownerGam
  have ownerElement : target.ownerElem? = some element := by
    rcases resizable with rfl | rfl <;> simp [Ty.ownerElem?]
  have ownerLoc : LocTy afterPlace.store location target := by
    rcases place with ⟨_, loc, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, ref, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, path, _⟩
    · exact Core.Sound.access source.permission loc gam (fun t ht =>
        Or.inr (Or.inr (Or.inr (recorded t ht))))
    · cases target <;> simp_all [Ty.ownerElem?, Ty.isRefLike]
    · rw [path] at ownerElement
      simp [Ty.ownerElem?] at ownerElement
  obtain ⟨_, _, _, _, _, _, clearFrame, clearFootprint, _, _, clearObserved, _, _, clearClassified⟩ :=
    statementAssignWholeClearFrame source.context moduleProfile source.active source.access
      source.protection source.permission resizable ownerTyped ownerRooted place ownerLoc gam
      (ownerGam ⟨element, resizable⟩) recorded frame observed (classified moduleProfile) truncated
  obtain ⟨child, childTyping, childRoots, childType, childWorld, childObservation, _⟩ :=
    source.expressionChildSource 1 replacement
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNode.visibleForChild]) middle last target r3 r4 replacementRoots
      replacementTyped replacementRooted e4 clearFrame clearObserved (fun _ => clearClassified)
  have placeFootprint := result.footprint
  rw [worldEq] at placeFootprint
  exact ⟨child, childTyping, childRoots, childWorld, childObservation,
    childType.trans typeEq.symm, placeFootprint.trans clearFootprint⟩

end Goose.Lower
