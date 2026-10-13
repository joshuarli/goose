import Goose.Core.Sound.Context
import Goose.Core.Sound.Protection
import Goose.Core.Sound.RetainSyntax

/-!
Bridge one checked direct shrink point to its runtime retention obligations.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

theorem Frame.demandedSliceTargets_ne_of_shrinkProtected
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {ownerRoots : List RootRef}
    (frame : Frame m W tenv penv env s future)
    (hProtected : KnownEffectShrinkProtected W)
    (ownerTargets : ∀ target, target ∈ rootsTargets ownerRoots → target ∈ W.E.shrinks)
    (owner : Gam env W.P ownerRoots ownerRoot) :
    ∀ holder elem, W.D holder elem → ∀ target, W.A holder target → target ≠ ownerRoot := by
  intro holder elem hD target hA
  obtain ⟨activation, holderScope, holderVar, hholder, hbeforeBase⟩ :=
    frame.dOut holder elem hD
  have holderAge := frame.aOlder _ target hA
  obtain ⟨ownerRef, hownerRef, hownerRoot⟩ := owner
  cases ownerRef with
  | «local» ownerVar =>
    rcases hownerRoot with ⟨lv, ownerScope, hvar, hlookup, hroot⟩
    obtain ⟨before, after, hscopes, _⟩ := List.lookup_eq_some_iff.mp hlookup
    have hscopeMem : (lv.scope, ownerScope) ∈ env.scopes := by
      rw [hscopes]
      exact List.mem_append_right _ List.mem_cons_self
    have hbase := (frame.below _ hscopeMem).1
    intro hsame
    have hownerOlder : ownerScope ≤ holderScope := by
      rw [hsame, hroot, hholder] at holderAge
      exact (by simpa [Older] using holderAge)
    exact (Nat.not_le_of_gt (Nat.lt_of_lt_of_le hbeforeBase hbase)) hownerOlder
  | global g =>
    have hshrinks : Target.global g ∈ W.E.shrinks :=
      ownerTargets (.global g) (mem_rootsTargets_global hownerRef)
    have hmay : MayShrinkEff W.P W.E (.global g) :=
      ⟨.global g, Or.inl hshrinks, rfl⟩
    have haway := hProtected.2 holder elem target hD hA (.global g) hmay
    intro hsame
    exact haway (hsame.trans hownerRoot)
  | param i =>
    have hshrinks : Target.param i ∈ W.E.shrinks :=
      ownerTargets (.param i) (mem_rootsTargets_param hownerRef)
    have hmay : MayShrinkEff W.P W.E ownerRoot :=
      ⟨.param i, Or.inl hshrinks, hownerRoot⟩
    exact hProtected.2 holder elem target hD hA ownerRoot hmay

theorem locTy_growshrink_root_ne_of_slice
    {m : Module} {G : Nat} {s : Store} {root : RootInst} {path : List Nat}
    {E T : Ty} {v : Val}
    (hroot : s.roots[root]? = some v)
    (hslice : HasTy m G s v (.slice .mutable E))
    (hloc : LocTy s ⟨root, path⟩ (.growshrink T)) : False := by
  rcases hslice with ⟨sliceLoc, start, count, rfl, _, _⟩
  obtain ⟨value, hread, hflat⟩ := hloc
  obtain ⟨storedRoot, hstored, hget⟩ := (read_ok_iff _ _ _).1 hread
  rw [hroot] at hstored
  cases hstored
  cases path with
  | nil =>
    rw [get_nil] at hget
    cases hget
    simp [FlatTy] at hflat
  | cons index rest =>
    simp [Val.get?, Val.children?, Val.elems?] at hget

theorem DemandOwner.conflicts_false_disjoint {owner : DemandOwner}
    {alias : RetainedAlias}
    (hinvalidates : owner.invalidates = true)
    (hinterior : alias.ty.interiorTarget?.isSome = true)
    (hconflicts : owner.conflicts alias = false) :
    DemandRootsDisjoint owner.roots alias.roots := by
  simp [DemandRootsDisjoint, DemandOwner.conflicts, DemandOwner.compatible,
    hinvalidates, hinterior] at hconflicts ⊢
  exact hconflicts

/-- An approved resizable shrink excludes every retained interior alias root. -/
theorem shrinkApproval_retainedInteriorDisjoint
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan} {alias : RetainedAlias}
    {element : Ty}
    (howner : approval.shrinkOwner.ty = some (.growshrink element))
    (hinterior : alias.ty.interiorTarget?.isSome = true)
    (hmem : alias ∈ approval.point.retained) :
    DemandRootsDisjoint approval.shrinkOwner.roots alias.roots := by
  have hinvalidates : approval.shrinkOwner.invalidates = true := by
    simp [DemandOwner.invalidates, howner]
  exact DemandOwner.conflicts_false_disjoint hinvalidates hinterior
    (approval.safe.2 alias hmem)

theorem shrinkApproval_retainedInteriorHeld
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan} {alias : RetainedAlias}
    {element : Ty} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future : List VarId} {o : Loc} {len : Nat} {v : Val}
    (hownerTy : approval.shrinkOwner.ty = some (.growshrink element))
    (hinterior : alias.ty.interiorTarget?.isSome = true)
    (hmem : alias ∈ approval.point.retained)
    (hframe : Frame m W tenv penv env s future)
    (howner : Gam env W.P approval.shrinkOwner.roots o.root)
    (halias : AliasAt m W env s.store alias v) :
    RetainedHeld o len v := by
  have hdisjoint := shrinkApproval_retainedInteriorDisjoint
    hownerTy hinterior hmem
  have hrootNe : ∀ r, Targets v r → r ≠ o.root := by
    intro r htarget
    exact (Gam.root_ne_of_no_overlap hframe hdisjoint howner (halias.2 r htarget)).symm
  cases v with
  | ref l => exact Or.inl (hrootNe l.root rfl)
  | slice l start count => exact ⟨Or.inl (hrootNe l.root rfl), Or.inl (hrootNe l.root rfl)⟩
  | unit => trivial
  | bool _ => trivial
  | int _ _ => trivial
  | fixed _ => trivial
  | resizable _ _ => trivial
  | limited _ _ _ _ => trivial
  | record _ _ => trivial

theorem HasTy.truncate_growshrink {m : Module} {G : Nat} {s s' : Store}
    {o : Loc} {len : Nat} {v : Val} {T : Ty}
    (htruncate : s.truncate o len = .ok s')
    (hLoc : ∀ l U, RetainedLoc o len l → LocOk m G s l U → LocOk m G s' l U)
    (hSlice : ∀ l start count, RetainedLoc o len l →
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len) →
      ∀ E, SliceTy s l start count E → SliceTy s' l start count E)
    (hretained : RetainedHeld o len v)
    (h : HasTy m G s v T) : HasTy m G s' v T := by
  cases T with
  | ref mu target =>
    simp only [HasTy] at h ⊢
    obtain ⟨l, rfl, hloc⟩ := h
    refine ⟨l, rfl, ?_⟩
    rcases hloc with ⟨htarget, hloc, hheader⟩ | ⟨hslice, hpath, hroot⟩
    · change RetainedLoc o len l at hretained
      exact Or.inl ⟨htarget, hLoc l target hretained hloc, hheader⟩
    · change RetainedLoc o len l at hretained
      refine Or.inr ⟨hslice, hpath, ?_⟩
      by_cases hrootOwner : l.root = o.root
      · simpa [hrootOwner] using truncate_root_exists s s' o len htruncate
      · have hagree := truncate_except_owner s s' o len htruncate
        rw [hagree l.root (by simpa using hrootOwner)]
        exact hroot
  | slice mu elem =>
    simp only [HasTy] at h ⊢
    obtain ⟨l, start, count, rfl, hflat, hslice⟩ := h
    change RetainedLoc o len l ∧
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len) at hretained
    exact ⟨l, start, count, rfl, hflat,
      hSlice l start count hretained.1 hretained.2 elem hslice⟩
  | unit => exact h
  | tuple parts => exact h
  | int t => exact h
  | bool => exact h
  | arr elem count => exact h
  | grow elem => exact h
  | growshrink elem => exact h
  | limited elem capacity => exact h
  | structT id fields => exact h

theorem HasTy.slice_truncate_unrelated_root
    {m : Module} {G : Nat} {s s' : Store} {o l : Loc} {len start count : Nat}
    {mu : Mutability} {element : Ty}
    (htruncate : s.truncate o len = .ok s')
    (hroot : l.root ≠ o.root)
    (h : HasTy m G s (.slice l start count) (.slice mu element)) :
    HasTy m G s' (.slice l start count) (.slice mu element) := by
  simp only [HasTy] at h ⊢
  obtain ⟨oldLoc, oldStart, oldCount, heq, hflat, hslice⟩ := h
  cases heq
  obtain ⟨value, elems, hread, helems, hbounds, hkind⟩ := hslice
  have hagree := truncate_except_owner s s' o len htruncate
  have hread' : s'.read l = .ok value := by
    rw [read_ok_iff]
    obtain ⟨old, hrootValue, hget⟩ := (read_ok_iff _ _ _).1 hread
    exact ⟨old, by rw [hagree l.root (by simpa using hroot)]; exact hrootValue, hget⟩
  exact ⟨l, start, count, rfl, hflat,
    value, elems, hread', helems, hbounds, hkind⟩

theorem Frame.truncateGrowshrinkSa
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {state : St}
    {future : List VarId} {ownerRoots : List RootRef}
    {s' : Store} {o : Loc} {len : Nat} {element : Ty}
    (frame : Frame m W tenv penv env state future)
    (hProtected : KnownEffectShrinkProtected W)
    (ownerTargets : ∀ target, target ∈ rootsTargets ownerRoots → target ∈ W.E.shrinks)
    (owner : Gam env W.P ownerRoots o.root)
    (howner : LocTy state.store o (.growshrink element))
    (htruncate : state.store.truncate o len = .ok s') :
    ∀ holder elem, W.D holder elem →
      ∃ v, s'.roots[holder]? = some v ∧ HasTy m W.G s' v (.slice .mutable elem) ∧
        ∀ target, Targets v target → W.A holder target := by
  intro holder elem hD
  obtain ⟨v, hvalue, hhasTy, htargets⟩ := frame.sa holder elem hD
  have hholder_ne : holder ≠ o.root := by
    intro heq
    exact locTy_growshrink_root_ne_of_slice (by simpa [heq] using hvalue) hhasTy howner
  obtain ⟨l, start, count, hv, hflat, hslice⟩ := hhasTy
  have hrootNe : l.root ≠ o.root := by
    intro heq
    have htarget : W.A holder l.root := htargets l.root (by simp [hv, Targets])
    have haway := frame.demandedSliceTargets_ne_of_shrinkProtected
      hProtected ownerTargets owner holder elem hD l.root htarget
    exact haway heq
  have hheld : RetainedHeld o len (.slice l start count) := by
    simp [RetainedHeld, ResizableRetainedHeld, RetainedLoc, ResizableRetainedLoc, hrootNe]
  have hpreTy : HasTy m W.G state.store (.slice l start count) (.slice .mutable elem) :=
    ⟨l, start, count, rfl, hflat, hslice⟩
  have hpostTy : HasTy m W.G s' (.slice l start count) (.slice .mutable elem) :=
    HasTy.slice_truncate_unrelated_root htruncate hrootNe hpreTy
  have hrootPost : s'.roots[holder]? = some (.slice l start count) := by
    rw [truncate_except_owner state.store s' o len htruncate holder hholder_ne]
    simpa [hv] using hvalue
  refine ⟨.slice l start count, hrootPost, hpostTy, ?_⟩
  simpa [hv] using htargets

theorem shrinkApproval_retainsInteriorAlias
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan} {alias : RetainedAlias}
    {element : Ty} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {state : St} {future : List VarId} {s' : Store} {o : Loc} {len : Nat}
    (hownerTy : approval.shrinkOwner.ty = some (.growshrink element))
    (hinterior : alias.ty.interiorTarget?.isSome = true)
    (hmem : alias ∈ approval.point.retained)
    (hframe : Frame m W tenv penv env state future)
    (howner : Gam env W.P approval.shrinkOwner.roots o.root)
    (htruncate : state.store.truncate o len = .ok s')
    (hLoc : ∀ l U, RetainedLoc o len l → LocOk m W.G state.store l U → LocOk m W.G s' l U)
    (hSlice : ∀ l start count, RetainedLoc o len l →
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len) →
      ∀ E, SliceTy state.store l start count E → SliceTy s' l start count E) :
    RetainsAlias m W env state.store s' alias := by
  constructor
  · intro v halias
    have hretained := shrinkApproval_retainedInteriorHeld (len := len)
      hownerTy hinterior hmem hframe howner halias
    exact ⟨HasTy.truncate_growshrink htruncate hLoc hSlice hretained halias.1,
      halias.2⟩
  · intro mu el capacity l start count hty _ _
    simp [hty, Ty.interiorTarget?, Ty.ownerElem?] at hinterior

/- A direct mutation context selects the approval for its exact owner and
frame, so each mutation proof uses the checked request for that source point. -/
theorem NodeContext.directShrinkApproval
    {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat} {node : DemandNode}
    (context : NodeContext planContext path node .mutation)
    {ownerPlace : Place}
    (directPlace : node.directShrinkPlace? = some ownerPlace)
    {owner : DemandOwner}
    (ownerResult : planContext.approvals.access.owner ownerPlace = .ok owner) :
    ∃ approval : DemandShrinkApproval m planContext.owner planContext.plan,
      approval.point.path = path ∧ approval.shrinkOwner = owner ∧
        approval.point.phase = .mutation ∧
          DemandPoint.sameFrameMembership approval.point context.expected.toPoint := by
  have howner : owner ∈ context.expected.shrinkOwners :=
    context.sourceAt.directShrinkOwner rfl directPlace
      planContext.approvals.accessMatches ownerResult
  rcases context.sourceAt with ⟨points, hwalk, hmem, hpath, hnode, hphase⟩
  rcases planContext.approvals.directShrinkAt context.expected context.member hphase
      (by simpa [DemandNode.isDirectShrink, hnode, directPlace]) owner howner with
    ⟨approval, _, hapath, howner, hphase, hframe⟩
  exact ⟨approval, hapath.trans hpath, howner, hphase, hframe⟩

/- A clear mutation context selects the approval for its exact owner and frame. -/
theorem NodeContext.clearApproval
    {m : Module} {plans : Array (Array DemandPoint)}
    {planContext : PlanContext m plans} {path : List Nat}
    {ownerPlace : Place} {origin : OriginId}
    (context : NodeContext planContext path (.statement (.clear ownerPlace origin)) .mutation)
    {owner : DemandOwner}
    (ownerResult : planContext.approvals.access.owner ownerPlace = .ok owner) :
    ∃ approval : DemandShrinkApproval m planContext.owner planContext.plan,
      approval.point.path = path ∧ approval.shrinkOwner = owner ∧
        approval.point.phase = .mutation ∧
          DemandPoint.sameFrameMembership approval.point context.expected.toPoint := by
  exact context.directShrinkApproval (ownerPlace := ownerPlace)
    (by simp [DemandNode.directShrinkPlace?]) ownerResult

end Goose.Core.Sound
