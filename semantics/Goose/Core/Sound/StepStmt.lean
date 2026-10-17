import Goose.Core.Sound.StepAux
import Goose.Core.Sound.RetainSyntax
import Goose.Core.Sound.AccessTyping
import Goose.Core.Sound.AccessReplay
import Goose.Core.Sound.ShrinkBridge
import Goose.Core.Sound.TruncateObservation

/-!
One step of the induction on fuel for the statements that bind, write, rebind
and grow.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

private noncomputable def statementExprChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (e : Expr)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.expression e)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.expression e) .expression :=
  ec.child rfl index (DemandNode.expression e) .expression hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementPlaceChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (p : Place)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.place p)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.place p) .place :=
  ec.child rfl index (DemandNode.place p) .place hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementViewChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (v : View)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.view v)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.view v) .view :=
  ec.child rfl index (DemandNode.view v) .view hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementBlockChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (b : Block)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.block b)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.block b) .block :=
  ec.child rfl index (DemandNode.block b) .block hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementMutationContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (hphase : DemandNodeHasPhase (DemandNode.statement st) .mutation) :
    EvaluationContext m plans path (DemandNode.statement st) .mutation :=
  ec.phase rfl .mutation hphase

/- A statement's checked direct owner request supplies the plan half of
   shrink authority for the exact runtime owner. -/
theorem EvaluationContext.directShrinkMayShrink
    {plans : Array (Array DemandPoint)} {path : List Nat} {st : Stmt}
    {pc : PlanContext m plans} {ownerPlace : Place} {owner : DemandOwner}
    {root : RootInst} {observation : Observation} {W : World}
    (profile : m.profile = .shrink)
    (context : NodeContext pc path (.statement st) .mutation)
    (directPlace : (DemandNode.statement st).directShrinkPlace? = some ownerPlace)
    (ownerResult : pc.approvals.access.owner ownerPlace = .ok owner)
    (hexternal : owner.denotesExternalShrink W.ownerP root)
    (hcap : OwnerCap m observation root) :
    ∃ approval : DemandShrinkApproval m pc.owner pc.plan,
      approval.point.path = path ∧ approval.shrinkOwner = owner ∧
        approval.point.phase = .mutation ∧
          DemandPoint.sameFrameMembership approval.point context.expected.toPoint ∧
          (EvaluationContext.shrink profile context).mayShrink W.ownerP observation root := by
  obtain ⟨approval, hpath, howner, hphase, hframe⟩ :=
    context.directShrinkApproval directPlace ownerResult
  have hownerMem : owner ∈ context.expected.shrinkOwners :=
    context.sourceAt.directShrinkOwner rfl directPlace
      pc.approvals.accessMatches ownerResult
  rcases context.sourceAt with ⟨points, hwalk, hmem, hpathExpected, hnode, hphaseExpected⟩
  have hplan : PlanMayShrink pc W.ownerP root :=
    PlanMayShrink.ofExpected context.member hphaseExpected hownerMem hexternal
  exact ⟨approval, hpath, howner, hphase, hframe, ⟨hplan, hcap⟩⟩

private theorem statementOwnerRefTyOfPassable {source target : Ty}
    (passable : source.passableTo target = true) (owner : OwnerRefTy target) :
    OwnerRefTy source := by
  rcases owner with ⟨mu, element, rfl | rfl⟩ <;>
    cases source <;> simp [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passable
  all_goals
    rcases passable with ⟨rfl, _⟩
    first | exact ⟨_, _, Or.inl rfl⟩ | exact ⟨_, _, Or.inr rfl⟩

private theorem statementEffectMutationRoot {W : World} {tenv : TEnv}
    {penv : PEnv} {env : Env} {s : St} {future : List VarId} {roots : List RootRef}
    {root : RootInst} {effect : Eff}
    (frame : Frame m W tenv penv env s future) (denotes : Gam env W.P roots root)
    (targets : ∀ target, target ∈ rootsTargets roots →
      target ∈ effectMutationTargets effect) :
    MutationRoots env W.P W.base (effectMutationRoots m penv.impl effect) root := by
  obtain ⟨reference, hreference, hroot⟩ := denotes
  cases reference with
  | «local» x =>
    rcases hroot with ⟨lv, scope, hvar, hlookup, rfl⟩
    exact Or.inr ⟨env.act, scope, x, rfl, (frame.inst_lt hlookup).1⟩
  | global g =>
    apply Or.inl
    refine ⟨.global g, ?_, hroot⟩
    have htarget := targets (.global g) (mem_rootsTargets_global hreference)
    have hknown : RootRef.global g ∈ effectTargetRoots (effectMutationTargets effect) :=
      List.mem_map.mpr ⟨.global g, htarget, rfl⟩
    simp only [effectMutationRoots]
    split <;> simp_all
  | param i =>
    apply Or.inl
    refine ⟨.param i, ?_, hroot⟩
    have htarget := targets (.param i) (mem_rootsTargets_param hreference)
    have hknown : RootRef.param i ∈ effectTargetRoots (effectMutationTargets effect) :=
      List.mem_map.mpr ⟨.param i, htarget, rfl⟩
    simp only [effectMutationRoots]
    split <;> simp_all

private theorem statementSingleRootMutation {W : World} {env : Env} {s s' : St}
    {roots : List RootRef} {root : RootInst}
    (agreement : StoreLeExcept (fun r => r = root) s.store s'.store)
    (changed : MutationRoots env W.P W.base roots root) :
    MutationFootprint env W.P W.base roots s s' := by
  intro r outside
  apply agreement r
  intro heq
  subst r
  exact outside changed

private theorem statementPlaceForbiddenDisjoint {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt} {tenv : TEnv} {penv : PEnv} {index : Nat}
    {place : Place} {rst rst' : RState} {roots : List RootRef}
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (access : ec.AccessMatches tenv penv)
    (child : (DemandNode.statement st).child? index = some (.place place))
    (replayed : rpPlace penv place rst = .ok (roots, rst')) :
    ∀ owner, owner ∈ ec.forbiddenOwners → DemandRootsDisjoint owner.roots roots := by
  cases ec with
  | pilot profile active => simp [EvaluationContext.forbiddenOwners]
  | @shrink pc profile context =>
    intro owner howner
    let transition := context.child rfl index (.place place) .place child (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchildOwner := transition.forbiddenSubset owner howner
    obtain ⟨checkedRoots, checked, disjoint⟩ :=
      transition.context.placeWholeRootsChecked owner hchildOwner
    have accessEq : pc.approvals.access = penv.access := by
      have hAccessMod := access.2.2.1
      have hAccessImpl := access.2.2.2.1
      have hAccessCtx := access.2.2.2.2
      cases hAccessValue : pc.approvals.access
      rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
      unfold PEnv.access
      congr 1
    rw [accessEq] at checked
    have included := rpPlace_accessRoots penv place rst roots rst' checkedRoots replayed checked
    intro forbiddenRoot hforbiddenRoot checkedRoot hcheckedRoot
    exact disjoint forbiddenRoot hforbiddenRoot checkedRoot (included checkedRoot hcheckedRoot)

private theorem statementPlaceForbiddenStaticDisjoint {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt} {tenv : TEnv} {penv : PEnv} {index : Nat}
    {place : Place} {roots : List RootRef}
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (access : ec.AccessMatches tenv penv)
    (child : (DemandNode.statement st).child? index = some (.place place))
    (checked : penv.access.placeRoots place = .ok roots) :
    ∀ owner, owner ∈ ec.forbiddenOwners → DemandRootsDisjoint owner.roots roots := by
  cases ec with
  | pilot profile active => simp [EvaluationContext.forbiddenOwners]
  | @shrink pc profile context =>
    intro owner howner
    let transition := context.child rfl index (.place place) .place child (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches])
    have hchildOwner := transition.forbiddenSubset owner howner
    obtain ⟨checkedRoots, hchecked, hdisjoint⟩ :=
      transition.context.placeWholeRootsChecked owner hchildOwner
    have accessEq : pc.approvals.access = penv.access := by
      have hAccessMod := access.2.2.1
      have hAccessImpl := access.2.2.2.1
      have hAccessCtx := access.2.2.2.2
      cases hAccessValue : pc.approvals.access
      rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
      unfold PEnv.access
      congr 1
    rw [accessEq] at hchecked
    rw [checked] at hchecked
    cases hchecked
    exact hdisjoint

private theorem statementStoreForbidden {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s s' : St} {future : List VarId} {roots : List RootRef}
    {root : RootInst} {forbidden : List DemandOwner}
    (frame : Frame m W tenv penv env s future)
    (denotes : Gam env W.P roots root)
    (disjoint : ∀ owner, owner ∈ forbidden → DemandRootsDisjoint owner.roots roots)
    (agreement : StoreLeExcept (fun r => r = root) s.store s'.store) :
    PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
      forbidden s s' := by
  intro owner howner r hsource
  rcases hsource with ⟨element, elements, htype, hdenotes, hvalue⟩
  exact agreement r (Gam.root_ne_of_no_overlap frame (disjoint owner howner) hdenotes denotes)

private theorem statementIntroduceForbidden {W : World} {env : Env} {s : St}
    {forbidden : List DemandOwner} {root : RootInst} {value : Val}
    (free : s.store.roots[root]? = none) :
    PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
      forbidden s { s with store := s.store.introduce root value } := by
  intro owner howner r hsource
  rcases hsource with ⟨element, elements, htype, hdenotes, hvalue⟩
  have hne : root ≠ r := by
    intro heq
    subst r
    rw [free] at hvalue
    cases hvalue
  simp [Store.introduce, Std.HashMap.getElem?_insert, hne]

private theorem statementRebindForbidden {W : World} {env : Env} {s : St}
    {forbidden : List DemandOwner} {root : RootInst} {old value : Val}
    (present : s.store.roots[root]? = some old) (reference : IsRef old) :
    PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
      forbidden s { s with store := ⟨(s.store.roots.erase root).insert root value⟩ } := by
  intro owner howner r hsource
  rcases hsource with ⟨element, elements, htype, hdenotes, hvalue⟩
  have hne : root ≠ r := by
    intro heq
    subst r
    rw [present] at hvalue
    cases hvalue
    cases reference
  simp [get_reinsert, hne]
/- The variable alias and its frame annotation use the same root list, so a
   checked conflict-free alias cannot point into the selected owner root. -/
theorem DemandShrinkApproval.variableTarget_ne
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {o : Loc}
    {x : VarId} {lv : LocalVar} {si : ScopeInst} {v : Val}
    (frame : Frame m W tenv penv env s future)
    (accessEq : approval.access = penv.access)
    (ownerInvalidates : approval.shrinkOwner.invalidates = true)
    (ownerRoot : Gam env W.P approval.shrinkOwner.roots o.root)
    (needed : x ∈ approval.point.future) (active : x ∈ approval.point.active)
    (variableAt : env.vars[x]? = some lv)
    (scope : env.scopes.lookup lv.scope = some si)
    (present : s.store.roots[RootInst.local env.act si x]? = some v)
    (notSliceRef : lv.ty.isRefSlice = false)
    (interior : lv.ty.interiorTarget?.isSome = true) :
    ∀ target, Targets v target → target ≠ o.root := by
  intro target targeted
  obtain ⟨annotation, annotationAt, targetIn⟩ :=
    frame.rooted x lv si v variableAt scope present target targeted
  have variableP : penv.impl.vars[x]? = some lv := by
    rw [frame.vars_p]
    exact variableAt
  have annotationCtx : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some annotation := by
    simpa [PEnv.ann] using annotationAt
  let alias : RetainedAlias := ⟨lv.ty, annotation, .variable x⟩
  have aliasLookup : approval.access.aliasVariable x = .ok (some alias) := by
    rw [accessEq]
    simp [AccessEnv.aliasVariable, PEnv.access, variableP, notSliceRef,
      interior, AccessEnv.variableRoots, annotationCtx, alias]
    rfl
  have aliasInterior : alias.ty.interiorTarget?.isSome = true := by
    simpa [alias] using interior
  have disjoint := DemandOwner.conflicts_false_disjoint ownerInvalidates aliasInterior
    (approval.safe.1.1 x needed active alias aliasLookup)
  exact (Gam.root_ne_of_no_overlap frame disjoint ownerRoot targetIn).symm

/- A reference to a slice variable points at its header, while the checked
   alias describes the slice contents. The frame's PRef relation connects
   that header to a demanded slice holder. -/
theorem Frame.refSliceHeader_ne_of_shrinkApproval
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {o : Loc} {element : Ty}
    {x : VarId} {lv : LocalVar} {si : ScopeInst} {mu mu' : Mutability} {sliceElement : Ty}
    {l : Loc}
    (frame : Frame m W tenv penv env s future)
    (accessEq : approval.access = penv.access)
    (needed : x ∈ approval.point.future) (active : x ∈ approval.point.active)
    (variableAt : env.vars[x]? = some lv)
    (scope : env.scopes.lookup lv.scope = some si)
    (present : s.store.roots[RootInst.local env.act si x]? = some (.ref l))
    (typeEq : lv.ty = .ref mu (.slice mu' sliceElement))
    (sliceFlat : sliceElement.flat = true)
    (ownerLoc : LocTy s.store o (.growshrink element)) :
    l.root ≠ o.root := by
  have variableP : penv.impl.vars[x]? = some lv := by
    rw [frame.vars_p]
    exact variableAt
  obtain ⟨aliases, hlookup⟩ :=
    DemandPointShrinkSafe.aliasVariable_succeeds approval.safe needed active
  rw [accessEq] at hlookup
  have content : ∃ roots, penv.cont x = some roots := by
    cases hcontent : penv.cont x with
    | some roots => exact ⟨roots, rfl⟩
    | none =>
      have contentCtx :
          (penv.ctx.contentRoots.find? (·.1 == x)).map (·.2) = none := by
        simpa [PEnv.cont] using hcontent
      have impossible : False := by
        rw [PEnv.access] at hlookup
        simp only [AccessEnv.aliasVariable, variableP, typeEq,
          Ty.isRefSlice, sliceFlat, if_pos] at hlookup
        simp [AccessEnv.contentRoots, contentCtx, Except.map, reject] at hlookup
        cases hlookup
      exact impossible.elim
  obtain ⟨roots, contentAt⟩ := content
  have pref := frame.pref x roots contentAt
  have annotationAt : penv.ann x = some [.param x] := pref.2.1
  obtain ⟨annotation, annotationFound, targetIn⟩ :=
    frame.rooted x lv si (.ref l) variableAt scope present l.root rfl
  rw [annotationAt] at annotationFound
  cases annotationFound
  have parameterTarget : W.P x l.root := by
    obtain ⟨root, member, denotes⟩ := targetIn
    simp only [List.mem_singleton] at member
    cases member
    exact denotes
  have holderDemand : W.D l.root sliceElement :=
    (pref.2.2 lv mu mu' sliceElement variableAt typeEq l.root parameterTarget).1
  have holderSlice := frame.sa l.root sliceElement holderDemand
  intro same
  obtain ⟨value, rootPresent, sliceTy, _⟩ := holderSlice
  exact locTy_growshrink_root_ne_of_slice (by simpa [same] using rootPresent)
    sliceTy ownerLoc

/- Typed locals outside the changed holder keep their type across truncation.
   Interior aliases use the exact mutation approval; owner-header references
   use preservation of whole-root types. -/
private theorem Frame.localHasTy_afterGrowshrinkTruncate
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {o : Loc} {len : Nat} {element : Ty} {ownerType : Ty}
    {x : VarId} {lv : LocalVar} {si : ScopeInst} {v : Val} {s' : Store}
    (frame : Frame m W tenv penv env s future)
    (accessEq : approval.access = penv.access)
    (ownerTy : approval.shrinkOwner.ty = some ownerType)
    (resizable : ownerType = .grow element ∨ ownerType = .growshrink element)
    (ownerRoot : Gam env W.P approval.shrinkOwner.roots o.root)
    (ownerLoc : LocTy s.store o ownerType)
    (needed : x ∈ approval.point.future) (active : x ∈ approval.point.active)
    (variableAt : env.vars[x]? = some lv)
    (scope : env.scopes.lookup lv.scope = some si)
    (present : s.store.roots[RootInst.local env.act si x]? = some v)
    (typed : HasTy m W.G s.store v lv.ty)
    (htruncate : s.store.truncate o len = .ok s') :
    HasTy m W.G s' v lv.ty := by
  have ownerLocGrowshrink : LocTy s.store o (.growshrink element) := by
    rcases resizable with hgrow | hshrink
    · cases hgrow
      exact ownerLoc.grow_to_growshrink
    · cases hshrink
      exact ownerLoc
  have ownerInvalidates : approval.shrinkOwner.invalidates = true := by
    simp only [DemandOwner.invalidates]
    rw [ownerTy]
    rcases resizable with hgrow | hshrink
    · rw [hgrow]
    · rw [hshrink]
  have rootTyLe : RootTyLe s.store s' :=
    truncate_growshrink_rootTyLe s.store s' o len element ownerLocGrowshrink htruncate
  have hagree := truncate_except_owner s.store s' o len htruncate
  have preserveNonref {T : Ty} (h : HasTy m W.G s.store v T)
      (hnonref : T.isRefLike = false) : HasTy m W.G s' v T := by
    exact HasTy.agree (P := fun root => root = o.root) hagree
      (by
        intro target targeted
        exact False.elim ((h.not_ref hnonref) (Targets.isRef targeted))) h
  cases htype : lv.ty with
  | ref mu target =>
    have typedRef : HasTy m W.G s.store v (.ref mu target) := by
      simpa [htype] using typed
    cases target with
    | grow _ | growshrink _ | limited _ _ =>
      cases v with
      | ref l => exact HasTy.owner_mono rootTyLe (by simp [Ty.ownerElem?]) typedRef
      | _ => simp [HasTy, Ty.isSlice] at typedRef
    | slice mu' sliceElement =>
      cases v with
      | ref l =>
        have sliceFlat : sliceElement.flat = true := by
          have typedShape := typedRef
          simp only [HasTy] at typedShape
          rcases typedShape with ⟨_, _, hshape⟩
          rcases hshape with ⟨href, _, _⟩ | ⟨hslice, _, _⟩
          · simp [Ty.refTarget] at href
          · simpa [Ty.isSlice] using hslice
        have rootAway := Frame.refSliceHeader_ne_of_shrinkApproval frame accessEq
          needed active variableAt scope present htype sliceFlat ownerLocGrowshrink
        exact HasTy.agree (P := fun root => root = o.root) hagree (by
          intro target targeted
          change l.root = target at targeted
          subst target
          exact rootAway) typedRef
      | _ => simp [HasTy, Ty.refTarget, Ty.isSlice] at typedRef
    | int _ | bool | arr _ _ | structT _ _ =>
      cases v with
      | ref l =>
        have notSliceRef : lv.ty.isRefSlice = false := by simp [htype, Ty.isRefSlice]
        have interior : lv.ty.interiorTarget?.isSome = true := by
          simp [htype, Ty.interiorTarget?, Ty.ownerElem?]
        have rootAway := DemandShrinkApproval.variableTarget_ne frame accessEq
          ownerInvalidates ownerRoot needed active variableAt scope present notSliceRef interior
        exact HasTy.agree hagree rootAway typedRef
      | _ => simp [HasTy, Ty.refTarget, Ty.isSlice] at typedRef
    | unit | tuple _ | ref _ _ => simp [HasTy, Ty.refTarget, Ty.isSlice] at typedRef
  | slice mu elem =>
    have typedSlice : HasTy m W.G s.store v (.slice mu elem) := by
      simpa [htype] using typed
    cases v with
    | slice l start count =>
      have notSliceRef : lv.ty.isRefSlice = false := by simp [htype, Ty.isRefSlice]
      have interior : lv.ty.interiorTarget?.isSome = true := by simp [htype, Ty.interiorTarget?]
      have rootAway := DemandShrinkApproval.variableTarget_ne frame accessEq
        ownerInvalidates ownerRoot needed active variableAt scope present notSliceRef interior
      exact HasTy.agree hagree rootAway typedSlice
    | _ => simp [HasTy] at typedSlice
  | unit => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | tuple _ =>
    have impossible : False := by simpa [htype, HasTy] using typed
    exact impossible.elim
  | int _ => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | bool => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | arr _ _ => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | grow _ => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | growshrink _ => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | limited _ _ => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
  | structT _ _ => exact preserveNonref (by simpa [htype] using typed) (by simp [Ty.isRefLike])
private theorem statementBindAssoc {α β γ : Type} (x : M α) (f : α → M β) (g : β → M γ) :
    ((x >>= f) >>= g) = x >>= fun a => f a >>= g := by
  funext s
  show M.bind' (M.bind' x f) g s = M.bind' x (fun a => M.bind' (f a) g) s
  unfold M.bind'
  cases x s <;> rfl

private theorem statementChildFacts {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (child : DemandNode) (childPhase : DemandPhase)
    (hchild : (DemandNode.statement st).child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase)
    (hactive : ec.ActiveMatches tenv) (haccessChild : ec.AccessMatches tenv' penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hF : Frame m W tenv' penv env s ec.inputFuture)
    (hvisible : ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (hinput : ∀ x,
      x ∈ (ec.child rfl index child childPhase hchild hchildPhase).inputFuture →
      x ∈ ec.inputFuture) :
    (ec.child rfl index child childPhase hchild hchildPhase).ActiveMatches tenv' ∧
    (ec.child rfl index child childPhase hchild hchildPhase).AccessMatches tenv' penv ∧
    ShrinkProtected W.D W.A
      ((ec.child rfl index child childPhase hchild hchildPhase).mayShrink W.ownerP observation) ∧
    ObservedSafe m W
      ((ec.child rfl index child childPhase hchild hchildPhase).mayShrink W.ownerP observation)
      observation s.store ∧
    Frame m W tenv' penv env s
      (ec.child rfl index child childPhase hchild hchildPhase).inputFuture ∧
    (∀ alias, alias ∈ ec.retained →
      alias ∈ (ec.child rfl index child childPhase hchild hchildPhase).retained) := by
  have hmay root := ec.child_mayShrink_iff rfl index child childPhase hchild hchildPhase
    W.ownerP observation root
  refine ⟨ec.child_activeMatches rfl index child childPhase hchild hchildPhase tenv tenv'
      hactive hvisible,
    (ec.child_accessMatches_iff rfl index child childPhase hchild hchildPhase tenv' penv).2
      haccessChild,
    hprotected.mono (fun _ _ h => h) (fun _ _ h => h)
      (fun root h => (hmay root).1 h),
    hobserved.weakenShrinking (fun root h => (hmay root).1 h),
    hF.narrowFuture hinput,
    ?_⟩
  intro alias hmem
  exact ec.child_retained_subset rfl index child childPhase hchild hchildPhase hmem

private theorem statementShrinkChildNewAlias {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt} {pc : PlanContext m plans}
    (profile : m.profile = .shrink)
    (context : NodeContext pc path (DemandNode.statement st) .statement)
    (index : Nat) (child : DemandNode) (childPhase : DemandPhase)
    (hchild : (DemandNode.statement st).child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase)
    (aliases : List RetainedAlias) (alias : RetainedAlias)
    (haliases : (DemandNode.statement st).retainedForChild pc.approvals.access path index =
      .ok aliases)
    (hmem : alias ∈ aliases) :
    List.Mem alias (((EvaluationContext.shrink profile context).child rfl index child childPhase
      hchild hchildPhase).retained) := by
  let transition := context.child rfl index child childPhase hchild hchildPhase
  have hchildFrame := DemandNode.childFrame_newAlias transition.childFrameEq haliases hmem
  have hphaseFrame := DemandNode.phaseFrame_retains transition.phaseFrameEq hchildFrame
  change List.Mem alias transition.context.expected.frame.retained
  rw [transition.expectedFrameEq]
  exact hphaseFrame

private theorem statementIntroducePreservation {W : World} {env : Env} {s : St}
    {observation : Observation} {shrinking : RootInst → Prop} {aliases : List RetainedAlias}
    {root : RootInst} {value : Val}
    (hsafe : ObservedSafe m W shrinking observation s.store)
    (hfree : s.store.roots[root]? = none) :
    PreservesRootTypes m W.G observation.roots s.store (s.store.introduce root value) ∧
    PreservesValues m W.G observation.values s.store (s.store.introduce root value) ∧
    ObservedSafe m W shrinking observation (s.store.introduce root value) ∧
    RetainsAliases m W env s.store (s.store.introduce root value) aliases ∧
    PilotStoreLe m s { s with store := s.store.introduce root value } := by
  have hle := introduce_le s.store root value hfree
  have hroots : PreservesRootTypes m W.G observation.roots s.store
      (s.store.introduce root value) := by
    intro r T hr old hold hty
    by_cases heq : root = r
    · subst r
      rw [hfree] at hold
      cases hold
    · refine ⟨old, ?_, HasTy.mono hle hty⟩
      simpa [Store.introduce, Std.HashMap.getElem?_insert, heq] using hold
  have hvalues : PreservesValues m W.G observation.values s.store
      (s.store.introduce root value) := by
    intro v T hv hty
    exact HasTy.mono hle hty
  have hsafe' : ObservedSafe m W shrinking observation (s.store.introduce root value) := by
    refine ⟨hsafe.typed.advance hroots hvalues, hsafe.rootsOlder, hsafe.valuesOlder, ?_,
      hsafe.valuesProtected, hsafe.holderTypes⟩
    intro r T old hr hnew hi target ht
    have hnotObserved : ¬ observation.roots root T := by
      intro hobs
      obtain ⟨v, hv, _⟩ := hsafe.typed.roots root T hobs
      rw [hfree] at hv
      cases hv
    by_cases heq : root = r
    · subst r
      exact False.elim (hnotObserved hr)
    · have hold : s.store.roots[r]? = some old := by
        simpa [Store.introduce, Std.HashMap.getElem?_insert, heq] using hnew
      exact hsafe.rootsProtected r T old hr hold hi target ht
  have hretains : RetainsAliases m W env s.store (s.store.introduce root value) aliases := by
    intro alias hmem
    constructor
    · intro v ⟨hty, hgam⟩
      exact ⟨HasTy.mono hle hty, hgam⟩
    · intro mu el capacity l start len hty halias hslice
      exact SliceTy.mono hle hslice
  exact ⟨hroots, hvalues, hsafe', hretains, fun _ => hle⟩

private theorem statementStorePreservation {W : World} {env : Env} {s s' : St}
    {observation : Observation} {shrinking : RootInst → Prop} {aliases : List RetainedAlias}
    (hsafe : ObservedSafe m W shrinking observation s.store)
    (hle : StoreLe s.store s'.store)
    (hsame : ∀ r T, observation.roots r T → ∀ v,
      (s.store.roots[r]? = some v ↔ s'.store.roots[r]? = some v)) :
    PreservesRootTypes m W.G observation.roots s.store s'.store ∧
    PreservesValues m W.G observation.values s.store s'.store ∧
    ObservedSafe m W shrinking observation s'.store ∧
    RetainsAliases m W env s.store s'.store aliases ∧
    PilotStoreLe m s s' := by
  have hroots : PreservesRootTypes m W.G observation.roots s.store s'.store := by
    intro r T hr old hold hty
    exact ⟨old, (hsame r T hr old).1 hold, HasTy.mono hle hty⟩
  have hvalues : PreservesValues m W.G observation.values s.store s'.store := by
    intro v T hv hty
    exact HasTy.mono hle hty
  have hsafe' : ObservedSafe m W shrinking observation s'.store := by
    refine ⟨hsafe.typed.advance hroots hvalues, hsafe.rootsOlder, hsafe.valuesOlder, ?_,
      hsafe.valuesProtected, hsafe.holderTypes⟩
    intro r T v hr hnew hi target ht
    exact hsafe.rootsProtected r T v hr ((hsame r T hr v).2 hnew) hi target ht
  have hretains : RetainsAliases m W env s.store s'.store aliases := by
    intro alias hmem
    constructor
    · intro v ⟨hty, hgam⟩
      exact ⟨HasTy.mono hle hty, hgam⟩
    · intro mu el capacity l start len hty halias hslice
      exact SliceTy.mono hle hslice
  exact ⟨hroots, hvalues, hsafe', hretains, fun hprofile => hle⟩

private theorem statementHasTyInteriorIsRef {m : Module} {G : Nat} {store : Store}
    {v : Val} {T : Ty} (typed : HasTy m G store v T)
    (interior : T.interiorTarget?.isSome = true) : IsRef v := by
  cases T <;> simp only [Ty.interiorTarget?] at interior
  case ref mu target =>
    obtain ⟨location, rfl, _⟩ := typed
    trivial
  case slice mu element =>
    obtain ⟨location, start, count, rfl, _⟩ := typed
    trivial
  all_goals cases interior

private theorem sat_lengthLoc_owner {l : Loc} {owner element : Ty} {Q : Nat → St → Prop}
    (hl : LocTy s.store l owner) (howner : owner.ownerElem? = some element)
    (k : ∀ len, s.store.length l = .ok len → Q len s) :
    Sat (lengthLoc l) s Q := by
  obtain ⟨v, hread, hflat⟩ := hl
  cases owner with
  | grow el =>
    simp only [Ty.ownerElem?, Option.some.injEq] at howner
    subst element
    cases v <;> simp only [FlatTy] at hflat
    obtain ⟨rfl, _⟩ := hflat
    simp only [Sat, lengthLoc, Store.length, hread]
    exact k _ (by simp [Store.length, hread])
  | growshrink el =>
    simp only [Ty.ownerElem?, Option.some.injEq] at howner
    subst element
    cases v <;> simp only [FlatTy] at hflat
    obtain ⟨rfl, _⟩ := hflat
    simp only [Sat, lengthLoc, Store.length, hread]
    exact k _ (by simp [Store.length, hread])
  | limited el capacity =>
    simp only [Ty.ownerElem?, Option.some.injEq] at howner
    subst element
    cases v <;> simp only [FlatTy] at hflat
    obtain ⟨rfl, rfl, _, _, _⟩ := hflat
    simp only [Sat, lengthLoc, Store.length, hread]
    exact k _ (by simp [Store.length, hread])
  | int _ => simp [Ty.ownerElem?] at howner
  | bool => simp [Ty.ownerElem?] at howner
  | unit => simp [Ty.ownerElem?] at howner
  | arr _ _ => simp [Ty.ownerElem?] at howner
  | ref _ _ => simp [Ty.ownerElem?] at howner
  | slice _ _ => simp [Ty.ownerElem?] at howner
  | tuple _ => simp [Ty.ownerElem?] at howner
  | structT _ _ => simp [Ty.ownerElem?] at howner

private theorem statementLimitedTruncateFlatStep
    {source : Store} {l : Loc} {element : Ty} {capacity currentLen newLen : Nat}
    (hloc : LocTy source l (.limited element capacity))
    (hlen : source.length l = .ok currentLen) (hshort : newLen < currentLen) :
    ∃ destination,
      source.truncate l newLen = .ok destination ∧
      FlatStep source destination ∧ LocTy destination l (.limited element capacity) := by
  obtain ⟨value, hread, hflat⟩ := hloc
  cases value with
  | limited storedElement storedCapacity slots oldLen =>
    simp only [FlatTy] at hflat
    rcases hflat with ⟨rfl, rfl, hcapacity, hcapacityBound, hslots⟩
    have hcurrent : oldLen = currentLen := by
      have h := hlen.symm
      simpa [Store.length, hread] using h.symm
    have hnewBound : newLen ≤ oldLen := by omega
    have htruncateValue :
        Val.truncate newLen (.limited element capacity slots oldLen) =
          some (.limited element capacity slots newLen) := by
      simp [Val.truncate, hnewBound]
    obtain ⟨destination, hmodify⟩ := modify_total source l (Val.truncate newLen)
      (.limited element capacity slots oldLen) (.limited element capacity slots newLen)
      hread htruncateValue
    have htruncate : source.truncate l newLen = .ok destination := by
      simpa [Store.truncate] using hmodify
    have hstep : FlatStep source destination := by
      apply flatStep_modify source destination l (Val.truncate newLen)
        (.limited element capacity slots oldLen) hmodify hread (by simp [IsRef])
      intro next hnext
      rw [htruncateValue] at hnext
      cases hnext
      exact ⟨by simp [IsRef],
        refines_limitedTruncate element capacity slots oldLen newLen hnewBound⟩
    have hlocOriginal : LocTy source l (.limited element capacity) :=
      ⟨.limited element capacity slots oldLen, hread,
        ⟨rfl, rfl, hcapacity, hcapacityBound, hslots⟩⟩
    obtain ⟨_, _, _, _, _, hlocPost⟩ :=
      truncate_limited_shape source destination l newLen element capacity hlocOriginal htruncate
    exact ⟨destination, htruncate, hstep, hlocPost⟩
  | _ => simp [FlatTy] at hflat

/- A checked statement mutation protects demanded slice targets at its exact
   owner root, which is enough to preserve the slices across this truncation. -/
private theorem Frame.truncateGrowshrinkSa_of_mayShrink
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {state : St}
    {future : List VarId} {shrinking : RootInst → Prop}
    {s' : Store} {o : Loc} {len : Nat} {element : Ty}
    (frame : Frame m W tenv penv env state future)
    (hprotected : ShrinkProtected W.D W.A shrinking)
    (hmay : shrinking o.root)
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
    exact (hprotected holder elem l.root hD htarget o.root hmay) heq
  have hheld : RetainedHeld o len (.slice l start count) := by
    change RetainedLoc o len l ∧
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len)
    exact ⟨Or.inl hrootNe, Or.inl hrootNe⟩
  have hpreTy : HasTy m W.G state.store (.slice l start count) (.slice .mutable elem) :=
    ⟨l, start, count, rfl, hflat, hslice⟩
  have hpostTy : HasTy m W.G s' (.slice l start count) (.slice .mutable elem) :=
    HasTy.slice_truncate_unrelated_root htruncate hrootNe hpreTy
  have hrootPost : s'.roots[holder]? = some (.slice l start count) := by
    rw [truncate_except_owner state.store s' o len htruncate holder hholder_ne]
    simpa [hv] using hvalue
  refine ⟨.slice l start count, hrootPost, hpostTy, ?_⟩
  simpa [hv] using htargets

private theorem Frame.truncateGrowshrinkSa_of_localOwner
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {state : St}
    {future : List VarId} {ownerVar : VarId}
    {s' : Store} {o : Loc} {len : Nat} {element : Ty}
    (frame : Frame m W tenv penv env state future)
    (hownerRoot : RootIn env W.P o.root (.local ownerVar))
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
    obtain ⟨lv, ownerScope, hvar, hlookup, hroot⟩ := hownerRoot
    obtain ⟨activation, holderScope, holderVar, hholder, hbeforeBase⟩ := frame.dOut holder elem hD
    have holderAge := frame.aOlder holder l.root htarget
    rw [heq, hroot, hholder] at holderAge
    have hownerOlder : ownerScope ≤ holderScope := by
      simpa [Older] using holderAge
    obtain ⟨before, after, hscopes, _⟩ := List.lookup_eq_some_iff.mp hlookup
    have hscopeMem : (lv.scope, ownerScope) ∈ env.scopes := by
      rw [hscopes]
      exact List.mem_append_right _ List.mem_cons_self
    have hbase := (frame.below _ hscopeMem).1
    exact (Nat.not_le_of_gt (Nat.lt_of_lt_of_le hbeforeBase hbase)) hownerOlder
  have hheld : RetainedHeld o len (.slice l start count) := by
    change RetainedLoc o len l ∧
      (l.root ≠ o.root ∨ l.path ≠ o.path ∨ start + count ≤ len)
    exact ⟨Or.inl hrootNe, Or.inl hrootNe⟩
  have hpreTy : HasTy m W.G state.store (.slice l start count) (.slice .mutable elem) :=
    ⟨l, start, count, rfl, hflat, hslice⟩
  have hpostTy : HasTy m W.G s' (.slice l start count) (.slice .mutable elem) :=
    HasTy.slice_truncate_unrelated_root htruncate hrootNe hpreTy
  have hrootPost : s'.roots[holder]? = some (.slice l start count) := by
    rw [truncate_except_owner state.store s' o len htruncate holder hholder_ne]
    simpa [hv] using hvalue
  refine ⟨.slice l start count, hrootPost, hpostTy, ?_⟩
  simpa [hv] using htargets

/- Exact checked aliases preserve demanded locals, while whole-root typing
   preserves storage headers changed by truncation. -/
theorem Frame.truncateGrowshrinkPreservation
    {m : Module} {owner : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m owner plan}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {state : St}
    {future : List VarId} {shrinking : RootInst → Prop}
    {s' : Store} {o : Loc} {len : Nat} {element ownerType : Ty}
    (frame : Frame m W tenv penv env state future)
    (accessEq : approval.access = penv.access)
    (ownerTy : approval.shrinkOwner.ty = some ownerType)
    (resizable : ownerType = .grow element ∨ ownerType = .growshrink element)
    (ownerRoot : Gam env W.P approval.shrinkOwner.roots o.root)
    (ownerLoc : LocTy state.store o ownerType)
    (visibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active)
    (futureNeeded : ∀ x, x ∈ future → x ∈ approval.point.future)
    (profile : m.profile = .shrink)
    (hprotected : ShrinkProtected W.D W.A shrinking)
    (authority : shrinking o.root ∨
      ∃ a si x, o.root = .local a si x ∧ W.base ≤ si)
    (htruncate : state.store.truncate o len = .ok s') :
    Frame m W tenv penv env { state with store := s' } future ∧
      Footprint (insts env) (Dset W) state { state with store := s' } ∧
      PilotStoreLe m state { state with store := s' } := by
  have ownerGS : LocTy state.store o (.growshrink element) := by
    rcases resizable with hg | hs
    · cases hg; exact ownerLoc.grow_to_growshrink
    · cases hs; exact ownerLoc
  have rootTypes := truncate_growshrink_rootTyLe state.store s' o len element ownerGS htruncate
  have agree := truncate_except_owner state.store s' o len htruncate
  obtain ⟨oldRoot, oldValue, newValue, newRoot, oldAt, oldGet, _, _, _⟩ :=
    modify_spec state.store s' o (Val.truncate len) htruncate
  have oldNonref : ¬ IsRef oldRoot := by
    obtain ⟨es, ownerRead, _⟩ := truncate_growshrink_shape state.store s' o len element ownerGS htruncate
    obtain ⟨root, rootAt, rootGet⟩ := (read_ok_iff _ _ _).1 ownerRead
    rw [oldAt] at rootAt
    cases rootAt
    cases oldRoot <;> simp only [IsRef] <;> try trivial
    all_goals cases hpath : o.path <;> simp [Val.get?, Val.children?, Val.elems?, hpath] at rootGet
  have newNonref : ∀ v, s'.roots[o.root]? = some v → ¬ IsRef v :=
    fun _ hv => truncate_ownerRoot_nonRef htruncate hv
  have domain : ∀ (r : RootInst), s'.roots[r]? ≠ none → state.store.roots[r]? ≠ none := by
    intro r hr
    by_cases same : r = o.root
    · subst r; rw [oldAt]; simp
    · rw [agree r same] at hr; exact hr
  have localTyped : ∀ (x : VarId) (lv : LocalVar) (si : ScopeInst) (v : Val), x ∈ tenv.visible → x ∈ future →
      env.vars[x]? = some lv → env.scopes.lookup lv.scope = some si →
      state.store.roots[RootInst.local env.act si x]? = some v →
      HasTy m W.G state.store v lv.ty → HasTy m W.G s' v lv.ty := by
    intro x lv si v hv hf hvar hscope hvalue ht
    exact Frame.localHasTy_afterGrowshrinkTruncate frame accessEq ownerTy resizable
      ownerRoot ownerLoc (futureNeeded x hf) (visibleActive x hv) hvar hscope hvalue ht htruncate
  have inv : StoreInvAt m W.G env tenv.visible future { state with store := s' } := by
    apply StoreInv.except frame.inv agree
    · intro r v hd _ hv _
      cases r with
      | global g =>
        have hn := frame.inv.globalNonRefs g v hv
        cases v <;> simp_all [Held, IsRef]
      | «local» a si x =>
        rcases hd with ⟨ha, hvis, hf, lv, hvar, hscope⟩
        subst a
        obtain ⟨lv', si', v', hvar', hscope', _, hv', ht⟩ := frame.vis x hvis hf
        rw [hvar] at hvar'; cases hvar'
        rw [hscope] at hscope'; cases hscope'
        rw [hv] at hv'; cases hv'
        exact (localTyped x lv si v hvis hf hvar hscope hv ht).held
    · intro r v _ same hv
      have hn := newNonref v (by simpa [same] using hv)
      cases v <;> simp_all [Held, IsRef]
    · intro r v same hv target ht
      exact False.elim ((newNonref v (by simpa [same] using hv)) ht.isRef)
    · intro a si x _ hv
      exact frame.inv.fresh a si x (domain _ hv)
    · intro g gl _ hg hgl
      exact rootTypes _ _ (frame.inv.globals g gl hg hgl)
    · intro g v same hv
      exact newNonref v (by simpa [same] using hv)
    · intro g v same hv
      have source : state.store.roots[RootInst.global g]? = some oldRoot := by
        simpa [same] using oldAt
      rcases frame.inv.globalStorageDomain g oldRoot source with declared | ⟨T, flat, typed⟩
      · exact Or.inl declared
      · obtain ⟨new, hread, htyped⟩ := rootTypes (.global g) T
          ⟨oldRoot, by simp [Store.read, source, Val.get?], typed⟩
        have readValue : s'.read ⟨.global g, []⟩ = .ok v := by
          simp [Store.read, hv, Val.get?]
        rw [readValue] at hread
        cases hread
        exact Or.inr ⟨T, flat, htyped⟩
  have sa : ∀ holder elem, W.D holder elem →
      ∃ v, s'.roots[holder]? = some v ∧ HasTy m W.G s' v (.slice .mutable elem) ∧
        ∀ target, Targets v target → W.A holder target := by
    rcases authority with hmay | ⟨a, si, x, heq, hbase⟩
    · exact frame.truncateGrowshrinkSa_of_mayShrink hprotected hmay ownerGS htruncate
    · intro holder elem hd
      obtain ⟨v, hv, ht, htargets⟩ := frame.sa holder elem hd
      have holderNe : holder ≠ o.root := by
        intro he; exact locTy_growshrink_root_ne_of_slice (by simpa [he] using hv) ht ownerGS
      obtain ⟨l, start, count, rfl, hflat, hslice⟩ := ht
      have rootNe : l.root ≠ o.root := by
        intro he
        obtain ⟨ha, hs, hx, hholder, hbefore⟩ := frame.dOut holder elem hd
        have age := frame.aOlder holder l.root (htargets l.root rfl)
        rw [he, heq, hholder] at age
        have older : si ≤ hs := age
        exact (Nat.not_le_of_gt hbefore) (Nat.le_trans hbase older)
      refine ⟨.slice l start count, ?_,
        HasTy.slice_truncate_unrelated_root htruncate rootNe ⟨l, start, count, rfl, hflat, hslice⟩,
        htargets⟩
      rw [agree holder holderNe]; exact hv
  refine ⟨{ frame with
    vis := ?_
    bindings := ?_
    storage := ?_
    rooted := ?_
    rootedOwners := ?_
    inv := inv
    sa := sa }, ?_, ?_⟩
  · intro x hv hf
    obtain ⟨lv, si, v, hvar, hscope, hp, hvalue, ht⟩ := frame.vis x hv hf
    by_cases same : RootInst.local env.act si x = o.root
    · have hn : lv.ty.isRefLike = false := by
        cases hb : lv.ty.isRefLike
        · rfl
        · have hvo : oldRoot = v := by rw [← same, hvalue] at oldAt; exact (Option.some.inj oldAt).symm
          exact False.elim (oldNonref (hvo.symm ▸ ht.isRef hb))
      obtain ⟨v', hv', ht'⟩ := LocTy.hasTyRoot (rootTypes _ _
        (frame.storage _ _ ⟨x, lv, si, hvar, hscope, rfl, hn, rfl⟩ v hvalue)) hn
      exact ⟨lv, si, v', hvar, hscope, hp, hv', ht'⟩
    · exact ⟨lv, si, v, hvar, hscope, hp, by rw [agree _ same]; exact hvalue,
        localTyped x lv si v hv hf hvar hscope hvalue ht⟩
  · intro x hv
    obtain ⟨lv, si, v, hvar, hscope, hp, hvalue, href⟩ := frame.bindings x hv
    by_cases same : RootInst.local env.act si x = o.root
    · obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.1 (truncate_root_exists _ _ _ _ htruncate)
      refine ⟨lv, si, v', hvar, hscope, hp, by simpa [same] using hv', ?_⟩
      intro htype
      have hvo : oldRoot = v := by rw [← same, hvalue] at oldAt; exact (Option.some.inj oldAt).symm
      exact False.elim (oldNonref (hvo.symm ▸ href htype))
    · exact ⟨lv, si, v, hvar, hscope, hp, by rw [agree _ same]; exact hvalue, href⟩
  · intro r T hs v hv
    obtain ⟨old, ho⟩ := Option.ne_none_iff_exists'.1 (domain r (by rw [hv]; simp))
    exact rootTypes r T (frame.storage r T hs old ho)
  · intro x lv si v hvar hscope hv target ht
    by_cases same : RootInst.local env.act si x = o.root
    · exact False.elim ((newNonref v (by simpa [same] using hv)) ht.isRef)
    · rw [agree _ same] at hv
      exact frame.rooted x lv si v hvar hscope hv target ht
  · intro x lv si v hvar hscope hv howner target ht
    by_cases same : RootInst.local env.act si x = o.root
    · exact False.elim ((newNonref v (by simpa [same] using hv)) ht.isRef)
    · rw [agree _ same] at hv
      exact frame.rootedOwners x lv si v hvar hscope hv howner target ht
  · refine ⟨Nat.le_refl _, ?_, ?_, domain⟩
    · intro r v hv href _ _
      have ne : r ≠ o.root := by
        intro same; subst r
        rw [oldAt] at hv; cases hv
        exact oldNonref href
      rw [agree r ne]; exact hv
    · intro r v hv href _ _
      have ne : r ≠ o.root := by
        intro same; subst r
        exact newNonref v hv href
      rw [agree r ne] at hv; exact hv
  · intro hp
    rw [profile] at hp
    cases hp

private theorem statementModifyPreservesRootTypes {m : Module} {G : Nat}
    {observation : Observation} {source destination : Store} {l : Loc} {target : Ty}
    {modify : Val → Option Val}
    (hle : StoreLe source destination) (hloc : LocTy source l target)
    (hmodify : source.modify l modify = .ok destination) :
    PreservesRootTypes m G observation.roots source destination := by
  obtain ⟨oldRoot, oldValue, targetValue, newRoot, hroot, hget, hvalue, hmod, hroots⟩ :=
    modify_spec source destination l modify hmodify
  have hrootsExcept : ∀ r, r ≠ l.root → destination.roots[r]? = source.roots[r]? := by
    intro r hne
    rw [hroots]
    have hne' : l.root ≠ r := fun he => hne he.symm
    simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hne']
  obtain ⟨locValue, hread, htargetFlat⟩ := hloc
  obtain ⟨rootValue, hrootValue, hpath⟩ := (read_ok_iff source l locValue).1 hread
  have hsameRoot : rootValue = oldRoot := Option.some.inj (hrootValue.symm.trans hroot)
  subst rootValue
  have hnotRef : ∀ targetLoc, oldRoot ≠ .ref targetLoc := by
    intro targetLoc heq
    subst oldRoot
    cases hpathLoc : l.path with
    | nil =>
        rw [hpathLoc, get_nil] at hpath
        have hlocEq : locValue = .ref targetLoc := (Option.some.inj hpath).symm
        subst locValue
        exact (flat_not_ref htargetFlat) (by trivial)
    | cons index rest =>
        rw [hpathLoc] at hpath
        simp [Val.get?, Val.children?, Val.elems?] at hpath
  have hnotSlice : ∀ targetLoc start count, oldRoot ≠ .slice targetLoc start count := by
    intro targetLoc start count heq
    subst oldRoot
    cases hpathLoc : l.path with
    | nil =>
        rw [hpathLoc, get_nil] at hpath
        have hlocEq : locValue = .slice targetLoc start count := (Option.some.inj hpath).symm
        subst locValue
        exact (flat_not_ref htargetFlat) (by trivial)
    | cons index rest =>
        rw [hpathLoc] at hpath
        simp [Val.get?, Val.children?, Val.elems?] at hpath
  have hnotUnit : oldRoot ≠ .unit := by
    intro heq
    subst oldRoot
    cases hpathLoc : l.path with
    | nil =>
        rw [hpathLoc, get_nil] at hpath
        have hlocEq : locValue = .unit := (Option.some.inj hpath).symm
        subst locValue
        cases target <;> simp [FlatTy] at htargetFlat
    | cons index rest =>
        rw [hpathLoc] at hpath
        simp [Val.get?, Val.children?, Val.elems?] at hpath
  have hnewRoot : destination.roots[l.root]? = some newRoot := by
    rw [hroots]
    simp [Std.HashMap.getElem?_insert]
  intro r T hObserved v hv htyped
  by_cases hsame : r = l.root
  · subst r
    have hvEq : oldRoot = v := Option.some.inj (hroot.symm.trans hv)
    subst oldRoot
    cases T with
    | ref mu target =>
        obtain ⟨targetLoc, rfl, _⟩ := htyped
        exact False.elim (hnotRef targetLoc rfl)
    | slice mu element =>
        obtain ⟨targetLoc, start, count, rfl, _, _⟩ := htyped
        exact False.elim (hnotSlice targetLoc start count rfl)
    | unit =>
        simp only [HasTy] at htyped
        exact False.elim (hnotUnit htyped)
    | tuple fields => simp [HasTy] at htyped
    | int width =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
    | bool =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
    | arr element size =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
    | grow element =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
    | growshrink element =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
    | limited element capacity =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
    | structT id fields =>
        obtain ⟨newValue, hnewValue, hflatValue⟩ := flat_mono hle hv htyped
        have hnewValueEq : newValue = newRoot := Option.some.inj (hnewValue.symm.trans hnewRoot)
        subst newValue
        exact ⟨newRoot, hnewRoot, hflatValue⟩
  · refine ⟨v, ?_, HasTy.mono hle htyped⟩
    rw [hrootsExcept r hsame]
    exact hv

private theorem statementWritePreservesRootTypes {m : Module} {G : Nat}
    {observation : Observation} {source destination : Store} {l : Loc} {target : Ty} {value : Val}
    (hle : StoreLe source destination) (hloc : LocTy source l target)
    (hwrite : source.write l value = .ok destination) :
    PreservesRootTypes m G observation.roots source destination := by
  apply statementModifyPreservesRootTypes hle hloc
  simpa [Store.write] using hwrite

/- A replacement write starts from the empty owner installed by truncate. The
   old value has no elements to lose, so a typed replacement refines it. -/
private theorem Refines.emptyResizable {E : Ty} {es : Array Val}
    (items : ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy E e) :
    Refines (.resizable E #[]) (.resizable E es) := by
  intro path value hget
  cases path with
  | nil =>
    have hvalue : value = .resizable E #[] := by
      simpa [Val.get?] using hget.symm
    subst value
    refine ⟨.resizable E es, by simp [Val.get?], ?_, ?_⟩
    · intro T hflat
      cases T with
      | grow element =>
        simp only [FlatTy] at hflat ⊢
        cases hflat.1
        exact ⟨rfl, items⟩
      | growshrink element =>
        simp only [FlatTy] at hflat ⊢
        cases hflat.1
        exact ⟨rfl, items⟩
      | _ => simp [FlatTy] at hflat
    · intro oldElements helems
      simp only [Val.elems?, Option.some.injEq] at helems
      subst oldElements
      exact ⟨es, by simp [Val.elems?], Nat.zero_le _⟩
  | cons index rest =>
    simp [Val.get?, Val.children?, Val.elems?] at hget

private theorem statementAssignWholeWriteFlatStep {source destination : Store}
    {location : Loc} {element : Ty} {elements : Array Val}
    (hempty : source.read location = .ok (.resizable element #[]))
    (hwrite : source.write location (.resizable element elements) = .ok destination)
    (items : ∀ (i : Nat) (value : Val), elements[i]? = some value → FlatTy element value) :
    FlatStep source destination := by
  have hmodify : source.modify location (fun _ => some (.resizable element elements)) =
      .ok destination := by
    simpa [Store.write] using hwrite
  apply flatStep_modify source destination location
    (fun _ => some (.resizable element elements)) (.resizable element #[]) hmodify hempty
    (by simp [IsRef])
  intro value hvalue
  simp only [Option.some.injEq] at hvalue
  subst value
  exact ⟨by simp [IsRef], Refines.emptyResizable items⟩

private theorem statementAppendPreservesRootTypes {m : Module} {G : Nat}
    {observation : Observation} {source destination : Store} {l : Loc} {target : Ty}
    {values : Array Val} {index : Nat}
    (hloc : LocTy source l target)
    (happend : source.append l values = .ok (destination, index))
    (hstep : FlatStep source destination) :
    PreservesRootTypes m G observation.roots source destination := by
  apply statementModifyPreservesRootTypes hstep.le hloc
  rcases append_spec source destination l values index happend with
    ⟨_, _, _, _, hmodify⟩ | ⟨_, _, _, _, _, _, hmodify⟩
  · exact hmodify
  · exact hmodify

private theorem statementFlatStepPreservation {W : World} {env : Env} {s s' : St}
    {observation : Observation} {shrinking : RootInst → Prop} {aliases : List RetainedAlias}
    (hsafe : ObservedSafe m W shrinking observation s.store)
    (hroots : PreservesRootTypes m W.G observation.roots s.store s'.store)
    (hstep : FlatStep s.store s'.store) :
    PreservesRootTypes m W.G observation.roots s.store s'.store ∧
    PreservesValues m W.G observation.values s.store s'.store ∧
    ObservedSafe m W shrinking observation s'.store ∧
    RetainsAliases m W env s.store s'.store aliases ∧
    PilotStoreLe m s s' := by
  have hvalues : PreservesValues m W.G observation.values s.store s'.store := by
    intro v T hobserved hty
    exact HasTy.mono hstep.le hty
  have htyped' := hsafe.typed.advance hroots hvalues
  have hsafe' : ObservedSafe m W shrinking observation s'.store := by
    refine ⟨htyped', hsafe.rootsOlder, hsafe.valuesOlder, ?_,
      hsafe.valuesProtected, hsafe.holderTypes⟩
    intro r T v hobserved hroot hinterior target htarget
    obtain ⟨new, hnew, htyped⟩ := htyped'.roots r T hobserved
    have heq : new = v := Option.some.inj (hnew.symm.trans hroot)
    subst new
    have href := statementHasTyInteriorIsRef htyped hinterior
    rcases hstep.back r v hroot with hold | ⟨hnotRef, _⟩
    · obtain ⟨old, holdOld, _⟩ := hsafe.typed.roots r T hobserved
      have holdEq : old = v := Option.some.inj (holdOld.symm.trans hold)
      subst old
      exact hsafe.rootsProtected r T v hobserved hold hinterior target htarget
    · exact False.elim (hnotRef href)
  have hretains : RetainsAliases m W env s.store s'.store aliases := by
    intro alias _
    constructor
    · intro v ⟨hty, hgam⟩
      exact ⟨HasTy.mono hstep.le hty, hgam⟩
    · intro mu element capacity l start len htype halias hslice
      exact SliceTy.mono hstep.le hslice
  exact ⟨hroots, hvalues, hsafe', hretains, fun _ => hstep.le⟩

/- The replacement expression runs after the owner has been emptied. Exact
   root agreement keeps that empty header available to the final write. -/
private theorem statementAssignWholeWritePreservation
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {before clear evaluated : St} {destination : Store} {future : List VarId}
    {observation : Observation} {shrinking : RootInst → Prop}
    {aliases : List RetainedAlias} {location : Loc} {element : Ty}
    {elements : Array Val} {target : Ty}
    (hframe : Frame m W tenv penv env evaluated future)
    (hsafe : ObservedSafe m W shrinking observation evaluated.store)
    (htarget : target = .grow element ∨ target = .growshrink element)
    (hloc : LocTy before.store location target)
    (hclear : before.store.truncate location 0 = .ok clear.store)
    (hpath : location.path = [])
    (hroot : evaluated.store.roots[location.root]? = clear.store.roots[location.root]?)
    (hwrite : evaluated.store.write location (.resizable element elements) = .ok destination)
    (hitems : ∀ (i : Nat) (value : Val), elements[i]? = some value → FlatTy element value) :
    Frame m W tenv penv env { evaluated with store := destination } future ∧
    Footprint (insts env) (Dset W) evaluated { evaluated with store := destination } ∧
    PreservesRootTypes m W.G observation.roots evaluated.store destination ∧
    PreservesValues m W.G observation.values evaluated.store destination ∧
    ObservedSafe m W shrinking observation destination ∧
    RetainsAliases m W env evaluated.store destination aliases ∧
    PilotStoreLe m evaluated { evaluated with store := destination } ∧
    LocTy destination location target := by
  have hlocClear : LocTy before.store location (.growshrink element) := by
    rcases htarget with rfl | rfl
    · exact hloc.grow_to_growshrink
    · exact hloc
  obtain ⟨_, _, _, hemptyClear, _⟩ :=
    clear_growshrink before.store clear.store location element hlocClear hclear
  have hempty : evaluated.store.read location = .ok (.resizable element #[]) := by
    simpa only [Store.read, hroot, hpath] using hemptyClear
  have hlocPost : LocTy destination location target := by
    rcases htarget with rfl | rfl
    · exact (assignWhole_grow before.store clear.store evaluated.store destination
        location element elements hloc hclear hempty hwrite hitems).2.2.2.2
    · exact (assignWhole_growshrink before.store clear.store evaluated.store destination
        location element elements hloc hclear hempty hwrite hitems).2.2.2.2
  have hstep := statementAssignWholeWriteFlatStep hempty hwrite hitems
  have hlocEval : LocTy evaluated.store location (.growshrink element) :=
    ⟨.resizable element #[], hempty, by simp [FlatTy]⟩
  have hroots : PreservesRootTypes m W.G observation.roots evaluated.store destination :=
    statementWritePreservesRootTypes (observation := observation)
    hstep.le hlocEval hwrite
  obtain ⟨_, hvalues, hsafePost, hretained, hpilot⟩ :=
    statementFlatStepPreservation (s := evaluated)
      (s' := { evaluated with store := destination }) (env := env) (aliases := aliases)
      hsafe hroots hstep
  exact ⟨hframe.flatStep hstep, Footprint.of_flatStep hstep, hroots,
    hvalues, hsafePost, hretained, hpilot, hlocPost⟩

private theorem statementAssignWholeForbiddenRootAgreement
    {W : World} {env : Env} {clear evaluated : St} {forbidden : List DemandOwner}
    {owner : DemandOwner} {location : Loc} {element : Ty}
    (hforbidden : PreservesForbiddenOwnerRoots (m := m) (G := W.G)
      (env := env) (P := W.P) forbidden clear evaluated)
    (hmem : owner ∈ forbidden)
    (htype : owner.ty = some (.grow element) ∨ owner.ty = some (.growshrink element))
    (hgam : Gam env W.P owner.roots location.root)
    (hpath : location.path = [])
    (hempty : clear.store.read location = .ok (.resizable element #[])) :
    evaluated.store.roots[location.root]? = clear.store.roots[location.root]? := by
  have hheader : clear.store.roots[location.root]? = some (.resizable element #[]) := by
    cases hroot : clear.store.roots[location.root]? with
    | none => simp [Store.read, hroot] at hempty
    | some value =>
      have heq : value = .resizable element #[] := by
        simpa [Store.read, hroot, hpath, Val.get?] using hempty
      simpa [heq] using hroot
  exact hforbidden owner hmem location.root ⟨element, #[], htype, hgam, hheader⟩

private theorem statementAssignWholeTypeInputs
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

private theorem statementAssignWholeCheckedOwnerFacts
    {access : AccessEnv} {tenv : TEnv} {penv : PEnv} {p : Place} {owner : DemandOwner}
    {target : Ty} {binding contents : Bool} {tn tn' : Nat} {rst rst' : RState}
    {roots : List RootRef}
    (haccess : access.mod = tenv.mod ∧ access.impl.vars = tenv.vars ∧
      access.mod = penv.mod ∧ access.impl = penv.impl ∧ access.ctx = penv.ctx)
    (howner : access.owner p = .ok owner)
    (htype : tyPlace tenv p tn = .ok (⟨target, binding, contents⟩, tn'))
    (hreplay : rpPlace penv p rst = .ok (roots, rst')) :
    access = penv.access ∧ owner.ty = some target ∧
      access.placeRoots p = .ok owner.roots ∧ RootsIncluded roots owner.roots := by
  have hmod : tenv.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
  have hvars : tenv.vars = penv.impl.vars :=
    haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
  have heq : access = penv.access := by
    cases access
    unfold PEnv.access
    congr 1
    · exact haccess.2.2.1
    · exact haccess.2.2.2.1
    · exact haccess.2.2.2.2
  rw [heq] at howner ⊢
  have hplaceType := tyPlace_accessType hmod hvars htype
  simp only [AccessEnv.owner, hplaceType] at howner
  cases hroots : penv.access.placeRoots p with
  | error error => simp [hroots, Functor.map, Except.map] at howner
  | ok staticRoots =>
    simp [hroots, Functor.map, Except.map] at howner
    subst owner
    exact ⟨rfl, rfl, rfl,
      rpPlace_accessRoots penv p rst roots rst' staticRoots hreplay hroots⟩

private theorem statementAssignWholeMutationRoot
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {state : St}
    {future : List VarId} {roots : List RootRef} {root : RootInst} {effect : Eff}
    (frame : Frame m W tenv penv env state future)
    (denotes : Gam env W.P roots root)
    (recorded : ∀ target, target ∈ rootsTargets roots → target ∈ effect.shrinks) :
    MutationRoots env W.P W.base (effectMutationRoots m penv.impl effect) root := by
  have hknown (target : Target) (hshrink : target ∈ effect.shrinks) :
      effectTargetRoot target ∈ effectMutationRoots m penv.impl effect := by
    have htarget : target ∈ effectMutationTargets effect := by
      simp only [effectMutationTargets, List.mem_append]
      exact Or.inl (Or.inr hshrink)
    have hroot : effectTargetRoot target ∈ effectTargetRoots (effectMutationTargets effect) :=
      List.mem_map.mpr ⟨target, htarget, rfl⟩
    unfold effectMutationRoots
    split
    · exact List.mem_append_left _ hroot
    · exact hroot
  obtain ⟨reference, hmem, hroot⟩ := denotes
  cases reference with
  | «local» x =>
    rcases hroot with ⟨lv, si, hvar, hlookup, hroot⟩
    obtain ⟨before, after, hscopes, _⟩ := List.lookup_eq_some_iff.mp hlookup
    have hscope : (lv.scope, si) ∈ env.scopes := by
      rw [hscopes]
      exact List.mem_append_right _ List.mem_cons_self
    exact Or.inr ⟨env.act, si, x, hroot, (frame.below _ hscope).1⟩
  | global g =>
    exact Or.inl ⟨.global g, hknown (.global g)
      (recorded (.global g) (mem_rootsTargets_global hmem)), hroot⟩
  | param i =>
    exact Or.inl ⟨.param i, hknown (.param i)
      (recorded (.param i) (mem_rootsTargets_param hmem)), hroot⟩

private theorem statementAssignWholeTruncateBind
    {location : Loc} {element : Ty} {state : St} {next : Unit → M α}
    {post : α → St → Prop}
    (hloc : LocTy state.store location (.growshrink element))
    (hnext : ∀ destination, state.store.truncate location 0 = .ok destination →
      Sat (next ()) { state with store := destination } post) :
    Sat (truncateLoc location 0 >>= next) state post := by
  obtain ⟨value, hread, hflat⟩ := hloc
  cases value <;> simp only [FlatTy] at hflat
  case resizable actual elements =>
    rcases hflat with ⟨rfl, _⟩
    obtain ⟨destination, hmodify⟩ := modify_total state.store location (Val.truncate 0)
      (.resizable element elements) (.resizable element #[]) hread (by simp [Val.truncate])
    have htruncate : state.store.truncate location 0 = .ok destination := by
      simpa [Store.truncate] using hmodify
    have heval : (truncateLoc location 0 >>= next) state =
        next () { state with store := destination } := by
      show M.bind' (truncateLoc location 0) next state = _
      simp [M.bind', truncateLoc, htruncate]
    unfold Sat
    rw [heval]
    exact hnext destination htruncate
  all_goals contradiction

private theorem statementAssignWholeOwnerEffects
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {source destination : St}
    {future : List VarId} {location : Loc} {ownerRoots effectRoots : List RootRef}
    {forbidden : List DemandOwner}
    (hframe : Frame m W tenv penv env source future)
    (howner : Gam env W.P ownerRoots location.root)
    (heffect : MutationRoots env W.P W.base effectRoots location.root)
    (hdisjoint : ∀ owner, owner ∈ forbidden →
      DemandRootsDisjoint owner.roots ownerRoots)
    (hagree : StoreLeExcept (fun r => r = location.root) source.store destination.store) :
    PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
      forbidden source destination ∧
    MutationFootprint env W.P W.base effectRoots source destination := by
  constructor
  · intro owner hmem r hsource
    obtain ⟨element, elements, htype, hroot, hvalue⟩ := hsource
    exact hagree r (Gam.root_ne_of_no_overlap hframe (hdisjoint owner hmem)
      hroot howner)
  · intro r hnot
    apply hagree r
    intro heq
    exact hnot (heq.symm ▸ heffect)

private theorem statementAssignWholeReplacement
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    {before clear : St} {future : List VarId} {replacement : M Val}
    {observation : Observation} {shrinking : RootInst → Prop}
    {aliases : List RetainedAlias} {location : Loc} {element : Ty} {target : Ty}
    {forbidden parentForbidden : List DemandOwner} {owner : DemandOwner}
    {effectRoots : List RootRef}
    (htarget : target = .grow element ∨ target = .growshrink element)
    (hloc : LocTy before.store location target)
    (hclear : before.store.truncate location 0 = .ok clear.store)
    (hpath : location.path = [])
    (hmem : owner ∈ forbidden)
    (htype : owner.ty = some (.grow element) ∨ owner.ty = some (.growshrink element))
    (hgam : Gam env W.P owner.roots location.root)
    (heffect : MutationRoots env W.P W.base effectRoots location.root)
    (hsubset : ∀ owner, owner ∈ parentForbidden → owner ∈ forbidden)
    (hdisjoint : ∀ excluded, excluded ∈ parentForbidden →
      DemandRootsDisjoint excluded.roots owner.roots)
    (hrhs : Sat replacement clear (fun value evaluated =>
      Frame m W tenv penv env evaluated future ∧
      Footprint (insts env) (Dset W) clear evaluated ∧
      PreservesRootTypes m W.G observation.roots clear.store evaluated.store ∧
      PreservesValues m W.G observation.values clear.store evaluated.store ∧
      ObservedSafe m W shrinking observation evaluated.store ∧
      RetainsAliases m W env clear.store evaluated.store aliases ∧
      PilotStoreLe m clear evaluated ∧ HasTy m W.G evaluated.store value target ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        forbidden clear evaluated ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation evaluated.store) ∧
      MutationFootprint env W.P W.base effectRoots clear evaluated)) :
    Sat (do
      let value ← replacement
      match value with
      | .resizable .. => writeLoc location value
      | _ => fault .shape
      pure (Flow.normal .unit)) clear (fun flow final =>
      Frame m W tenv penv env final future ∧
      Footprint (insts env) (Dset W) clear final ∧
      PreservesRootTypes m W.G observation.roots clear.store final.store ∧
      PreservesValues m W.G observation.values clear.store final.store ∧
      ObservedSafe m W shrinking observation final.store ∧
      RetainsAliases m W env clear.store final.store aliases ∧
      PilotStoreLe m clear final ∧ LocTy final.store location target ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation final.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        parentForbidden clear final ∧
      MutationFootprint env W.P W.base effectRoots clear final ∧ flow = .normal .unit) := by
  refine Sat.bind hrhs ?_
  rintro value evaluated ⟨hframe, hfoot, hroots, hvalues, hsafe, hretained, hpilot,
    htyped, hforbidden, hclassified, hmutation⟩
  have hflat : FlatTy (.grow element) value := by
    rcases htarget with rfl | rfl
    · exact htyped
    · cases value <;> simpa [HasTy, FlatTy] using htyped
  have hshape : ∃ elements, value = .resizable element elements ∧
      ∀ (i : Nat) (item : Val), elements[i]? = some item → FlatTy element item := by
    cases value <;> simp only [FlatTy] at hflat
    case resizable actual elements =>
      rcases hflat with ⟨rfl, hitems⟩
      exact ⟨elements, rfl, hitems⟩
    all_goals contradiction
  obtain ⟨elements, rfl, hitems⟩ := hshape
  have hlocClear : LocTy before.store location (.growshrink element) := by
    rcases htarget with rfl | rfl
    · exact hloc.grow_to_growshrink
    · exact hloc
  obtain ⟨_, _, _, hemptyClear, _⟩ :=
    clear_growshrink before.store clear.store location element hlocClear hclear
  have hagreement := statementAssignWholeForbiddenRootAgreement
    hforbidden hmem htype hgam hpath hemptyClear
  have hempty : evaluated.store.read location = .ok (.resizable element #[]) := by
    simpa only [Store.read, hagreement, hpath] using hemptyClear
  have hlocEval : LocTy evaluated.store location (.growshrink element) :=
    ⟨.resizable element #[], hempty, by simp [FlatTy]⟩
  refine sat_writeLoc_bind hlocEval ?_
  intro destination hwrite
  simp only [sat_pure]
  obtain ⟨hframePost, hfootPost, hrootsPost, hvaluesPost, hsafePost, hretainedPost,
      hpilotPost, hlocPost⟩ := statementAssignWholeWritePreservation
    hframe hsafe htarget hloc hclear hpath hagreement hwrite hitems
  have hagreeWrite : StoreLeExcept (fun r => r = location.root)
      evaluated.store destination :=
    modify_roots_agree_except evaluated.store destination location
      (fun _ => some (.resizable element elements)) (by simpa [Store.write] using hwrite)
  obtain ⟨hforbiddenPost, hmutationPost⟩ := statementAssignWholeOwnerEffects
    (destination := { evaluated with store := destination })
    hframe hgam heffect hdisjoint hagreeWrite
  exact ⟨hframePost, hfoot.trans hfootPost, hroots.trans hrootsPost,
    hvalues.trans hvaluesPost, hsafePost, hretained.trans hretainedPost,
    fun hprofile => StoreLe.trans (hpilot hprofile) (hpilotPost hprofile), hlocPost,
    fun hprofile => hframe.classifiedParameters_advance (hclassified hprofile) hfootPost,
    (hforbidden.subset hsubset).trans hforbiddenPost, hmutation.trans hmutationPost, trivial⟩

private theorem statementExprChildSpec (ih : Specs m prof plans n)
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (e : Expr)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.expression e))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W) (hF : Frame m W tenv penv env s ec.inputFuture)
    (hvisible : ∀ x, x ∈ tenv.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (hinput : ∀ x,
      x ∈ (ec.child rfl index (DemandNode.expression e) .expression hchild (by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef)
    (ht : tyExpr tenv e tn = .ok (ty, tn'))
    (hr : rpExpr penv e rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalExpr n ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s'
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      OwnerRooted env W.ownerP rho v ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  let childEc := ec.child rfl index (DemandNode.expression e) .expression hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have facts := statementChildFacts ec observation W tenv tenv penv env s index
    (DemandNode.expression e) .expression hchild (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hactive haccess hprotected
    hobserved hF hvisible hinput
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  have hresult := ih.expr (path ++ [index]) e childEc observation W tenv penv env s tn tn' ty rst rst' rho
    facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 hclassified hp facts.2.2.2.2.1 ht hr hE
  refine hresult.mono ?_
  intro v s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hty, hgam, _, howner, hforbidden, hmutation⟩
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset (fun alias hmem => ec.child_retained_subset rfl index
      (DemandNode.expression e) .expression hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem),
    hpilot, hty, hgam, howner,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.expression e)
      .expression hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])),
    hforbidden, hmutation⟩

private theorem statementExprChildSpecAtFrame
    (ih : Specs m prof plans n) {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (e : Expr)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.expression e))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv' penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W)
    (childEc : EvaluationContext m plans (path ++ [index]) (DemandNode.expression e) .expression)
    (hchildEc : childEc = ec.child rfl index (DemandNode.expression e) .expression hchild (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]))
    (hF : Frame m W tenv' penv env s childEc.inputFuture)
    (hvisible : ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (retained : List RetainedAlias)
    (hretained : ∀ alias, alias ∈ retained → alias ∈ childEc.retained)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef)
    (ht : tyExpr tenv' e tn = .ok (ty, tn'))
    (hr : rpExpr penv e rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalExpr n ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv' penv env s' childEc.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      OwnerRooted env W.ownerP rho v ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  rw [← hchildEc] at hmay
  have hactiveChild0 := ec.child_activeMatches rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv tenv' hactive hvisible
  have hactiveChild := hchildEc.symm ▸ hactiveChild0
  have haccessChild0 := (ec.child_accessMatches_iff rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv' penv).2 haccess
  have haccessChild := hchildEc.symm ▸ haccessChild0
  have hprotectedChild := hprotected.mono (fun _ _ h => h) (fun _ _ h => h)
    (fun root h => (hmay root).1 h)
  have hobservedChild := hobserved.weakenShrinking (fun root h => (hmay root).1 h)
  have hresult := ih.expr (path ++ [index]) e childEc observation W tenv' penv env s
    tn tn' ty rst rst' rho hactiveChild haccessChild hprotectedChild hobservedChild
    hclassified hp hF ht hr hE
  refine hresult.mono ?_
  intro v s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hty, hgam, _, howner, hforbidden, hmutation⟩
  rw [hchildEc] at hforbidden
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset hretained, hpilot, hty, hgam, howner,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.expression e)
      .expression hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])),
    hforbidden, hmutation⟩

private theorem statementViewChildSpecAtFrame
    (ih : Specs m prof plans n) {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (v : View)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.view v))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv' penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W)
    (childEc : EvaluationContext m plans (path ++ [index]) (DemandNode.view v) .view)
    (hchildEc : childEc = ec.child rfl index (DemandNode.view v) .view hchild (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]))
    (hF : Frame m W tenv' penv env s childEc.inputFuture)
    (hvisible : ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (retained : List RetainedAlias)
    (hretained : ∀ alias, alias ∈ retained → alias ∈ childEc.retained)
    (tn tn' : Nat) (el : Ty) (mu : Bool) (rst rst' : RState) (rho : List RootRef)
    (ht : tyView tenv' v tn = .ok ((el, mu), tn'))
    (hr : rpView penv v rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalView n ⟨prof, m⟩ env v) s (fun vw s' =>
      Frame m W tenv' penv env s' childEc.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store retained ∧
      PilotStoreLe m s s' ∧ ViewOk s'.store vw el ∧
      Gam env W.P rho vw.loc.root ∧ ViewAliases m W penv env s'.store v vw el ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.view v) .view
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  rw [← hchildEc] at hmay
  have hactiveChild0 := ec.child_activeMatches rfl index (DemandNode.view v) .view
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv tenv' hactive hvisible
  have hactiveChild := hchildEc.symm ▸ hactiveChild0
  have haccessChild0 := (ec.child_accessMatches_iff rfl index (DemandNode.view v) .view
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv' penv).2 haccess
  have haccessChild := hchildEc.symm ▸ haccessChild0
  have hprotectedChild := hprotected.mono (fun _ _ h => h) (fun _ _ h => h)
    (fun root h => (hmay root).1 h)
  have hobservedChild := hobserved.weakenShrinking (fun root h => (hmay root).1 h)
  have hresult := ih.view (path ++ [index]) v childEc observation W tenv' penv env s
    tn tn' el mu rst rst' rho hactiveChild haccessChild hprotectedChild hobservedChild
    hclassified hp hF ht hr hE
  refine hresult.mono ?_
  intro vw s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hview, hgam,
    haliases, _, hforbidden, hmutation⟩
  rw [hchildEc] at hforbidden
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset hretained, hpilot, hview, hgam, haliases,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.view v)
      .view hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])), hmutation⟩

private theorem statementPlaceChildSpec (ih : Specs m prof plans n)
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (p : Place)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.place p))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W) (hF : Frame m W tenv penv env s ec.inputFuture)
    (hvisible : ∀ x, x ∈ tenv.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (hinput : ∀ x,
      x ∈ (ec.child rfl index (DemandNode.place p) .place hchild (by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture)
    (tn tn' : Nat) (ty : Ty) (mu contents : Bool)
    (rst rst' : RState) (rho : List RootRef)
    (ht : tyPlace tenv p tn = .ok (⟨ty, mu, contents⟩, tn'))
    (hr : rpPlace penv p rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalPlace n ⟨prof, m⟩ env p) s (fun l s' =>
      Frame m W tenv penv env s'
        (ec.child rfl index (DemandNode.place p) .place hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ PlaceOk m W.G W.P penv env s'.store p l ty ∧
      Gam env W.P rho l.root ∧
      ((∃ el, ty = .grow el ∨ ty = .growshrink el) → Gam env W.ownerP rho l.root) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  let childEc := ec.child rfl index (DemandNode.place p) .place hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have facts := statementChildFacts ec observation W tenv tenv penv env s index
    (DemandNode.place p) .place hchild (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hactive haccess hprotected
    hobserved hF hvisible hinput
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.place p) .place
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  have hresult := ih.place (path ++ [index]) p childEc observation W tenv penv env s
    tn tn' ty mu contents rst rst' rho facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1
    hclassified hp
    facts.2.2.2.2.1 ht hr hE
  refine hresult.mono ?_
  intro l s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hplace, hgam, _, howner, hforbidden, hmutation⟩
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset (fun alias hmem => ec.child_retained_subset rfl index
      (DemandNode.place p) .place hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem),
    hpilot, hplace, hgam, howner,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.place p)
      .place hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])), hmutation⟩

private theorem statementAssignPlaceInputSubset
    {path : List Nat} {p : Place} {e : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.assign p e o)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place p) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.assign p e o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphase : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.assign p e o).variables = p.variables ++ e.variables := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ p.variables ++
      (DemandNode.statement (.assign p e o)).visibleForChild active 0 at hx
    have hchild : x ∈ p.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hx
    have hparent : x ∈ (p.variables ++ e.variables) ++ active := by
      rcases List.mem_append.mp hchild with hp | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.place p) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.assign p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.assign p e o)).visibleForChild
                context.expected.frame.active 0,
              e.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchild hphase).inputFuture =
        p.variables ++ (e.variables ++ context.expected.frame.future) := by
      change p.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    intro x hx
    rw [hchildInput] at hx
    have hparent : x ∈ (p.variables ++ e.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hx with hp | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · rcases List.mem_append.mp rest with he | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _ he)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementAssignExprInputFrame
    {path : List Nat} {p : Place} {e : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.assign p e o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFPlace : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.place p) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression e) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildP : (DemandNode.statement (.assign p e o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseP : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildE : (DemandNode.statement (.assign p e o)).child? 1 =
      some (DemandNode.expression e) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseE : DemandNodeHasPhase (DemandNode.expression e) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.place p).visibleAfter
        ((DemandNode.statement (.assign p e o)).visibleForChild active 0)) at hFPlace
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFPlace
    have hchanged := hFactive.changeFuture (future' := e.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionP := context.child rfl 0 (DemandNode.place p) .place hchildP hphaseP
    let transitionE := context.child rfl 1 (DemandNode.expression e) .expression hchildE hphaseE
    have hexpectationP :
        (DemandNode.statement (.assign p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.assign p e o)).visibleForChild
                context.expected.frame.active 0,
              e.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP]
    have hexpectationE :
        (DemandNode.statement (.assign p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.assign p e o)).visibleForChild
                context.expected.frame.active 1,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
    have hfutureP := DemandNode.childFrame_future transitionP.childFrameEq hexpectationP
    have hfutureE := DemandNode.childFrame_future transitionE.childFrameEq hexpectationE
    have houtputP :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchildP hphaseP).outputFuture =
          e.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transitionP.context.expected.frame.future =
        e.variables ++ context.expected.frame.future
      rw [transitionP.expectedFrameEq, DemandNode.phaseFrame_future transitionP.phaseFrameEq,
        hfutureP]
      simp [DemandNode.phaseFuture]
    have hinputE :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression e) .expression hchildE hphaseE).inputFuture =
          e.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change e.variables ++ transitionE.context.expected.frame.future =
        e.variables ++ context.expected.frame.future
      rw [transitionE.expectedFrameEq, DemandNode.phaseFrame_future transitionE.phaseFrameEq,
        hfutureE]
      simp [DemandNode.phaseFuture]
    rw [houtputP] at hFPlace
    rw [hinputE]
    exact hFPlace

private theorem statementAssignWholePlaceInputSubset
    {path : List Nat} {p : Place} {e : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.assignWhole p e o)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place p) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.assignWhole p e o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphase : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.assignWhole p e o).variables = p.variables ++ e.variables := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ p.variables ++
      (DemandNode.statement (.assignWhole p e o)).visibleForChild active 0 at hx
    have hchild : x ∈ p.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hx
    have hparent : x ∈ (p.variables ++ e.variables) ++ active := by
      rcases List.mem_append.mp hchild with hp | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.place p) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.assignWhole p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.assignWhole p e o)).visibleForChild
                context.expected.frame.active 0,
              e.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchild hphase).inputFuture =
        p.variables ++ (e.variables ++ context.expected.frame.future) := by
      change p.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    intro x hx
    rw [hchildInput] at hx
    have hparent : x ∈ (p.variables ++ e.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hx with hp | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · rcases List.mem_append.mp rest with he | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _ he)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementAssignWholeExprInputFrame
    {path : List Nat} {p : Place} {e : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.assignWhole p e o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFPlace : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.place p) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression e) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildP : (DemandNode.statement (.assignWhole p e o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseP : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildE : (DemandNode.statement (.assignWhole p e o)).child? 1 =
      some (DemandNode.expression e) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseE : DemandNodeHasPhase (DemandNode.expression e) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.place p).visibleAfter
        ((DemandNode.statement (.assignWhole p e o)).visibleForChild active 0)) at hFPlace
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFPlace
    have hchanged := hFactive.changeFuture (future' := e.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionP := context.child rfl 0 (DemandNode.place p) .place hchildP hphaseP
    let transitionE := context.child rfl 1 (DemandNode.expression e) .expression hchildE hphaseE
    have hexpectationP :
        (DemandNode.statement (.assignWhole p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.assignWhole p e o)).visibleForChild
                context.expected.frame.active 0,
              e.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP]
    have hexpectationE :
        (DemandNode.statement (.assignWhole p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.assignWhole p e o)).visibleForChild
                context.expected.frame.active 1,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
    have hfutureP := DemandNode.childFrame_future transitionP.childFrameEq hexpectationP
    have hfutureE := DemandNode.childFrame_future transitionE.childFrameEq hexpectationE
    have houtputP :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchildP hphaseP).outputFuture =
          e.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transitionP.context.expected.frame.future =
        e.variables ++ context.expected.frame.future
      rw [transitionP.expectedFrameEq, DemandNode.phaseFrame_future transitionP.phaseFrameEq,
        hfutureP]
      simp [DemandNode.phaseFuture]
    have hinputE :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression e) .expression hchildE hphaseE).inputFuture =
          e.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change e.variables ++ transitionE.context.expected.frame.future =
        e.variables ++ context.expected.frame.future
      rw [transitionE.expectedFrameEq, DemandNode.phaseFrame_future transitionE.phaseFrameEq,
        hfutureE]
      simp [DemandNode.phaseFuture]
    rw [houtputP] at hFPlace
    rw [hinputE]
    exact hFPlace

private theorem statementAssignOpPlaceInputSubset
    {path : List Nat} {op : BinOp} {p : Place} {e : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.assignOp op p e o)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place p) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.assignOp op p e o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphase : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.assignOp op p e o).variables = p.variables ++ e.variables := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ p.variables ++
      (DemandNode.statement (.assignOp op p e o)).visibleForChild active 0 at hx
    have hchild : x ∈ p.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hx
    have hparent : x ∈ (p.variables ++ e.variables) ++ active := by
      rcases List.mem_append.mp hchild with hp | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.place p) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.assignOp op p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.assignOp op p e o)).visibleForChild
                context.expected.frame.active 0,
              e.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchild hphase).inputFuture =
        p.variables ++ (e.variables ++ context.expected.frame.future) := by
      change p.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture, List.append_assoc]
    intro x hx
    rw [hchildInput] at hx
    have hparent : x ∈ (p.variables ++ e.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hx with hp | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · rcases List.mem_append.mp rest with he | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _ he)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementAssignOpExprInputFrame
    {path : List Nat} {op : BinOp} {p : Place} {e : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.assignOp op p e o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFPlace : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.place p) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression e) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildP : (DemandNode.statement (.assignOp op p e o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseP : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildE : (DemandNode.statement (.assignOp op p e o)).child? 1 =
      some (DemandNode.expression e) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseE : DemandNodeHasPhase (DemandNode.expression e) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.place p).visibleAfter
        ((DemandNode.statement (.assignOp op p e o)).visibleForChild active 0)) at hFPlace
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFPlace
    have hchanged := hFactive.changeFuture (future' := e.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionP := context.child rfl 0 (DemandNode.place p) .place hchildP hphaseP
    let transitionE := context.child rfl 1 (DemandNode.expression e) .expression hchildE hphaseE
    have hexpectationP :
        (DemandNode.statement (.assignOp op p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.assignOp op p e o)).visibleForChild
                context.expected.frame.active 0,
              e.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP]
    have hexpectationE :
        (DemandNode.statement (.assignOp op p e o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.assignOp op p e o)).visibleForChild
                context.expected.frame.active 1,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
    have hfutureP := DemandNode.childFrame_future transitionP.childFrameEq hexpectationP
    have hfutureE := DemandNode.childFrame_future transitionE.childFrameEq hexpectationE
    have houtputP :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchildP hphaseP).outputFuture =
          e.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transitionP.context.expected.frame.future =
        e.variables ++ context.expected.frame.future
      rw [transitionP.expectedFrameEq, DemandNode.phaseFrame_future transitionP.phaseFrameEq,
        hfutureP]
      simp [DemandNode.phaseFuture]
    have hinputE :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression e) .expression hchildE hphaseE).inputFuture =
          e.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change e.variables ++ transitionE.context.expected.frame.future =
        e.variables ++ context.expected.frame.future
      rw [transitionE.expectedFrameEq, DemandNode.phaseFrame_future transitionE.phaseFrameEq,
        hfutureE]
      simp [DemandNode.phaseFuture]
    rw [houtputP] at hFPlace
    rw [hinputE]
    exact hFPlace

private theorem statementAppendPlaceInputSubset
    {path : List Nat} {p : Place} {v : View} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.append p v o)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place p) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.append p v o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphase : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.append p v o).variables = p.variables ++ v.variables := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ p.variables ++
      (DemandNode.statement (.append p v o)).visibleForChild active 0 at hx
    have hchild : x ∈ p.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hx
    have hparent : x ∈ (p.variables ++ v.variables) ++ active := by
      rcases List.mem_append.mp hchild with hp | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.place p) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.append p v o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.append p v o)).visibleForChild
                context.expected.frame.active 0,
              v.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchild hphase).inputFuture =
        p.variables ++ (v.variables ++ context.expected.frame.future) := by
      change p.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    intro x hx
    rw [hchildInput] at hx
    have hparent : x ∈ (p.variables ++ v.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hx with hp | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · rcases List.mem_append.mp rest with he | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _ he)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementPopNPlaceInputSubset
    {path : List Nat} {owner : Place} {count : Expr} {org : OriginId}
    (ec : EvaluationContext m plans path (.statement (.popN owner count org)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place owner) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.popN owner count org)).child? 0 =
      some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
  have hphase : DemandNodeHasPhase (DemandNode.place owner) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.popN owner count org).variables = owner.variables ++ count.variables := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ owner.variables ++
      (DemandNode.statement (.popN owner count org)).visibleForChild active 0 at hx
    have hchild : x ∈ owner.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hx
    have hparent : x ∈ (owner.variables ++ count.variables) ++ active := by
      rcases List.mem_append.mp hchild with howner | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ howner)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.place owner) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.popN owner count org)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.popN owner count org)).visibleForChild
                context.expected.frame.active 0,
              count.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place owner) .place hchild hphase).inputFuture =
        owner.variables ++ (count.variables ++ context.expected.frame.future) := by
      change owner.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp only [DemandNode.phaseFuture]
    intro x hx
    rw [hchildInput] at hx
    have hparent : x ∈ (owner.variables ++ count.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hx with howner | rest
      · exact List.mem_append_left _ (List.mem_append_left _ howner)
      · rcases List.mem_append.mp rest with hcount | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _ hcount)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementPopNCountInputFrame
    {path : List Nat} {owner : Place} {count : Expr} {org : OriginId}
    (ec : EvaluationContext m plans path (.statement (.popN owner count org)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFPlace : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.place owner) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression count) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildP : (DemandNode.statement (.popN owner count org)).child? 0 =
      some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseP : DemandNodeHasPhase (DemandNode.place owner) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildC : (DemandNode.statement (.popN owner count org)).child? 1 =
      some (DemandNode.expression count) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseC : DemandNodeHasPhase (DemandNode.expression count) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.place owner).visibleAfter
        ((DemandNode.statement (.popN owner count org)).visibleForChild active 0)) at hFPlace
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFPlace
    have hchanged := hFactive.changeFuture (future' := count.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionP := context.child rfl 0 (DemandNode.place owner) .place hchildP hphaseP
    let transitionC := context.child rfl 1 (DemandNode.expression count) .expression hchildC hphaseC
    have hexpectationP :
        (DemandNode.statement (.popN owner count org)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.popN owner count org)).visibleForChild
                context.expected.frame.active 0,
              count.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP]
    have hexpectationC :
        (DemandNode.statement (.popN owner count org)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.popN owner count org)).visibleForChild
                context.expected.frame.active 1,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildC]
    have hfutureP := DemandNode.childFrame_future transitionP.childFrameEq hexpectationP
    have hfutureC := DemandNode.childFrame_future transitionC.childFrameEq hexpectationC
    have houtputP :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place owner) .place hchildP hphaseP).outputFuture =
          count.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transitionP.context.expected.frame.future =
        count.variables ++ context.expected.frame.future
      rw [transitionP.expectedFrameEq, DemandNode.phaseFrame_future transitionP.phaseFrameEq,
        hfutureP]
      simp only [DemandNode.phaseFuture]
    have hinputC :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression count) .expression hchildC hphaseC).inputFuture =
          count.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change count.variables ++ transitionC.context.expected.frame.future =
        count.variables ++ context.expected.frame.future
      rw [transitionC.expectedFrameEq, DemandNode.phaseFrame_future transitionC.phaseFrameEq,
        hfutureC]
      simp only [DemandNode.phaseFuture]
    rw [houtputP] at hFPlace
    rw [hinputC]
    exact hFPlace

private theorem statementClearPlaceInputSubset
    {path : List Nat} {owner : Place} {org : OriginId}
    (ec : EvaluationContext m plans path (.statement (.clear owner org)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place owner) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  intro x hx
  cases ec with
  | pilot profile active =>
    change x ∈ owner.variables ++
      (DemandNode.statement (.clear owner org)).visibleForChild active 0 at hx
    simpa [EvaluationContext.inputFuture, DemandNode.variables,
      DemandNode.visibleForChild, Stmt.variables] using hx
  | shrink profile context =>
    rename_i stmtPlanContext
    have hchild : (DemandNode.statement (.clear owner org)).child? 0 =
        some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
    have hphase : DemandNodeHasPhase (DemandNode.place owner) .place := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let transition := context.child rfl 0 (DemandNode.place owner) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.clear owner org)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.clear owner org)).visibleForChild
                context.expected.frame.active 0,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place owner) .place hchild hphase).inputFuture =
        owner.variables ++ context.expected.frame.future := by
      change owner.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp only [DemandNode.phaseFuture]
    rw [hchildInput] at hx
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, Stmt.variables] using hx

private theorem statementAddShrinksOk (roots : List RootRef) (state : RState)
    (result : Unit × RState) (checked : addShrinks roots state = .ok result) :
    result.2.nextVar = state.nextVar ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ result.2.eff.shrinks := by
  unfold addShrinks addRoots at checked
  rw [st_modify_ok] at checked
  subst checked
  exact ⟨rfl, addTargets_right _ _⟩

private theorem statementTruncateGrowTotal {s : Store} {l : Loc}
    {len : Nat} {element : Ty}
    (owner : LocTy s l (.grow element))
    (bound : ∃ oldSize, s.length l = .ok oldSize ∧ len ≤ oldSize) :
    ∃ s', s.truncate l len = .ok s' := by
  obtain ⟨v, hread, hflat⟩ := owner
  cases v with
  | resizable storedElement values =>
    simp only [FlatTy] at hflat
    obtain ⟨rfl, hvalues⟩ := hflat
    obtain ⟨oldSize, hlength, hbound⟩ := bound
    have hlengthValues : oldSize = values.size := by
      have hlength' : s.length l = .ok values.size := by
        simp [Store.length, hread]
      rw [hlength'] at hlength
      exact (Except.ok.inj hlength).symm
    have hsize : len ≤ values.size := by omega
    have htruncateValue : Val.truncate len (.resizable element values) =
        some (.resizable element (values.extract 0 len)) := by
      simp [Val.truncate, hsize]
    obtain ⟨s', hmodify⟩ := modify_total s l (Val.truncate len)
      (.resizable element values) (.resizable element (values.extract 0 len)) hread htruncateValue
    exact ⟨s', by simpa [Store.truncate] using hmodify⟩
  | _ => simp [FlatTy] at hflat

private theorem statementTruncateGrowshrinkTotal {s : Store} {l : Loc}
    {len : Nat} {element : Ty}
    (owner : LocTy s l (.growshrink element))
    (bound : ∃ oldSize, s.length l = .ok oldSize ∧ len ≤ oldSize) :
    ∃ s', s.truncate l len = .ok s' := by
  obtain ⟨v, hread, hflat⟩ := owner
  cases v with
  | resizable storedElement values =>
    simp only [FlatTy] at hflat
    obtain ⟨rfl, hvalues⟩ := hflat
    obtain ⟨oldSize, hlength, hbound⟩ := bound
    have hlengthValues : oldSize = values.size := by
      have hlength' : s.length l = .ok values.size := by
        simp [Store.length, hread]
      rw [hlength'] at hlength
      exact (Except.ok.inj hlength).symm
    have hsize : len ≤ values.size := by omega
    have htruncateValue : Val.truncate len (.resizable element values) =
        some (.resizable element (values.extract 0 len)) := by
      simp [Val.truncate, hsize]
    obtain ⟨s', hmodify⟩ := modify_total s l (Val.truncate len)
      (.resizable element values) (.resizable element (values.extract 0 len)) hread htruncateValue
    exact ⟨s', by simpa [Store.truncate] using hmodify⟩
  | _ => simp [FlatTy] at hflat

private theorem statementTruncateLimitedTotal {s : Store} {l : Loc}
    {len : Nat} {element : Ty} {capacity : Nat}
    (owner : LocTy s l (.limited element capacity))
    (bound : ∃ oldSize, s.length l = .ok oldSize ∧ len ≤ oldSize) :
    ∃ s', s.truncate l len = .ok s' := by
  obtain ⟨v, hread, hflat⟩ := owner
  cases v with
  | limited storedElement storedCapacity slots currentLen =>
    simp only [FlatTy] at hflat
    obtain ⟨rfl, rfl, hcapacity, hcurrentSlots, hslots⟩ := hflat
    obtain ⟨oldSize, hlength, hbound⟩ := bound
    have hlengthCurrent : oldSize = currentLen := by
      have hlength' : s.length l = .ok currentLen := by
        simp [Store.length, hread]
      rw [hlength'] at hlength
      exact (Except.ok.inj hlength).symm
    have hsize : len ≤ currentLen := by omega
    have htruncateValue : Val.truncate len (.limited element capacity slots currentLen) =
        some (.limited element capacity slots len) := by
      simp [Val.truncate, hsize]
    obtain ⟨s', hmodify⟩ := modify_total s l (Val.truncate len)
      (.limited element capacity slots currentLen) (.limited element capacity slots len) hread htruncateValue
    exact ⟨s', by simpa [Store.truncate] using hmodify⟩
  | _ => simp [FlatTy] at hflat

private theorem statementTruncateOwnerTotal {s : Store} {l : Loc} {t element : Ty}
    (owner : LocTy s l t) (hasElement : t.ownerElem? = some element) :
    ∃ s', s.truncate l 0 = .ok s' := by
  revert owner
  cases t with
  | grow storedElement =>
    intro owner
    simp only [Ty.ownerElem?] at hasElement
    obtain ⟨v, hread, hflat⟩ := owner
    cases v with
    | resizable actual values =>
      simp only [FlatTy] at hflat
      obtain ⟨rfl, hvalues⟩ := hflat
      have hlength : s.length l = .ok values.size := by simp [Store.length, hread]
      have owner' : LocTy s l (.grow storedElement) := by
        refine ⟨.resizable storedElement values, hread, ?_⟩
        simp only [FlatTy]
        exact ⟨by simp, hvalues⟩
      exact statementTruncateGrowTotal owner' ⟨values.size, hlength, Nat.zero_le _⟩
    | _ => simp [FlatTy] at hflat
  | growshrink storedElement =>
    intro owner
    simp only [Ty.ownerElem?] at hasElement
    obtain ⟨v, hread, hflat⟩ := owner
    cases v with
    | resizable actual values =>
      simp only [FlatTy] at hflat
      obtain ⟨rfl, hvalues⟩ := hflat
      have hlength : s.length l = .ok values.size := by simp [Store.length, hread]
      have owner' : LocTy s l (.growshrink storedElement) := by
        refine ⟨.resizable storedElement values, hread, ?_⟩
        simp only [FlatTy]
        exact ⟨by simp, hvalues⟩
      exact statementTruncateGrowshrinkTotal owner' ⟨values.size, hlength, Nat.zero_le _⟩
    | _ => simp [FlatTy] at hflat
  | limited storedElement capacity =>
    intro owner
    simp only [Ty.ownerElem?] at hasElement
    obtain ⟨v, hread, hflat⟩ := owner
    cases v with
    | limited actual actualCapacity slots currentLen =>
      simp only [FlatTy] at hflat
      obtain ⟨rfl, rfl, hcapacity, hcurrentSlots, hslots⟩ := hflat
      have hlength : s.length l = .ok currentLen := by simp [Store.length, hread]
      have owner' : LocTy s l (.limited storedElement capacity) := by
        refine ⟨.limited storedElement capacity slots currentLen, hread, ?_⟩
        simp only [FlatTy]
        exact ⟨by simp, by simp, hcapacity, hcurrentSlots, hslots⟩
      exact statementTruncateLimitedTotal owner' ⟨currentLen, hlength, Nat.zero_le _⟩
    | _ => simp [FlatTy] at hflat
  | _ => simp [Ty.ownerElem?] at hasElement

private theorem statementDirectShrinkAuthority
    {m : Module} {plans : Array (Array DemandPoint)} {pc : PlanContext m plans}
    {path : List Nat} {node : DemandNode} {ownerPlace : Place} {request : DemandOwner}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St} {future : List VarId}
    {l : Loc} {element ownerType : Ty} {rho : List RootRef} {observation : Observation}
    (context : NodeContext pc path node .mutation) (profile : m.profile = .shrink)
    (direct : node.directShrinkPlace? = some ownerPlace)
    (query : pc.approvals.access.owner ownerPlace = .ok request)
    (requestType : request.ty = some ownerType)
    (resizable : ownerType = .grow element ∨ ownerType = .growshrink element)
    (requestRoot : Gam env W.ownerP request.roots l.root)
    (ownerRoot : Gam env W.ownerP rho l.root)
    (frame : Frame m W tenv penv env s future) (permission : Perm m W)
    (classified : ClassifiedParameters m W.P W.D observation s.store)
    (observed : Observed m W.G observation s.store)
    (header : l.path = []) (typed : LocTy s.store l ownerType)
    (recorded : ∀ t, t ∈ rootsTargets rho → t ∈ W.E.shrinks) :
    ((EvaluationContext.shrink profile context).mayShrink W.ownerP observation l.root ∨
      ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
      (∀ g, l.root = .global g → g < W.G) := by
  have ownerG : LocTy s.store l (.grow element) := by
    rcases resizable with heq | heq
    · cases heq; exact typed
    · cases heq; exact typed.growshrink_to_grow
  have globals := frame.ownerGlobalAuthority (observation := observation) permission ownerRoot
    header (Or.inl ownerG) (fun t ht => Or.inr (Or.inr (Or.inr (recorded t ht))))
  refine ⟨?_, fun g hg => (globals g hg).1⟩
  by_cases current : ∃ a si x, l.root = .local a si x ∧ W.base ≤ si
  · exact Or.inr current
  have localAge : ∀ x, RootIn env W.ownerP l.root (.local x) → False := by
    intro x hx
    obtain ⟨lv, si, hvar, hscope, hroot⟩ := hx
    obtain ⟨before, after, hscopes, _⟩ := List.lookup_eq_some_iff.mp hscope
    have hmem : (lv.scope, si) ∈ env.scopes := by
      rw [hscopes]
      exact List.mem_append_right _ List.mem_cons_self
    exact current ⟨env.act, si, x, hroot, (frame.below _ hmem).1⟩
  have external : Gam noEnv W.ownerP request.roots l.root := by
    obtain ⟨q, hq, hroot⟩ := requestRoot
    refine ⟨q, hq, ?_⟩
    cases q with
    | «local» x => exact False.elim (localAge x hroot)
    | global g => exact hroot
    | param i => exact hroot
  have capability : OwnerCap m observation l.root := by
    cases hroot : l.root with
    | global g => exact (globals g hroot).2
    | «local» a si x =>
      obtain ⟨q, hq, hdenotes⟩ := ownerRoot
      cases q with
      | «local» y => exact False.elim (localAge y hdenotes)
      | global g => rw [hroot] at hdenotes; cases hdenotes
      | param i =>
        have param : W.P i (.local a si x) := frame.ownerSubset i _ (hroot ▸ hdenotes)
        have location : l = ⟨.local a si x, []⟩ := by cases l; simp_all
        have localOwner : LocTy s.store ⟨.local a si x, []⟩ (.grow element) := location ▸ ownerG
        exact ClassifiedParameters.localOwner classified observed
          (fun r E hd => by obtain ⟨v, hv, ht, _⟩ := frame.sa r E hd; exact ⟨v, hv, ht⟩)
          param localOwner
  have invalidates : request.invalidates = true := by
    rcases resizable with heq | heq <;> cases heq <;>
      simp [DemandOwner.invalidates, requestType]
  have requestMember : request ∈ context.expected.shrinkOwners :=
    context.sourceAt.directShrinkOwner rfl direct pc.approvals.accessMatches query
  have expectedPhase : context.expected.phase = .mutation := by
    rcases context.sourceAt with ⟨_, _, _, _, _, hphase⟩
    exact hphase
  have may : PlanMayShrink pc W.ownerP l.root :=
    PlanMayShrink.ofExpected context.member expectedPhase requestMember ⟨invalidates, external⟩
  exact Or.inl ⟨may, capability⟩


private theorem statementResizableTruncatePreservation
    {ownerIndex : Nat} {plan : Array DemandPoint}
    {approval : DemandShrinkApproval m ownerIndex plan}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {state : St}
    {future : List VarId} {shrinking : RootInst → Prop} {observation : Observation}
    {destination : Store} {l : Loc} {len : Nat} {element ownerType : Ty}
    {aliases : List RetainedAlias}
    (frame : Frame m W tenv penv env state future)
    (accessEq : approval.access = penv.access)
    (ownerTy : approval.shrinkOwner.ty = some ownerType)
    (resizable : ownerType = .grow element ∨ ownerType = .growshrink element)
    (ownerRoot : Gam env W.P approval.shrinkOwner.roots l.root)
    (ownerLoc : LocTy state.store l ownerType)
    (visibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active)
    (futureNeeded : ∀ x, x ∈ future → x ∈ approval.point.future)
    (profile : m.profile = .shrink)
    (hprotected : ShrinkProtected W.D W.A shrinking)
    (observed : ObservedSafe m W shrinking observation state.store)
    (authority : shrinking l.root ∨ ∃ a si x, l.root = .local a si x ∧ W.base ≤ si)
    (header : l.path = []) (flat : element.flat = true)
    (bound : ∀ g, l.root = .global g → g < W.G)
    (retained : ∀ alias, alias ∈ aliases → alias ∈ approval.point.retained)
    (truncate : state.store.truncate l len = .ok destination) :
    Frame m W tenv penv env { state with store := destination } future ∧
      Footprint (insts env) (Dset W) state { state with store := destination } ∧
      PreservesRootTypes m W.G observation.roots state.store destination ∧
      PreservesValues m W.G observation.values state.store destination ∧
      ObservedSafe m W shrinking observation destination ∧
      RetainsAliases m W env state.store destination aliases ∧
      PilotStoreLe m state { state with store := destination } := by
  have ownerGS : LocTy state.store l (.growshrink element) := by
    rcases resizable with heq | heq
    · cases heq; exact ownerLoc.grow_to_growshrink
    · cases heq; exact ownerLoc
  obtain ⟨postFrame, footprint, pilot⟩ := frame.truncateGrowshrinkPreservation accessEq
    ownerTy resizable ownerRoot ownerLoc visibleActive futureNeeded profile hprotected authority truncate
  obtain ⟨roots, values, safe⟩ := frame.truncateGrowshrinkObservations observed authority
    header ownerGS truncate
  have ownerApproval : approval.shrinkOwner.ty = some (.grow element) ∨
      approval.shrinkOwner.ty = some (.growshrink element) := by
    rcases resizable with heq | heq
    · exact Or.inl (heq ▸ ownerTy)
    · exact Or.inr (heq ▸ ownerTy)
  have retains := (shrinkApproval_retainsGrowshrinkAliases frame ownerApproval ownerRoot
    bound header flat ownerGS truncate).subset retained
  exact ⟨postFrame, footprint, roots, values, safe, retains, pilot⟩

private theorem statementOwnerElementFlat
    {W : World} {penv : PEnv} {env : Env} {store : Store} {owner : Place}
    {l : Loc} {t element : Ty}
    (hplace : PlaceOk m W.G W.P penv env store owner l t)
    (howner : t.ownerElem? = some element) : element.flat = true := by
  rcases hplace with ⟨href, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, hRefLike, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, htype, _, _, _, _, _⟩
  · cases t <;> simp_all [Ty.ownerElem?, Ty.refTarget]
  · cases t <;> simp_all [Ty.ownerElem?, Ty.isRefLike]
  · rw [htype] at howner
    simp [Ty.ownerElem?] at howner

private theorem statementCheckedShrinkOwnerFacts
    {accessEnv : AccessEnv} {tenv : TEnv} {penv : PEnv} {ownerPlace : Place}
    {owner : DemandOwner} {t : Ty} {bindingWritable contentsWritable : Bool}
    {tn tn' : Nat} {rst rst' : RState} {rho : List RootRef}
    {env : Env} {W : World} {P : Nat → RootInst → Prop} {root : RootInst}
    (haccess : accessEnv.mod = tenv.mod ∧ accessEnv.impl.vars = tenv.vars ∧
      accessEnv.mod = penv.mod ∧ accessEnv.impl = penv.impl ∧ accessEnv.ctx = penv.ctx)
    (hquery : accessEnv.owner ownerPlace = .ok owner)
    (ht : tyPlace tenv ownerPlace tn = .ok (⟨t, bindingWritable, contentsWritable⟩, tn'))
    (hr : rpPlace penv ownerPlace rst = .ok (rho, rst'))
    (hgam : Gam env P rho root) :
    accessEnv = penv.access ∧ owner.ty = some t ∧ Gam env P owner.roots root := by
  have hmod : tenv.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
  have hvars : tenv.vars = penv.impl.vars :=
    haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
  have henv : accessEnv = penv.access := by
    cases accessEnv
    unfold PEnv.access
    congr 1
    · exact haccess.2.2.1
    · exact haccess.2.2.2.1
    · exact haccess.2.2.2.2
  rw [henv] at hquery
  have htype := tyPlace_accessType hmod hvars ht
  simp only [AccessEnv.owner, htype] at hquery
  cases hroots : penv.access.placeRoots ownerPlace with
  | error err => simp [hroots, Functor.map, Except.map] at hquery
  | ok roots =>
    simp [hroots, Functor.map, Except.map] at hquery
    subst owner
    exact ⟨henv, rfl, hgam.subset (rpPlace_accessRoots penv ownerPlace rst rho rst' roots hr hroots)⟩

theorem statementAssignWholeClearFrame
    {path : List Nat} {owner : Place} {replacement : Expr} {org : OriginId}
    {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {sPlace : St}
    {element target : Ty} {binding contents : Bool} {tn middle : Nat}
    {rst r1 : RState} {ownerRoots : List RootRef} {location : Loc}
    {observation : Observation} {destination : Store}
    (ec : EvaluationContext m plans path (.statement (.assignWhole owner replacement org)) .statement)
    (hmProfile : m.profile = .shrink)
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hp : Perm m W)
    (htarget : target = .grow element ∨ target = .growshrink element)
    (hownerTy : tyPlace tenv owner tn = .ok (⟨target, binding, contents⟩, middle))
    (hownerRp : rpPlace penv owner rst = .ok (ownerRoots, r1))
    (hplace : PlaceOk m W.G W.P penv env sPlace.store owner location target)
    (hownerLoc : LocTy sPlace.store location target)
    (hgamPlace : Gam env W.P ownerRoots location.root)
    (hownerP : Gam env W.ownerP ownerRoots location.root)
    (hrecorded : ∀ t, t ∈ rootsTargets ownerRoots → t ∈ W.E.shrinks)
    (hFPlace : Frame m W tenv penv env sPlace
      (ec.child rfl 0 (.place owner) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture)
    (hsafePlace : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation sPlace.store)
    (hclassifiedPlace : ClassifiedParameters m W.P W.D observation sPlace.store)
    (htruncate : sPlace.store.truncate location 0 = .ok destination) :
    ∃ ownerRequest : DemandOwner,
      ec.access? = some penv.access ∧ penv.access.owner owner = .ok ownerRequest ∧
      ownerRequest.ty = some target ∧ Gam env W.P ownerRequest.roots location.root ∧
      penv.access.placeRoots owner = .ok ownerRequest.roots ∧
      Frame m W tenv penv env { sPlace with store := destination }
        (ec.child rfl 1 (.expression replacement) .expression
          (by simp [DemandNode.child?, DemandNode.children])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture ∧
      Footprint (insts env) (Dset W) sPlace { sPlace with store := destination } ∧
      PreservesRootTypes m W.G observation.roots sPlace.store destination ∧
      PreservesValues m W.G observation.values sPlace.store destination ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation destination ∧
      RetainsAliases m W env sPlace.store destination ec.retained ∧
      PilotStoreLe m sPlace { sPlace with store := destination } ∧
      ClassifiedParameters m W.P W.D observation destination := by
    have hchildE : (DemandNode.statement (.assignWhole owner replacement org)).child? 1 =
        some (.expression replacement) := by simp [DemandNode.child?, DemandNode.children]
    have hphaseE : DemandNodeHasPhase (.expression replacement) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 1 replacement hchildE
    have hFExprInput := statementAssignWholeExprInputFrame ec hactive hFPlace
    have hownerElem : target.ownerElem? = some element := by
      rcases htarget with rfl | rfl <;> simp [Ty.ownerElem?]
    have hheader : location.path = [] := hplace.ownerHeader (by simp [hownerElem])
    have hflat : element.flat = true := statementOwnerElementFlat hplace hownerElem
    have hinputE : childEc.inputFuture = replacement.variables ++ ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change replacement.variables ++
          (DemandNode.statement (.assignWhole owner replacement org)).visibleForChild active 1 =
          replacement.variables ++
            (DemandNode.statement (.assignWhole owner replacement org)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 1 (DemandNode.expression replacement) .expression
          hchildE hphaseE
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.assignWhole owner replacement org))
            stmtPlanContext.approvals.access
            ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 1 = some ⟨
                (DemandNode.statement (.assignWhole owner replacement org)).visibleForChild
                  context.expected.frame.active 1,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change replacement.variables ++ transition.context.expected.frame.future =
          replacement.variables ++ context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    have hmutationPhase : DemandNodeHasPhase
        (DemandNode.statement (.assignWhole owner replacement org)) .mutation := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let mutationEc := statementMutationContext ec hmutationPhase
    have hmutationFuture : mutationEc.outputFuture = childEc.inputFuture := by
      rw [hinputE]
      cases ec with
      | pilot pilotProfile active =>
        have hfalse : False := by
          rw [hmProfile] at pilotProfile
          cases pilotProfile
        exact hfalse.elim
      | shrink profile context =>
        have hout := EvaluationContext.phase_outputFuture
          (parent := EvaluationContext.shrink profile context) rfl .mutation hmutationPhase
        simpa [mutationEc, statementMutationContext, DemandNode.phaseFuture,
          EvaluationContext.outputFuture, NodeContext.outputFuture] using hout
    have haccessMutation :=
      (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
    have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
    have hretainedMutation : ∀ alias, alias ∈ ec.retained → alias ∈ mutationEc.retained := by
      intro alias hmem
      exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
    change mutationEc.AccessMatches tenv penv at haccessMutation
    change mutationEc.ActiveMatches tenv at hactiveMutation
    cases hmutation : mutationEc with
    | pilot pilotProfile active =>
      have hfalse : False := by
        rw [hmProfile] at pilotProfile
        cases pilotProfile
      exact hfalse.elim
    | @shrink pc profile mutationContext =>
      rw [hmutation] at haccessMutation hactiveMutation hretainedMutation hmutationFuture
      have hdirect :
          (DemandNode.statement (.assignWhole owner replacement org)).directShrinkPlace? =
            some owner := by simp [DemandNode.directShrinkPlace?]
      obtain ⟨ownerRequest, hownerResult, _⟩ :=
        mutationContext.sourceAt.directShrinkOwner_result rfl hdirect pc.approvals.accessMatches
      obtain ⟨approval, _, hsameOwner, _, happrovalFrame⟩ :=
        mutationContext.directShrinkApproval hdirect hownerResult
      have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
        haccessMutation hownerResult hownerTy hownerRp hgamPlace
      have hownerFactsP := statementCheckedShrinkOwnerFacts (W := W)
        haccessMutation hownerResult hownerTy hownerRp hownerP
      have hcheckedFacts := statementAssignWholeCheckedOwnerFacts
        haccessMutation hownerResult hownerTy hownerRp
      have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
        intro x hx
        exact (happrovalFrame.1 x).2 ((hactiveMutation x).2 hx)
      have hfutureNeeded : ∀ x, x ∈ childEc.inputFuture →
          x ∈ approval.point.future := by
        intro x hx
        apply (happrovalFrame.2.1 x).2
        have hx' : x ∈ (EvaluationContext.shrink profile mutationContext).outputFuture := by
          rw [hmutationFuture]
          exact hx
        exact hx'
      have happrovalAccess : approval.access = pc.approvals.access :=
        Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
      have haccessEq : approval.access = penv.access := happrovalAccess.trans hownerFacts.1
      have happrovalTy : approval.shrinkOwner.ty = some target := by
        rw [hsameOwner]
        exact hownerFacts.2.1
      have happrovalRoot : Gam env W.P approval.shrinkOwner.roots location.root := by
        rw [hsameOwner]
        exact hownerFacts.2.2
      have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
          alias ∈ approval.point.retained := by
        intro alias hmem
        exact (happrovalFrame.2.2 alias).2 (hretainedMutation alias hmem)
      have hauthority := statementDirectShrinkAuthority mutationContext profile hdirect
        hownerResult hownerFactsP.2.1 htarget hownerFactsP.2.2 hownerP hFExprInput hp
        hclassifiedPlace hsafePlace.typed hheader hownerLoc
        hrecorded
      have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
        W.ownerP observation location.root
      change mutationEc.mayShrink W.ownerP observation location.root ↔
        ec.mayShrink W.ownerP observation location.root at hmay
      rw [hmutation] at hmay
      have hauthority' : ec.mayShrink W.ownerP observation location.root ∨
          ∃ a si x, location.root = .local a si x ∧ W.base ≤ si :=
        hauthority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr
      obtain ⟨hFClear, hfootClear, hrootsClear, hvaluesClear, hsafeClear,
        hretainedClear, hpilotClear⟩ :=
        statementResizableTruncatePreservation hFExprInput haccessEq happrovalTy
          htarget happrovalRoot hownerLoc hvisibleActive hfutureNeeded profile hprotected
          hsafePlace hauthority' hheader hflat hauthority.2 hretainedNeeded htruncate
      have haccessSome : ec.access? = some penv.access := by
        have hphaseAccess : mutationEc.access? = ec.access? := by
          cases ec <;> rfl
        rw [← hphaseAccess, hmutation]
        exact congrArg some hownerFacts.1
      have hownerResultP : penv.access.owner owner = .ok ownerRequest := by
        rw [← hownerFacts.1]
        exact hownerResult
      have hcheckedRoots : penv.access.placeRoots owner = .ok ownerRequest.roots := by
        rw [← hcheckedFacts.1]
        exact hcheckedFacts.2.2.1
      exact ⟨ownerRequest, haccessSome, hownerResultP, hownerFacts.2.1,
        hownerFacts.2.2, hcheckedRoots, hFClear, hfootClear, hrootsClear, hvaluesClear,
        hsafeClear, hretainedClear, hpilotClear,
        hFExprInput.classifiedParameters_advance hclassifiedPlace hfootClear⟩

private theorem statementTruncateLimitedFlatStep {s s' : Store} {l : Loc}
    {len : Nat} {element : Ty} {capacity : Nat}
    (owner : LocTy s l (.limited element capacity))
    (htruncate : s.truncate l len = .ok s') : FlatStep s s' := by
  obtain ⟨_, slots, old, hread, hlen, _, _, _, _, _⟩ :=
    truncate_limited_step s s' l len element capacity owner htruncate
  apply flatStep_modify s s' l (Val.truncate len)
    (.limited element capacity slots old) htruncate hread (by simp [IsRef])
  intro value hvalue
  have hshape : Val.truncate len (.limited element capacity slots old) =
      some (.limited element capacity slots len) := by simp [Val.truncate, hlen]
  rw [hshape] at hvalue
  cases hvalue
  exact ⟨by simp [IsRef], refines_limitedTruncate element capacity slots old len hlen⟩

private theorem sat_statementTruncateLoc {s : St} {l : Loc} {len : Nat}
    {Q : Unit → St → Prop} {s' : Store}
    (htruncate : s.store.truncate l len = .ok s')
    (result : Q () { s with store := s' }) :
    Sat (truncateLoc l len) s Q := by
  unfold Sat truncateLoc
  simp [htruncate, result]

private theorem sat_statementTruncateLoc_bind {s : St} {l : Loc} {len : Nat}
    {Q : α → St → Prop} {s' : Store} {f : Unit → M α}
    (htruncate : s.store.truncate l len = .ok s')
    (result : Sat (f ()) { s with store := s' } Q) :
    Sat (truncateLoc l len >>= f) s Q := by
  have heq : (truncateLoc l len >>= f) s = f () { s with store := s' } := by
    show M.bind' (truncateLoc l len) f s = _
    simp [M.bind', truncateLoc, htruncate]
  unfold Sat
  rw [heq]
  exact result

private theorem statementAppendViewInputFrame
    {path : List Nat} {p : Place} {v : View} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.append p v o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFPlace : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.place p) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.view v) .view
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildP : (DemandNode.statement (.append p v o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseP : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildV : (DemandNode.statement (.append p v o)).child? 1 =
      some (DemandNode.view v) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseV : DemandNodeHasPhase (DemandNode.view v) .view := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.place p).visibleAfter
        ((DemandNode.statement (.append p v o)).visibleForChild active 0)) at hFPlace
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFPlace
    have hchanged := hFactive.changeFuture (future' := v.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionP := context.child rfl 0 (DemandNode.place p) .place hchildP hphaseP
    let transitionV := context.child rfl 1 (DemandNode.view v) .view hchildV hphaseV
    have hexpectationP :
        (DemandNode.statement (.append p v o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.append p v o)).visibleForChild
                context.expected.frame.active 0,
              v.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP]
    have hexpectationV :
        (DemandNode.statement (.append p v o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.append p v o)).visibleForChild
                context.expected.frame.active 1,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildV]
    have hfutureP := DemandNode.childFrame_future transitionP.childFrameEq hexpectationP
    have hfutureV := DemandNode.childFrame_future transitionV.childFrameEq hexpectationV
    have houtputP :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchildP hphaseP).outputFuture =
          v.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transitionP.context.expected.frame.future =
        v.variables ++ context.expected.frame.future
      rw [transitionP.expectedFrameEq, DemandNode.phaseFrame_future transitionP.phaseFrameEq,
        hfutureP]
      simp [DemandNode.phaseFuture]
    have hinputV :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.view v) .view hchildV hphaseV).inputFuture =
          v.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change v.variables ++ transitionV.context.expected.frame.future =
        v.variables ++ context.expected.frame.future
      rw [transitionV.expectedFrameEq, DemandNode.phaseFrame_future transitionV.phaseFrameEq,
        hfutureV]
      simp [DemandNode.phaseFuture]
    rw [houtputP] at hFPlace
    rw [hinputV]
    exact hFPlace

private theorem statementResizePlaceInputSubset
    {path : List Nat} {p : Place} {size : Expr} {fill : Option Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.resize p size fill o)) .statement) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.place p) .place
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.resize p size fill o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphase : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.resize p size fill o).variables =
      p.variables ++ (size.variables ++ fill.toList.flatMap Expr.variables) := by
    cases fill with
    | none => simp [Stmt.variables]
    | some e => simp [Stmt.variables, List.flatMap, List.append_assoc]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ p.variables ++
      (DemandNode.statement (.resize p size fill o)).visibleForChild active 0 at hx
    have hchild : x ∈ p.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hx
    have hparent : x ∈ (p.variables ++ size.variables ++
        fill.toList.flatMap Expr.variables) ++ active := by
      rcases List.mem_append.mp hchild with hp | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hp))
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables,
      List.append_assoc] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.place p) .place hchild hphase
    have hexpectation :
        (DemandNode.statement (.resize p size fill o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.resize p size fill o)).visibleForChild
                context.expected.frame.active 0,
              size.variables ++ fill.toList.flatMap Expr.variables ++
                context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchild hphase).inputFuture =
        p.variables ++ (size.variables ++ fill.toList.flatMap Expr.variables ++
          context.expected.frame.future) := by
      change p.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture, List.append_assoc]
    intro x hx
    rw [hchildInput] at hx
    have hparent : x ∈ (p.variables ++ size.variables ++
        fill.toList.flatMap Expr.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hx with hp | rest
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hp))
      · rcases List.mem_append.mp rest with hsf | hfuture
        · rcases List.mem_append.mp hsf with hs | hf
          · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
          · exact List.mem_append_left _ (List.mem_append_right _ hf)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables, List.append_assoc] using hparent

private theorem statementResizeSizeInputFrame
    {path : List Nat} {p : Place} {size : Expr} {fill : Option Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.resize p size fill o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFPlace : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.place p) .place
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression size) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildP : (DemandNode.statement (.resize p size fill o)).child? 0 =
      some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseP : DemandNodeHasPhase (DemandNode.place p) .place := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildS : (DemandNode.statement (.resize p size fill o)).child? 1 =
      some (DemandNode.expression size) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseS : DemandNodeHasPhase (DemandNode.expression size) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let fillVariables := fill.toList.flatMap Expr.variables
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.place p).visibleAfter
        ((DemandNode.statement (.resize p size fill o)).visibleForChild active 0)) at hFPlace
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFPlace
    have hchanged := hFactive.changeFuture (future' := size.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionP := context.child rfl 0 (DemandNode.place p) .place hchildP hphaseP
    let transitionS := context.child rfl 1 (DemandNode.expression size) .expression hchildS hphaseS
    have hexpectationP :
        (DemandNode.statement (.resize p size fill o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.resize p size fill o)).visibleForChild
                context.expected.frame.active 0,
              size.variables ++ fillVariables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP,
        fillVariables, List.append_assoc]
    have hexpectationS :
        (DemandNode.statement (.resize p size fill o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.resize p size fill o)).visibleForChild
                context.expected.frame.active 1,
              fillVariables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildS,
        fillVariables, List.append_assoc]
    have hfutureP := DemandNode.childFrame_future transitionP.childFrameEq hexpectationP
    have hfutureS := DemandNode.childFrame_future transitionS.childFrameEq hexpectationS
    have houtputP :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.place p) .place hchildP hphaseP).outputFuture =
          size.variables ++ (fillVariables ++ (EvaluationContext.shrink profile context).outputFuture) := by
      change transitionP.context.expected.frame.future = _
      rw [transitionP.expectedFrameEq, DemandNode.phaseFrame_future transitionP.phaseFrameEq]
      simpa [fillVariables, List.append_assoc, EvaluationContext.outputFuture,
        NodeContext.outputFuture, DemandNode.phaseFuture] using hfutureP
    have hinputS :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression size) .expression hchildS hphaseS).inputFuture =
          size.variables ++ (fillVariables ++ (EvaluationContext.shrink profile context).outputFuture) := by
      change size.variables ++ transitionS.context.expected.frame.future = _
      rw [transitionS.expectedFrameEq, DemandNode.phaseFrame_future transitionS.phaseFrameEq]
      simpa [fillVariables, List.append_assoc, EvaluationContext.outputFuture,
        NodeContext.outputFuture, DemandNode.phaseFuture] using
        congrArg (fun xs => size.variables ++ xs) hfutureS
    rw [houtputP] at hFPlace
    rw [hinputS]
    exact hFPlace

private theorem statementResizeFillInputFrame
    {path : List Nat} {p : Place} {size fill : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.resize p size (some fill) o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFSize : Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression size) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 2 (DemandNode.expression fill) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildS : (DemandNode.statement (.resize p size (some fill) o)).child? 1 =
      some (DemandNode.expression size) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseS : DemandNodeHasPhase (DemandNode.expression size) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildF : (DemandNode.statement (.resize p size (some fill) o)).child? 2 =
      some (DemandNode.expression fill) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseF : DemandNodeHasPhase (DemandNode.expression fill) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.expression size).visibleAfter
        ((DemandNode.statement (.resize p size (some fill) o)).visibleForChild active 1)) at hFSize
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFSize
    have hchanged := hFactive.changeFuture (future' := fill.variables ++ active) (by
      intro x hxvisible _
      exact (hactive x).2 hxvisible)
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleAfter, DemandNode.visibleForChild] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionS := context.child rfl 1 (DemandNode.expression size) .expression hchildS hphaseS
    let transitionF := context.child rfl 2 (DemandNode.expression fill) .expression hchildF hphaseF
    have hexpectationS :
        (DemandNode.statement (.resize p size (some fill) o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.resize p size (some fill) o)).visibleForChild
                context.expected.frame.active 1,
              fill.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildS]
    have hexpectationF :
        (DemandNode.statement (.resize p size (some fill) o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 2 = some ⟨
              (DemandNode.statement (.resize p size (some fill) o)).visibleForChild
                context.expected.frame.active 2,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildF]
    have hfutureS := DemandNode.childFrame_future transitionS.childFrameEq hexpectationS
    have hfutureF := DemandNode.childFrame_future transitionF.childFrameEq hexpectationF
    have houtputS :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression size) .expression hchildS hphaseS).outputFuture =
          fill.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transitionS.context.expected.frame.future = fill.variables ++ context.expected.frame.future
      rw [transitionS.expectedFrameEq, DemandNode.phaseFrame_future transitionS.phaseFrameEq]
      simpa [DemandNode.phaseFuture] using hfutureS
    have hinputF :
        ((EvaluationContext.shrink profile context).child rfl 2
          (DemandNode.expression fill) .expression hchildF hphaseF).inputFuture =
          fill.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change fill.variables ++ transitionF.context.expected.frame.future =
        fill.variables ++ context.expected.frame.future
      rw [transitionF.expectedFrameEq, DemandNode.phaseFrame_future transitionF.phaseFrameEq]
      exact congrArg (fun xs => fill.variables ++ xs) hfutureF
    rw [houtputS] at hFSize
    rw [hinputF]
    exact hFSize

private theorem statementResizeFillOutputFuture
    {path : List Nat} {p : Place} {size fill : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.resize p size (some fill) o)) .statement) :
    (ec.child rfl 2 (DemandNode.expression fill) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture = ec.outputFuture := by
  have hchildF : (DemandNode.statement (.resize p size (some fill) o)).child? 2 =
      some (DemandNode.expression fill) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseF : DemandNodeHasPhase (DemandNode.expression fill) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active => rfl
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionF := context.child rfl 2 (DemandNode.expression fill) .expression hchildF hphaseF
    have hexpectationF :
        (DemandNode.statement (.resize p size (some fill) o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 2 = some ⟨
              (DemandNode.statement (.resize p size (some fill) o)).visibleForChild
                context.expected.frame.active 2,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildF]
    have hfutureF := DemandNode.childFrame_future transitionF.childFrameEq hexpectationF
    change transitionF.context.expected.frame.future = context.expected.frame.future
    rw [transitionF.expectedFrameEq, DemandNode.phaseFrame_future transitionF.phaseFrameEq]
    exact hfutureF

private theorem statementResizeSizeOutputFuture
    {path : List Nat} {p : Place} {size : Expr} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.resize p size none o)) .statement) :
    (ec.child rfl 1 (DemandNode.expression size) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture = ec.outputFuture := by
  have hchildS : (DemandNode.statement (.resize p size none o)).child? 1 =
      some (DemandNode.expression size) := by simp [DemandNode.child?, DemandNode.children]
  have hphaseS : DemandNodeHasPhase (DemandNode.expression size) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active => rfl
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionS := context.child rfl 1 (DemandNode.expression size) .expression hchildS hphaseS
    have hexpectationS :
        (DemandNode.statement (.resize p size none o)).childExpectation?
          stmtPlanContext.approvals.access
          ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.resize p size none o)).visibleForChild
                context.expected.frame.active 1,
              context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildS]
    have hfutureS := DemandNode.childFrame_future transitionS.childFrameEq hexpectationS
    change transitionS.context.expected.frame.future = context.expected.frame.future
    rw [transitionS.expectedFrameEq, DemandNode.phaseFrame_future transitionS.phaseFrameEq]
    exact hfutureS

private theorem frameTopAtFuture {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} (hF : Frame m W tenv penv env s future) {sc : Nat}
    (hsc : tenv.scopes.head? = some sc) :
    ∃ si rest, env.scopes = (sc, si) :: rest ∧ env.scopes.lookup sc = some si := by
  rw [hF.scopes_t] at hsc
  cases hs : env.scopes with
  | nil => simp [hs] at hsc
  | cons p rest =>
    obtain ⟨scope, si⟩ := p
    simp only [hs, List.map_cons, List.head?_cons, Option.some.injEq] at hsc
    subst hsc
    exact ⟨si, rest, rfl, by simp [lookup_cons]⟩

set_option maxHeartbeats 1600000 in
private theorem step_stmt_a_core (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (st : Stmt)
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    (match st with
      | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append ..
        | .popN .. | .clear .. | .resize .. | .assignWhole .. => True
      | _ => False) →
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) →
    ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt (n + 1) ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ec.outputFuture ∧ FootprintS env (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ TSame tenv tenv' ∧ TopB env lo rst'.nextVar s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s' ∧
      match fl with
      | .normal _ => st.diverges m.noReturn = false
      | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  intro path st ec observation W tenv tenv' penv env s sc tn tn' rst rst' lo
    hsel hactive haccess hprotected hobserved hclassified hp hF hsc hT hlo ht hr hE
  have hcur := (rpStmt_mono hr).1
  cases st with
  | letS x e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, lv, t1, hd, te, t2, hte, hownerRun, heq, htenv, htn⟩ := ht
    rcases htn with ⟨htenv', htn'⟩
    subst tenv'
    subst tn'
    obtain ⟨hxn, re, r1, hre, hr⟩ := hr
    obtain ⟨hxt, hlv, hlsc, hst, _⟩ := declare_ok _ _ _ _ _ hd
    simp only at hlv hlsc hst
    rw [hF.vars_t] at hlv
    obtain ⟨si, rest, htop, hlk⟩ := frameTopAtFuture hF hsc
    have hpv : penv.impl.vars[x]? = some lv := by rw [hF.vars_p]; exact hlv
    have hmono1 := rpExpr_mono hre
    have hb : rst' = r1 ∧ (lv.ty.isRefLike = true → bindRootsV penv penv.scopes x re = .ok ()) := by
      simp only [hpv] at hr
      by_cases hrl : lv.ty.isRefLike = true
      · simp only [hrl, if_true] at hr; inv at hr; exact ⟨hr.2, fun _ => hr.1⟩
      · simp only [hrl] at hr; inv at hr; exact ⟨hr, fun h => absurd h hrl⟩
    obtain ⟨rfl, hbr⟩ := hb
    simp only [execStmt]
    have hchild : (DemandNode.statement (.letS x e o)).child? 0 =
        some (DemandNode.expression e) := by
      simp [DemandNode.child?, DemandNode.children]
    have hchildPhase : DemandNodeHasPhase (DemandNode.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 0 e hchild
    have hvisible : ∀ y, y ∈ tenv.visible ↔
        y ∈ (DemandNode.statement (.letS x e o)).visibleForChild tenv.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hinput : ∀ y, y ∈ childEc.inputFuture → y ∈ ec.inputFuture := by
      intro y hy
      cases ec with
      | pilot profile active =>
        change y ∈ e.variables ++ active at hy
        change y ∈ (DemandNode.statement (.letS x e o)).variables ++ active
        simpa [DemandNode.variables, Stmt.variables] using hy
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hchildContext : childEc = .shrink profile transition.context := rfl
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.letS x e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.letS x e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        rw [hchildContext] at hy
        change y ∈ e.variables ++ transition.context.expected.frame.future at hy
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture] at hy
        simp [DemandNode.phaseFuture] at hy
        change y ∈ (DemandNode.statement (.letS x e o)).variables ++ context.expected.frame.future
        simpa [DemandNode.variables, Stmt.variables] using hy
    have hresult := statementExprChildSpec ih ec observation W tenv penv env s 0 e hchild
      hactive haccess hprotected hobserved hclassified hp hF hvisible hinput _ _ _ _ _ _ hte hre hE
    have houtput : ∀ y, y ∈ ec.outputFuture → y ∈ x :: childEc.outputFuture := by
      intro y hy
      cases ec with
      | pilot profile active =>
        change y ∈ (DemandNode.statement (.letS x e o)).visibleAfter active at hy
        change y ∈ x :: (DemandNode.expression e).visibleAfter
          ((DemandNode.statement (.letS x e o)).visibleForChild active 0)
        by_cases hx : x ∈ active
        · simp [DemandNode.visibleAfter, hx] at hy
          simp [DemandNode.visibleForChild, DemandNode.visibleAfter, hx]
          exact Or.inr hy
        · simpa [DemandNode.visibleForChild, DemandNode.visibleAfter, hx] using hy
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.letS x e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.letS x e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        have hchildOutput : childEc.outputFuture = context.expected.frame.future := by
          change transition.context.outputFuture = context.expected.frame.future
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact hfuture
        change y ∈ context.expected.frame.future at hy
        rw [hchildOutput]
        exact List.mem_cons_of_mem _ hy
    refine Sat.bind hresult ?_
    rintro v s1 ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, hv0, hg, howner, hforbidden, hforbiddenChild, hmutation⟩
    have hv := hasTy_passable hv0 htenv
    have hlk' : env.scopes.lookup lv.scope = some si := hlsc ▸ hlk
    simp only [rootOf, hlv, hlk', sat_pure_bind, sat_bindRoot_bind, sat_pure]
    have hfree0 : s.store.roots[RootInst.local env.act si x]? = none := by
      cases h0 : s.store.roots[RootInst.local env.act si x]? with
      | none => rfl
      | some v0 =>
        have := (hT _ _ _ htop x (by rw [h0]; simp)).2
        rw [hxn] at this
        exact absurd this (Nat.lt_irrefl _)
    have hfree : s1.store.roots[RootInst.local env.act si x]? = none := by
      cases h1 : s1.store.roots[RootInst.local env.act si x]? with
      | none => rfl
      | some v1 => exact absurd hfree0 (hfp.dom _ (by rw [h1]; simp))
    obtain ⟨hrootsBind, hvaluesBind, hsafeBind, hretBind, hpilotBind⟩ :=
      statementIntroducePreservation hsafe hfree
    have hroot : ∀ r, Targets v r → (∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r) ∧
        Older r (.local env.act si x) := by
      by_cases hrl : lv.ty.isRefLike = true
      · exact bind_roots_sem hF1 (hbr hrl) hlv hlk' hg
      · exact hasTy_no_targets hv (by simpa using hrl)
    have htop' : env.scopes = (lv.scope, si) :: rest := hlsc ▸ htop
    refine ⟨(hF1.bind hlv hlk' (paramOk_of_storable hst) hfree hv hroot (by
        intro ho r hr
        obtain ⟨_, ann, _, ha, hs, _⟩ := bindRootsV_ok _ _ _ _ (hbr (by
          rcases ho with ⟨mu, el, ht | ht⟩ <;> simp [ht, Ty.isRefLike]))
        exact ⟨ann, ha, (howner (statementOwnerRefTyOfPassable htenv ho) r hr).subset hs⟩)).narrowFuture houtput,
      hfp.toS.trans (extS_bind htop' hlv hfree).toFootprintS, hroots.trans hrootsBind,
      hvalues.trans hvaluesBind, hsafeBind, hret.trans hretBind,
      fun hprof => StoreLe.trans (hpilot hprof) (hpilotBind hprof),
      TSame.cons _ _, ?_, hforbidden.trans (statementIntroduceForbidden hfree),
      hmutation.trans (by
        apply statementSingleRootMutation (root := .local env.act si x)
        · intro r hne
          simp [Store.introduce, Std.HashMap.getElem?_insert, Ne.symm hne]
        · exact Or.inr ⟨env.act, si, x, rfl, (hF1.inst_lt hlk').1⟩), rfl⟩
    refine topB_bind htop (hT.ext hfp.dom (Nat.le_refl _)) ?_ ?_ ?_
    · rw [hxn]; exact hlo
    · rw [hxn]; exact hmono1.1
    · exact Nat.le_trans (Nat.le_succ _) hmono1.1
  | assign p e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t, b, contents, t1, htp, hfl, te, t2, hte, heq, _, rfl, rfl⟩ := ht
    obtain ⟨rp, r1, hrp, re, r2, hre, hck, r3, hw, rfl⟩ := hr
    have : te = t := by simpa using heq
    subst this
    obtain ⟨_, hin0⟩ := addWrites_ok _ _ _ hw
    have hE3 : EffLe r3.eff W.E :=
      EffLe.trans ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩ hE
    have hin : ∀ t', t' ∈ rootsTargets rp → t' ∈ W.E.writes := fun t' ht' => hE3.2.1 t' (hin0 t' ht')
    have hE2 : EffLe r2.eff W.E := (PMono.addWrites _ _ _ _ hw).2.trans hE3
    have hfinalE : EffLe r2.eff { r3.eff with rebinds := addTargets r3.eff.rebinds (storeRebinds penv p) } := (PMono.addWrites _ _ _ _ hw).2.trans
      ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩
    have hfinalR : RebindsLe r2.eff { r3.eff with rebinds := addTargets r3.eff.rebinds (storeRebinds penv p) } := fun target hmem =>
      addTargets_left _ _ target (PMonoRebinds.addWrites _ _ _ _ hw target hmem)
    simp only [execStmt]
    have hchildP : (DemandNode.statement (.assign p e o)).child? 0 =
        some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
    have hphaseP : DemandNodeHasPhase (DemandNode.place p) .place := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    have hvisibleP : ∀ x, x ∈ tenv'.visible ↔
        x ∈ (DemandNode.statement (.assign p e o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hresultP := statementPlaceChildSpec ih ec observation W tenv' penv env s 0 p hchildP
      hactive haccess hprotected hobserved hclassified hp hF hvisibleP
      (statementAssignPlaceInputSubset ec) _ _ _ _ _ _ _ _ htp hrp
      ((rpExpr_mono hre).2.trans hE2)
    refine Sat.bind hresultP ?_
    rintro l s1 ⟨hF1, hX1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hpl, hg, howner1, hforbidden1, hmutation1⟩
    have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hrp
    have hchildE : (DemandNode.statement (.assign p e o)).child? 1 =
        some (DemandNode.expression e) := by simp [DemandNode.child?, DemandNode.children]
    have hphaseE : DemandNodeHasPhase (DemandNode.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 1 e hchildE
    have hinputE := statementAssignExprInputFrame ec hactive hF1
    have hvisibleE : ∀ x, x ∈ tenv'.visible ↔
        x ∈ (DemandNode.statement (.assign p e o)).visibleForChild tenv'.visible 1 := by
      simp [DemandNode.visibleForChild]
    have hclassified1 : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store := by
      intro hprofile
      exact hF.classifiedParameters_advance (hclassified hprofile) hX1
    have hresultE := statementExprChildSpecAtFrame ih ec observation W tenv' tenv' penv env s1
      1 e hchildE hactive haccess hprotected hsafe1 hclassified1 hp childEc rfl hinputE
      hvisibleE childEc.retained (fun _ hmem => hmem) _ _ _ _ _ _ hte hre hE2
    have houtputE : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.expression e).visibleAfter
          ((DemandNode.statement (.assign p e o)).visibleForChild active 1) =
          (DemandNode.statement (.assign p e o)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 1 (DemandNode.expression e) .expression
          hchildE hphaseE
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.assign p e o))
            stmtPlanContext.approvals.access
            ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 1 = some ⟨
                (DemandNode.statement (.assign p e o)).visibleForChild
                  context.expected.frame.active 1,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    refine Sat.bind hresultE ?_
    rintro v s2 ⟨hF2, hX2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hv, hgv, howner2, hforbidden2, hforbiddenChild2, hmutation2⟩
    have hforbiddenPre := hforbidden1.trans hforbidden2
    have hmutationPre := ((hmutation1.weaken (effectMutationRoots.mono m penv.impl
      (rpExpr_mono hre).2 (rpExpr_rebinds_mono hre))).trans hmutation2).weaken
        (effectMutationRoots.mono m penv.impl hfinalE hfinalR)
    have hchanged := statementEffectMutationRoot hF2 hg (effect := { r3.eff with rebinds := addTargets r3.eff.rebinds (storeRebinds penv p) }) (by
      intro target hmem
      simp only [effectMutationTargets, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (hin0 target hmem))))
    rcases hpl with ⟨hrt, hl, hheader⟩ | ⟨x, lv, si, v', hpv, _, _, _, _, hrl, _⟩ |
      ⟨x, lv, mu0, mus, E, ann, rfl, hlv, hty, rfl, hflE, hpath, hann, hgl, hlive⟩
    · have hfl' : te.flat = true := by
        cases hf : te.flat with
        | true => rfl
        | false =>
          simp only [hf, Bool.false_or, Bool.and_eq_true] at hfl
          rw [isSlice_not_refTarget hfl.1] at hrt; cases hrt
      have hloc2 : LocOk m W.G s2.store l te := by
        cases ec with
        | pilot profile _ => exact hl.mono (hpilot2 profile)
        | @shrink pc profile context =>
          have hMod : tenv'.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
          have hVars : tenv'.vars = penv.impl.vars :=
            haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
          have hEnv : pc.approvals.access = penv.access := by
            have hAccessMod := haccess.2.2.1
            have hAccessImpl := haccess.2.2.2.1
            have hAccessCtx := haccess.2.2.2.2
            cases hAccessValue : pc.approvals.access
            rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
            unfold PEnv.access
            congr 1
          have hplaceType : penv.access.placeType? p = some te :=
            tyPlace_accessType hMod hVars htp
          have hAliasCondition :
              ((Ty.ref .mutable te).interiorTarget?.isSome || te.ownerElem?.isSome) = true := by
            cases te <;> simp_all [Ty.flat, Ty.interiorTarget?, Ty.ownerElem?]
          let transition := context.child rfl 1 (DemandNode.expression e) .expression
            hchildE hphaseE
          have hPlaceRoots : ∃ roots, penv.access.placeRoots p = .ok roots := by
            cases hroots : penv.access.placeRoots p with
            | error err =>
              have hbad :
                  (DemandNode.statement (.assign p e o)).childFrame
                    penv.access path context.expected.frame 1 = .error err := by
                have hExpectation :
                    (DemandNode.statement (.assign p e o)).childExpectation?
                        penv.access
                        ⟨path, .expression, context.expected.frame.active,
                          context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                      some ⟨context.expected.frame.active, context.expected.frame.future⟩ := by
                  simp [DemandNode.childExpectation?, DemandNode.childFuture,
                    DemandNode.visibleForChild, DemandNode.child?, DemandNode.children]
                simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                  AccessEnv.aliasPlace, hplaceType, hAliasCondition, hroots,
                  Functor.map, Except.map]
              have htransition := transition.childFrameEq
              rw [hEnv] at htransition
              rw [hbad] at htransition
              cases htransition
            | ok roots => exact ⟨roots, rfl⟩
          obtain ⟨roots, hPlaceRoots⟩ := hPlaceRoots
          let placeAlias : RetainedAlias :=
            ⟨.ref .mutable te, roots, .operand (path ++ [0])⟩
          have hAliasQuery : penv.access.aliasPlace (path ++ [0]) p = .ok [placeAlias] := by
            simp [AccessEnv.aliasPlace, hplaceType, hAliasCondition, hPlaceRoots, placeAlias,
              Functor.map, Except.map]
          have hAliasQueryCtx : pc.approvals.access.aliasPlace (path ++ [0]) p =
              .ok [placeAlias] := by
            rw [hEnv]
            exact hAliasQuery
          have hnew : (DemandNode.statement (.assign p e o)).retainedForChild
              pc.approvals.access path 1 = .ok [placeAlias] := by
            simp [DemandNode.retainedForChild, hAliasQueryCtx]
          have hAliasMem : placeAlias ∈ childEc.retained := by
            have hChild := DemandNode.childFrame_newAlias
              (result := transition.childFrame) (aliases := [placeAlias])
              (alias := placeAlias) transition.childFrameEq hnew
              (List.mem_cons.mpr (Or.inl rfl))
            change placeAlias ∈ transition.context.expected.frame.retained
            rw [transition.expectedFrameEq]
            exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
          have hAliasSource : AliasAt m W env s1.store placeAlias (.ref l) :=
            AliasAt.ofAliasPlace hAliasQuery hplaceType hrp (Or.inl ⟨hrt, hl, hheader⟩) hg
              (Or.inl (flat_refTarget hfl'))
          have hAliasPost := (hret2 placeAlias hAliasMem).typed (.ref l) hAliasSource
          rcases hAliasPost.1 with ⟨l', heq, hloc⟩
          cases heq
          rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
          · exact hloc
          · cases te <;> simp_all [Ty.isSlice, Ty.refTarget]
      have hlt := access hp hloc2 hg (fun t' ht' => Or.inr (Or.inl (hin t' ht')))
      refine sat_writeLoc_bind hlt (fun st' hw' => ?_)
      simp only [sat_pure]
      have hstep := write_flatStep _ _ _ _ _ hfl' hlt (hv.flat hfl') hw'
      have hrootsWrite := statementWritePreservesRootTypes
        (m := m) (G := W.G) (observation := observation) hstep.le hlt hw'
      obtain ⟨hrootsWrite, hvaluesWrite, hsafeWrite, hretWrite, hpilotWrite⟩ :=
        statementFlatStepPreservation (s := s2) (s' := { s2 with store := st' })
          hsafe2 hrootsWrite hstep
      have hX := (hX1.trans hX2).trans (Footprint.of_flatStep hstep)
      have hretained : RetainsAliases m W env s.store st' ec.retained :=
        hret1.trans ((hret2.trans hretWrite).subset (fun alias hmem =>
          ec.child_retained_subset rfl 1 (DemandNode.expression e) .expression
            hchildE hphaseE hmem))
      exact ⟨houtputE ▸ hF2.flatStep hstep, hX.toS,
        (hroots1.trans hroots2).trans hrootsWrite,
        (hvalues1.trans hvalues2).trans hvaluesWrite, hsafeWrite, hretained,
        fun hprofile => StoreLe.trans (hpilot1 hprofile)
          (StoreLe.trans (hpilot2 hprofile) (hpilotWrite hprofile)),
        TSame.refl _, hT.ext hX.dom hcur,
      hforbiddenPre.trans (statementStoreForbidden hF2 hg hdisjoint
        (modify_roots_agree_except s2.store st' l (fun _ => some v) hw')),
      hmutationPre.trans (statementSingleRootMutation
        (modify_roots_agree_except s2.store st' l (fun _ => some v) hw') hchanged), rfl⟩
    · subst hpv
      cases hf : te.flat with
      | true => rw [refTarget_not_refLike (flat_refTarget hf)] at hrl; cases hrl
      | false => simp [hf, Place.derefVar?] at hfl
    · -- A slice stored through a reference to a slice variable of a caller.
      have hsv : penv.isRefSliceVar x = true := by
        simp [PEnv.isRefSliceVar, hF2.vars_p, hlv, hty, Ty.isRefSlice, hflE]
      obtain ⟨cont, hc, hsub⟩ := checkStore_ok _ _ _ hck x rfl hsv
      obtain ⟨hnl, hann', hpr⟩ := hF2.pref x _ hc
      rw [hann] at hann'
      cases hann'
      obtain ⟨q, hq, hrq⟩ := hgl
      simp only [List.mem_singleton] at hq
      subst hq
      obtain ⟨hD, _, hFW⟩ := hpr lv mu0 mus E hlv hty _ hrq
      obtain ⟨old, ho, _, _⟩ := hF2.sa _ E hD
      have hl : l = ⟨l.root, []⟩ := by
        cases l; simp only at hpath; simp [hpath]
      rw [hl]
      refine sat_writeRoot_bind ho ?_
      simp only [sat_pure]
      obtain ⟨hFw, hXw⟩ := hF2.outwrite hD (hasTy_slice_mu hv)
        (fun t ht' => hFW t (gam_noEnv ((hgv t ht').subset hsub) hnl))
      have hX := (hX1.trans hX2).trans hXw.toFootprint
      have hrootsWrite : PreservesRootTypes m W.G observation.roots s2.store
          ⟨(s2.store.roots.erase l.root).insert l.root v⟩ := by
        intro r T hobs old hold htyped
        by_cases heq : r = l.root
        · subst r
          obtain ⟨mu, rfl⟩ := hsafe2.holderTypes l.root T E hobs hD
          exact ⟨v, by simp [get_reinsert], hasTy_slice_mu (HasTy.mono hXw.le hv)⟩
        · refine ⟨old, ?_, HasTy.mono hXw.le htyped⟩
          have hne : l.root ≠ r := fun h => heq h.symm
          simp [get_reinsert, hne, hold]
      have hvaluesWrite : PreservesValues m W.G observation.values s2.store
          ⟨(s2.store.roots.erase l.root).insert l.root v⟩ := by
        intro value T _ htyped
        exact HasTy.mono hXw.le htyped
      have hsafeWrite := hF2.observedSafe_outerPreserved hprotected hsafe2
        hXw.toFootprint hrootsWrite hvaluesWrite (fun r E hD' => hFw.sa r E hD')
      have hretWrite : RetainsAliases m W env s2.store
          ⟨(s2.store.roots.erase l.root).insert l.root v⟩ childEc.retained := by
        intro alias _
        constructor
        · intro value ⟨htyped, hroots⟩
          exact ⟨HasTy.mono hXw.le htyped, hroots⟩
        · intro mu el capacity location start len htype halias hslice
          exact SliceTy.mono hXw.le hslice
      have hretained : RetainsAliases m W env s.store
          ⟨(s2.store.roots.erase l.root).insert l.root v⟩ ec.retained :=
        hret1.trans ((hret2.trans hretWrite).subset (fun alias hmem =>
          ec.child_retained_subset rfl 1 (DemandNode.expression e) .expression
            hchildE hphaseE hmem))
      exact ⟨houtputE ▸ hFw, hX.toS,
        (hroots1.trans hroots2).trans hrootsWrite,
        (hvalues1.trans hvalues2).trans hvaluesWrite, hsafeWrite, hretained,
        fun hprofile => StoreLe.trans (hpilot1 hprofile)
          (StoreLe.trans (hpilot2 hprofile) hXw.le),
        TSame.refl _, hT.ext hX.dom hcur,
        hforbiddenPre.trans (statementStoreForbidden hF2 hg hdisjoint (by
          intro r hne
          simp [get_reinsert, Ne.symm hne])),
        hmutationPre.trans (statementSingleRootMutation (root := l.root) (s' := { s2 with store := ⟨(s2.store.roots.erase l.root).insert l.root v⟩ }) (by
          intro r hne
          simp [get_reinsert, Ne.symm hne]) hchanged), rfl⟩
  | assignOp op p e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t, b, contents, t1, htp, it, rfl, te, t2, hte, iu, rfl, rfl, _, rfl, rfl⟩ := ht
    obtain ⟨rp, r1, hrp, re, r2, hre, r3, hrd, r4, hwr, hfin⟩ := hr
    have hE4 : EffLe r4.eff W.E := by
      refine EffLe.trans ?_ hE
      rcases hfin with ⟨_, hna⟩ | ⟨_, rfl⟩
      · exact (PMono.noteAborts _ _ _ hna).2
      · exact EffLe.refl _
    obtain ⟨_, hinr⟩ := addReads_ok _ _ _ hrd
    have hE3 := (PMono.addWrites _ _ _ _ hwr).2.trans hE4
    have hE2 := (PMono.addReads _ _ _ _ hrd).2.trans hE3
    have hfinal4E : EffLe r4.eff rst'.eff := by
      rcases hfin with ⟨_, hna⟩ | ⟨_, rfl⟩
      · exact (PMono.noteAborts _ _ _ hna).2
      · exact EffLe.refl _
    have hfinal4R : RebindsLe r4.eff rst'.eff := by
      rcases hfin with ⟨_, hna⟩ | ⟨_, rfl⟩
      · have heq := (st_modify_ok _ _ _).1 hna
        cases heq
        exact RebindsLe.refl _
      · exact RebindsLe.refl _
    have hfinalE := ((PMono.addReads _ _ _ _ hrd).2.trans
      (PMono.addWrites _ _ _ _ hwr).2).trans hfinal4E
    have hfinalR : RebindsLe r2.eff rst'.eff := fun target hmem => hfinal4R target
      (PMonoRebinds.addWrites _ _ _ _ hwr target
        (PMonoRebinds.addReads _ _ _ _ hrd target hmem))
    simp only [execStmt]
    have hchildP : (DemandNode.statement (.assignOp op p e o)).child? 0 =
        some (DemandNode.place p) := by simp [DemandNode.child?, DemandNode.children]
    have hvisibleP : ∀ x, x ∈ tenv'.visible ↔
        x ∈ (DemandNode.statement (.assignOp op p e o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hresultP := statementPlaceChildSpec ih ec observation W tenv' penv env s 0 p hchildP
      hactive haccess hprotected hobserved hclassified hp hF hvisibleP
      (statementAssignOpPlaceInputSubset ec) _ _ _ _ _ _ _ _ htp hrp
      ((rpExpr_mono hre).2.trans hE2)
    refine Sat.bind hresultP ?_
    rintro l s1 ⟨hF1, hX1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hpl, hg, howner1, hforbidden1, hmutation1⟩
    have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hrp
    rcases hpl with ⟨_, hl, _⟩ | ⟨x, lv, si, v', _, _, _, _, _, hrl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
    · have hlt1 := access hp hl hg (fun t' ht' => Or.inl (hE3.1 t' (hinr t' ht')))
      refine sat_readLoc_bind hlt1 (fun v0 _ hT0 => ?_)
      cases v0 <;> simp only [FlatTy] at hT0
      subst hT0
      simp only [expectInt, sat_pure_bind]
      have hchildE : (DemandNode.statement (.assignOp op p e o)).child? 1 =
          some (DemandNode.expression e) := by simp [DemandNode.child?, DemandNode.children]
      have hphaseE : DemandNodeHasPhase (DemandNode.expression e) .expression := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      let childEc := statementExprChildContext ec 1 e hchildE
      have hinputE := statementAssignOpExprInputFrame ec hactive hF1
      have hvisibleE : ∀ x, x ∈ tenv'.visible ↔
          x ∈ (DemandNode.statement (.assignOp op p e o)).visibleForChild tenv'.visible 1 := by
        simp [DemandNode.visibleForChild]
      have hclassified1 : m.profile = .shrink →
          ClassifiedParameters m W.P W.D observation s1.store := by
        intro hprofile
        exact hF.classifiedParameters_advance (hclassified hprofile) hX1
      have hresultE := statementExprChildSpecAtFrame ih ec observation W tenv' tenv' penv env s1
        1 e hchildE hactive haccess hprotected hsafe1 hclassified1 hp childEc rfl hinputE
        hvisibleE childEc.retained (fun _ hmem => hmem) _ _ _ _ _ _ hte hre hE2
      have houtputE : childEc.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active =>
          change (DemandNode.expression e).visibleAfter
            ((DemandNode.statement (.assignOp op p e o)).visibleForChild active 1) =
            (DemandNode.statement (.assignOp op p e o)).visibleAfter active
          simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
        | shrink profile context =>
          rename_i stmtPlanContext
          let transition := context.child rfl 1 (DemandNode.expression e) .expression
            hchildE hphaseE
          have hexpectation : DemandNode.childExpectation?
              (DemandNode.statement (.assignOp op p e o))
              stmtPlanContext.approvals.access
              ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
                context.expected.frame.retained⟩ 1 = some ⟨
                  (DemandNode.statement (.assignOp op p e o)).visibleForChild
                    context.expected.frame.active 1,
                  context.expected.frame.future⟩ := by
            simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
          have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
            hfuture]
          simp [DemandNode.phaseFuture]
      refine Sat.bind hresultE ?_
      rintro v s2 ⟨hF2, hX2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hv, _, howner2, hforbidden2, hforbiddenChild2, hmutation2⟩
      have hforbiddenPre := hforbidden1.trans hforbidden2
      have hmutationPre := ((hmutation1.weaken (effectMutationRoots.mono m penv.impl
        (rpExpr_mono hre).2 (rpExpr_rebinds_mono hre))).trans hmutation2).weaken
          (effectMutationRoots.mono m penv.impl hfinalE hfinalR)
      have hchanged := statementEffectMutationRoot hF2 hg (effect := rst'.eff) (by
        intro target hmem
        simp only [effectMutationTargets, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (hfinal4E.2.1 target
          ((addWrites_ok _ _ _ hwr).2 target hmem)))))
      obtain ⟨y, rfl⟩ := hasTy_int hv
      simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
      split
      · have hloc2 : LocOk m W.G s2.store l (.int it) := by
          cases ec with
          | pilot profile _ => exact hl.mono (hpilot2 profile)
          | @shrink pc profile context =>
            have hMod : tenv'.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
            have hVars : tenv'.vars = penv.impl.vars :=
              haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
            have hEnv : pc.approvals.access = penv.access := by
              have hAccessMod := haccess.2.2.1
              have hAccessImpl := haccess.2.2.2.1
              have hAccessCtx := haccess.2.2.2.2
              cases hAccessValue : pc.approvals.access
              rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
              unfold PEnv.access
              congr 1
            have hplaceType : penv.access.placeType? p = some (.int it) :=
              tyPlace_accessType hMod hVars htp
            have hAliasCondition :
                ((Ty.ref .mutable (.int it)).interiorTarget?.isSome ||
                  (Ty.int it).ownerElem?.isSome) = true := by
              simp [Ty.interiorTarget?, Ty.ownerElem?]
            let transition := context.child rfl 1 (DemandNode.expression e) .expression
              hchildE hphaseE
            have hPlaceRoots : ∃ roots, penv.access.placeRoots p = .ok roots := by
              cases hroots : penv.access.placeRoots p with
              | error err =>
                have hbad :
                    (DemandNode.statement (.assignOp op p e o)).childFrame
                      penv.access path context.expected.frame 1 = .error err := by
                  have hExpectation :
                      (DemandNode.statement (.assignOp op p e o)).childExpectation?
                          penv.access
                          ⟨path, .expression, context.expected.frame.active,
                            context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                        some ⟨context.expected.frame.active, context.expected.frame.future⟩ := by
                    simp [DemandNode.childExpectation?, DemandNode.childFuture,
                      DemandNode.visibleForChild, DemandNode.child?, DemandNode.children]
                  simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                    AccessEnv.aliasPlace, hplaceType, hAliasCondition, hroots,
                    Functor.map, Except.map]
                have htransition := transition.childFrameEq
                rw [hEnv] at htransition
                rw [hbad] at htransition
                cases htransition
              | ok roots => exact ⟨roots, rfl⟩
            obtain ⟨roots, hPlaceRoots⟩ := hPlaceRoots
            let placeAlias : RetainedAlias :=
              ⟨.ref .mutable (.int it), roots, .operand (path ++ [0])⟩
            have hAliasQuery : penv.access.aliasPlace (path ++ [0]) p = .ok [placeAlias] := by
              simp [AccessEnv.aliasPlace, hplaceType, hAliasCondition, hPlaceRoots, placeAlias,
                Functor.map, Except.map]
            have hAliasQueryCtx : pc.approvals.access.aliasPlace (path ++ [0]) p =
                .ok [placeAlias] := by
              rw [hEnv]
              exact hAliasQuery
            have hnew : (DemandNode.statement (.assignOp op p e o)).retainedForChild
                pc.approvals.access path 1 = .ok [placeAlias] := by
              simp [DemandNode.retainedForChild, hAliasQueryCtx]
            have hAliasMem : placeAlias ∈ childEc.retained := by
              have hChild := DemandNode.childFrame_newAlias
                (result := transition.childFrame) (aliases := [placeAlias])
                (alias := placeAlias) transition.childFrameEq hnew
                (List.mem_cons.mpr (Or.inl rfl))
              change placeAlias ∈ transition.context.expected.frame.retained
              rw [transition.expectedFrameEq]
              exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
            have hAliasSource : AliasAt m W env s1.store placeAlias (.ref l) :=
              AliasAt.ofAliasPlace hAliasQuery hplaceType hrp (Or.inl ⟨rfl, hl, by trivial⟩) hg
                (Or.inl (flat_refTarget rfl))
            have hAliasPost := (hret2 placeAlias hAliasMem).typed (.ref l) hAliasSource
            rcases hAliasPost.1 with ⟨l', heq, hloc⟩
            cases heq
            rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
            · exact hloc
            · cases hslice
        have hlt2 := access hp hloc2 hg (fun t' ht' => Or.inl (hE3.1 t' (hinr t' ht')))
        refine sat_writeLoc_bind hlt2 (fun st' hw' => ?_)
        simp only [sat_pure]
        have hstep := write_flatStep _ _ _ _ (.int it) rfl hlt2
          (show FlatTy (.int it) (Val.int it _) from rfl) hw'
        have hrootsWrite := statementWritePreservesRootTypes
          (m := m) (G := W.G) (observation := observation) hstep.le hlt2 hw'
        obtain ⟨hrootsWrite, hvaluesWrite, hsafeWrite, hretWrite, hpilotWrite⟩ :=
          statementFlatStepPreservation (s := s2) (s' := { s2 with store := st' })
            hsafe2 hrootsWrite hstep
        have hX := (hX1.trans hX2).trans (Footprint.of_flatStep hstep)
        have hretained : RetainsAliases m W env s.store st' ec.retained :=
          hret1.trans ((hret2.trans hretWrite).subset (fun alias hmem =>
            ec.child_retained_subset rfl 1 (DemandNode.expression e) .expression
              hchildE hphaseE hmem))
        exact ⟨houtputE ▸ hF2.flatStep hstep, hX.toS,
          (hroots1.trans hroots2).trans hrootsWrite,
          (hvalues1.trans hvalues2).trans hvaluesWrite, hsafeWrite, hretained,
          fun hprofile => StoreLe.trans (hpilot1 hprofile)
            (StoreLe.trans (hpilot2 hprofile) (hpilotWrite hprofile)),
          TSame.refl _, hT.ext hX.dom hcur,
          hforbiddenPre.trans (statementStoreForbidden hF2 hg hdisjoint
            (modify_roots_agree_except s2.store st' l _ hw')),
          hmutationPre.trans (statementSingleRootMutation
            (modify_roots_agree_except s2.store st' l _ hw') hchanged), rfl⟩
      · trivial
    · simp [Ty.isRefLike] at hrl
    · cases h3
  | rebind x e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hx, lv, hlv, hrl, _, te, t1, hte, heq, rfl, rfl⟩ := ht
    obtain ⟨re, r1, hre, hb, hfin⟩ := hr
    have hE1 : EffLe r1.eff W.E := by
      refine EffLe.trans ?_ hE
      rcases hfin with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩
      · exact EffLe.refl _
    simp only [execStmt]
    have hchild : (DemandNode.statement (.rebind x e o)).child? 0 =
        some (DemandNode.expression e) := by
      simp [DemandNode.child?, DemandNode.children]
    have hchildPhase : DemandNodeHasPhase (DemandNode.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 0 e hchild
    have hvisible : ∀ y, y ∈ tenv'.visible ↔
        y ∈ (DemandNode.statement (.rebind x e o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hinput : ∀ y, y ∈ childEc.inputFuture → y ∈ ec.inputFuture := by
      intro y hy
      cases ec with
      | pilot profile active =>
        change y ∈ e.variables ++ active at hy
        change y ∈ (DemandNode.statement (.rebind x e o)).variables ++ active
        simpa [DemandNode.variables, Stmt.variables] using hy
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hchildContext : childEc = .shrink profile transition.context := rfl
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.rebind x e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.rebind x e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        rw [hchildContext] at hy
        change y ∈ e.variables ++ transition.context.expected.frame.future at hy
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture] at hy
        simp [DemandNode.phaseFuture] at hy
        change y ∈ (DemandNode.statement (.rebind x e o)).variables ++ context.expected.frame.future
        simpa [DemandNode.variables, Stmt.variables] using hy
    have hresult := statementExprChildSpec ih ec observation W tenv' penv env s 0 e hchild
      hactive haccess hprotected hobserved hclassified hp hF hvisible hinput _ _ _ _ _ _ hte hre hE1
    have houtput : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.expression e).visibleAfter
          ((DemandNode.statement (.rebind x e o)).visibleForChild active 0) =
          (DemandNode.statement (.rebind x e o)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.rebind x e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.rebind x e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.outputFuture = context.outputFuture
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    refine Sat.bind hresult ?_
    rintro v s1 ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, hv0, hg, howner, hforbidden, hforbiddenChild, hmutation⟩
    have hv := hasTy_passable hv0 heq
    obtain ⟨lv1, si, old, h1, h2, h3, h4, h5⟩ := hF1.bindings x hx
    rw [hF.vars_t, h1] at hlv
    cases hlv
    simp only [rootOf, h1, h2, sat_pure_bind]
    refine sat_writeRoot_bind h4 ?_
    simp only [sat_pure]
    have hold : IsRef old := h5 hrl
    have hroot := bind_roots_sem hF1 hb h1 h2 hg
    let s2 := { s1 with store := ⟨(s1.store.roots.erase (.local env.act si x)).insert
      (.local env.act si x) v⟩ }
    have hRebind := ext_rebind (D := Dset W) (v := v) (lookup_inst h2) h4 hold
    have hnotObserved : ∀ T, observation.roots (.local env.act si x) T → False := by
      intro T hobs
      have hlt : si < W.base := by
        simpa [BeforeBase] using hsafe.rootsOlder (.local env.act si x) T hobs
      have hbase := (hF1.inst_lt h2).1
      exact (Nat.not_lt_of_ge hbase) hlt
    have hsame : ∀ r T, observation.roots r T → ∀ old,
        (s1.store.roots[r]? = some old ↔ s2.store.roots[r]? = some old) := by
      intro r T hobs old
      have hneq : RootInst.local env.act si x ≠ r := by
        intro heq
        subst r
        exact False.elim (hnotObserved T hobs)
      constructor <;> intro hrootStore <;>
        simpa [s2, get_reinsert, hneq] using hrootStore
    obtain ⟨hrootsOp, hvaluesOp, hsafeOp, hretOp, hpilotOp⟩ :=
      statementStorePreservation hsafe hRebind.le hsame
    have hX := hfp.trans hRebind.toFootprint
    exact ⟨houtput ▸ hF1.rebind h1 h2 h4 hold h3 hv hroot (by
        intro ho r hr
        obtain ⟨_, ann, _, ha, hs, _⟩ := bindRootsV_ok _ _ _ _ hb
        exact ⟨ann, ha, (howner (statementOwnerRefTyOfPassable heq ho) r hr).subset hs⟩), hX.toS,
      hroots.trans hrootsOp,
      hvalues.trans hvaluesOp, hsafeOp, hret.trans hretOp,
      fun hprof => StoreLe.trans (hpilot hprof) (hpilotOp hprof),
      TSame.refl _, hT.ext hX.dom hcur,
      hforbidden.trans (statementRebindForbidden h4 hold),
      (by
        have hsubset : ∀ root, root ∈ effectMutationRoots m penv.impl r1.eff →
            root ∈ effectMutationRoots m penv.impl rst'.eff := by
          apply effectMutationRoots.mono m penv.impl
          · rcases hfin with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact EffLe.refl _
          · rcases hfin with ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact addTargets_left _ _
            · exact RebindsLe.refl _
        apply (hmutation.weaken hsubset).trans
        apply statementSingleRootMutation (root := .local env.act si x)
        · intro r hne
          simp [get_reinsert, Ne.symm hne]
        · exact Or.inr ⟨env.act, si, x, rfl, (hF1.inst_lt h2).1⟩), rfl⟩
  | expr e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, te, t1, hte, rfl, rfl⟩ := ht
    obtain ⟨re, hre⟩ := hr
    simp only [execStmt]
    have hchild : (DemandNode.statement (.expr e o)).child? 0 =
        some (DemandNode.expression e) := by
      simp [DemandNode.child?, DemandNode.children]
    have hchildPhase : DemandNodeHasPhase (DemandNode.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 0 e hchild
    have hvisible : ∀ x, x ∈ tenv'.visible ↔
        x ∈ (DemandNode.statement (.expr e o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hinput : ∀ x, x ∈ childEc.inputFuture → x ∈ ec.inputFuture := by
      intro x hx
      cases ec with
      | pilot profile active =>
        change x ∈ e.variables ++ active at hx
        change x ∈ (DemandNode.statement (.expr e o)).variables ++ active
        simpa [DemandNode.variables, Stmt.variables] using hx
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hchildContext : childEc = .shrink profile transition.context := rfl
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.expr e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.expr e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        rw [hchildContext] at hx
        change x ∈ e.variables ++ transition.context.expected.frame.future at hx
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture] at hx
        simp [DemandNode.phaseFuture] at hx
        change x ∈ (DemandNode.statement (.expr e o)).variables ++ context.expected.frame.future
        simpa [DemandNode.variables, Stmt.variables] using hx
    have hresult := statementExprChildSpec ih ec observation W tenv' penv env s 0 e hchild
      hactive haccess hprotected hobserved hclassified hp hF hvisible hinput _ _ _ _ _ _ hte hre hE
    have houtput : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change active = active
        rfl
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.expr e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.expr e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    refine Sat.bind_eq hresult ?_
    rintro v s1 heq ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, _, _, _, hforbidden, hforbiddenChild, hmutation⟩
    simp only [sat_pure]
    refine ⟨houtput ▸ hF1, hfp.toS, hroots, hvalues, hsafe, hret, hpilot,
      TSame.refl _, hT.ext hfp.dom hcur, hforbidden, hmutation, ?_⟩
    -- A call that returned is not a call of a function that never returns.
    cases hdv : (Stmt.expr e o).diverges m.noReturn with
    | false => rfl
    | true =>
      exact absurd heq (never_call_expr ⟨prof, m⟩ m.noReturn (noReturn_sound m prof) n env e o
        (by cases e <;> first
              | (simp [Stmt.diverges] at hdv; done)
              | (simpa [Stmt.diverges] using hdv)) s v s1)
  | append owner src o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t, b, contents, t1, htp, ht⟩ := ht
    obtain ⟨rp, r1, hrp, rv, r2, hrv, r3, hrd, hgr⟩ := hr
    obtain ⟨r4, hgrows, hprofile⟩ := hgr
    obtain ⟨_, hin⟩ := addGrows_ok _ _ _ hgrows
    have hE3 : EffLe r4.eff W.E := by
      rcases hprofile with ⟨_, s1, hwrite, a, ha, hrun⟩ | ⟨_, hsame⟩
      · have hwrite' : EffLe r4.eff s1.eff := ((PMono.addWrites rp) r4 () s1 hwrite).2
        rcases hrun with ⟨_, hnote⟩ | ⟨_, hsame⟩
        · exact (hwrite'.trans ((PMono.noteAborts s1 () rst' hnote).2)).trans hE
        · subst rst'
          exact hwrite'.trans hE
      · subst rst'
        exact hE
    have hfinal4E : EffLe r4.eff rst'.eff := by
      rcases hprofile with ⟨_, middle, hwrite, a, ha, hrun⟩ | ⟨_, hsame⟩
      · have he := (PMono.addWrites _ _ _ _ hwrite).2
        rcases hrun with ⟨_, hnote⟩ | ⟨_, hsame⟩
        · exact he.trans (PMono.noteAborts _ _ _ hnote).2
        · subst rst'
          exact he
      · subst rst'
        exact EffLe.refl _
    have hfinal4R : RebindsLe r4.eff rst'.eff := by
      rcases hprofile with ⟨_, middle, hwrite, a, ha, hrun⟩ | ⟨_, hsame⟩
      · have he := PMonoRebinds.addWrites _ _ _ _ hwrite
        rcases hrun with ⟨_, hnote⟩ | ⟨_, hsame⟩
        · have heq := (st_modify_ok _ _ _).1 hnote
          cases heq
          exact he
        · subst rst'
          exact he
      · subst rst'
        exact RebindsLe.refl _
    have hfinalE := ((PMono.addReads _ _ _ _ hrd).2.trans
      (PMono.addGrows _ _ _ _ hgrows).2).trans hfinal4E
    have hfinalR : RebindsLe r2.eff rst'.eff := fun target hmem => hfinal4R target
      (PMonoRebinds.addGrows _ _ _ _ hgrows target
        (PMonoRebinds.addReads _ _ _ _ hrd target hmem))
    have hE4 : EffLe r3.eff W.E := (PMono.addGrows rp _ _ _ hgrows).2.trans hE3
    have hE2 := (PMono.addReads _ _ _ _ hrd).2.trans hE4
    obtain ⟨el, n1, howner, hrest⟩ := ht
    obtain ⟨sel, b', htv, hview, hsel, htenv, htn⟩ := hrest
    have hselEl : sel = el := by simpa using hsel
    have hownerElem : t.ownerElem? = some sel := by
      have h := (ownerElement_ok _ t el _ _ howner).2.1
      rw [← hselEl] at h
      exact h
    rcases htn with ⟨htenv', htn'⟩
    subst tenv'
    subst tn'
    simp only [execStmt]
    have hchildP : (DemandNode.statement (.append owner src o)).child? 0 =
        some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
    have hvisibleP : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.append owner src o)).visibleForChild tenv.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hresultP := statementPlaceChildSpec ih ec observation W tenv penv env s 0 owner hchildP
      hactive haccess hprotected hobserved hclassified hp hF hvisibleP
      (statementAppendPlaceInputSubset ec) _ _ _ _ _ _ _ _ htp hrp
      ((rpView_mono hrv).2.trans hE2)
    refine Sat.bind hresultP ?_
    rintro l s1 ⟨hF1, hX1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hpl, hg, howner1, hforbidden1, hmutation1⟩
    have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hrp
    have hchildV : (DemandNode.statement (.append owner src o)).child? 1 =
        some (DemandNode.view src) := by simp [DemandNode.child?, DemandNode.children]
    have hphaseV : DemandNodeHasPhase (DemandNode.view src) .view := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementViewChildContext ec 1 src hchildV
    have hinputV := statementAppendViewInputFrame ec hactive hF1
    have hvisibleV : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.append owner src o)).visibleForChild tenv.visible 1 := by
      simp [DemandNode.visibleForChild]
    have hclassified1 : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store := by
      intro hprofile'
      exact hF.classifiedParameters_advance (hclassified hprofile') hX1
    have hresultV := statementViewChildSpecAtFrame ih ec observation W tenv tenv penv env s1
      1 src hchildV hactive haccess hprotected hsafe1 hclassified1 hp childEc rfl hinputV
      hvisibleV childEc.retained (fun _ hmem => hmem) _ _ _ _ _ _ _ hview hrv hE2
    have houtputV : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.view src).visibleAfter
          ((DemandNode.statement (.append owner src o)).visibleForChild active 1) =
          (DemandNode.statement (.append owner src o)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 1 (DemandNode.view src) .view hchildV hphaseV
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.append owner src o))
            stmtPlanContext.approvals.access
            ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 1 = some ⟨
                (DemandNode.statement (.append owner src o)).visibleForChild
                  context.expected.frame.active 1,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildV]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    refine Sat.bind hresultV ?_
    rintro vw s2 ⟨hF2, hX2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hvw, _, _, hforbidden2, hmutation2⟩
    have hforbiddenPre := hforbidden1.trans hforbidden2
    have hmutationPre := ((hmutation1.weaken (effectMutationRoots.mono m penv.impl
      (rpView_mono hrv).2 (rpView_rebinds_mono hrv))).trans hmutation2).weaken
        (effectMutationRoots.mono m penv.impl hfinalE hfinalR)
    have hchanged := statementEffectMutationRoot hF2 hg (effect := rst'.eff) (by
      intro target hmem
      simp only [effectMutationTargets, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (hfinal4E.2.2.1 target (hin target hmem)))))
    refine sat_readRun_bind hvw (fun vs hvs => ?_)
    rcases hpl with ⟨hrt, hl, hheader⟩ | ⟨x, lv, si, v', _, _, _, _, _, hrl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
    · have hlt : LocTy s2.store l t := by
        cases ec with
        | pilot profile _ =>
          exact access hp (hl.mono (hpilot2 profile)) hg
            (fun t' ht' => Or.inr (Or.inr (Or.inl (hE3.2.2.1 t' (hin t' ht')))))
        | @shrink pc profile context =>
          have hMod : tenv.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
          have hVars : tenv.vars = penv.impl.vars :=
            haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
          have hEnv : pc.approvals.access = penv.access := by
            have hAccessMod := haccess.2.2.1
            have hAccessImpl := haccess.2.2.2.1
            have hAccessCtx := haccess.2.2.2.2
            cases hAccessValue : pc.approvals.access
            rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
            unfold PEnv.access
            congr 1
          have hplaceType : penv.access.placeType? owner = some t :=
            tyPlace_accessType hMod hVars htp
          let transition := context.child rfl 1 (DemandNode.view src) .view hchildV hphaseV
          have hOwnerRoots : ∃ roots, penv.access.placeRoots owner = .ok roots := by
            cases hroots : penv.access.placeRoots owner with
            | error err =>
              have hbad :
                  (DemandNode.statement (.append owner src o)).childFrame
                    penv.access path context.expected.frame 1 = .error err := by
                have hExpectation :
                    (DemandNode.statement (.append owner src o)).childExpectation?
                        penv.access
                        ⟨path, .expression, context.expected.frame.active,
                          context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                      some ⟨context.expected.frame.active, context.expected.frame.future⟩ := by
                  simp [DemandNode.childExpectation?, DemandNode.childFuture,
                    DemandNode.visibleForChild, DemandNode.child?, DemandNode.children]
                simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                  AccessEnv.aliasPlace, hplaceType, hownerElem, hroots,
                  Functor.map, Except.map]
              have htransition := transition.childFrameEq
              rw [hEnv] at htransition
              rw [hbad] at htransition
              cases htransition
            | ok roots => exact ⟨roots, rfl⟩
          obtain ⟨roots, hOwnerRoots⟩ := hOwnerRoots
          let ownerAlias : RetainedAlias :=
            ⟨.ref .mutable t, roots, .operand (path ++ [0])⟩
          have hAliasQuery : penv.access.aliasPlace (path ++ [0]) owner = .ok [ownerAlias] := by
            simp [AccessEnv.aliasPlace, hplaceType, hownerElem, hOwnerRoots, ownerAlias,
              Functor.map, Except.map]
          have hAliasQueryCtx : pc.approvals.access.aliasPlace (path ++ [0]) owner =
              .ok [ownerAlias] := by
            rw [hEnv]
            exact hAliasQuery
          have hnew : (DemandNode.statement (.append owner src o)).retainedForChild
              pc.approvals.access path 1 = .ok [ownerAlias] := by
            simp [DemandNode.retainedForChild, hAliasQueryCtx]
          have hAliasMem : ownerAlias ∈ childEc.retained := by
            have hChild := DemandNode.childFrame_newAlias
              (result := transition.childFrame) (aliases := [ownerAlias])
              (alias := ownerAlias) transition.childFrameEq hnew
              (List.mem_cons.mpr (Or.inl rfl))
            change ownerAlias ∈ transition.context.expected.frame.retained
            rw [transition.expectedFrameEq]
            exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
          have hrepresentable : t.refTarget = true ∨ t.isSlice = true := by
            cases t <;> simp_all [Ty.ownerElem?, Ty.refTarget, Ty.isSlice]
          have hAliasSource : AliasAt m W env s1.store ownerAlias (.ref l) :=
            AliasAt.ofAliasPlace hAliasQuery hplaceType hrp (Or.inl ⟨hrt, hl, hheader⟩)
              hg hrepresentable
          have hAliasPost := (hret2 ownerAlias hAliasMem).typed (.ref l) hAliasSource
          have hLocOkPost : LocOk m W.G s2.store l t := by
            rcases hAliasPost.1 with ⟨l', heq, hloc⟩
            cases heq
            rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
            · exact hloc
            · cases t <;> simp_all [Ty.isSlice, Ty.ownerElem?]
          exact access hp hLocOkPost hg
            (fun t' ht' => Or.inr (Or.inr (Or.inl (hE3.2.2.1 t' (hin t' ht')))))
      refine sat_checkedAppendLoc_bind hlt hownerElem hvw.1 hvs (fun st' i happ hstep => ?_)
      simp only [sat_pure]
      have hrootsAppend : PreservesRootTypes m W.G observation.roots s2.store st' :=
        statementAppendPreservesRootTypes hlt happ hstep
      obtain ⟨_, hvaluesAppend, hsafeAppend, hretainedAppend, hpilotAppend⟩ :=
        statementFlatStepPreservation (s := s2) (s' := { s2 with store := st' })
          (env := env) (aliases := childEc.retained) hsafe2 hrootsAppend hstep
      have hfootAppend : Footprint (insts env) (Dset W) s2 { s2 with store := st' } :=
        Footprint.of_flatStep hstep
      have hretained : RetainsAliases m W env s.store st' ec.retained :=
        hret1.trans ((hret2.trans hretainedAppend).subset (fun alias hmem =>
          ec.child_retained_subset rfl 1 (DemandNode.view src) .view
            hchildV hphaseV hmem))
      have hX := (hX1.trans hX2).trans hfootAppend
      exact ⟨houtputV ▸ hF2.flatStep hstep, hX.toS,
        (hroots1.trans hroots2).trans hrootsAppend,
        (hvalues1.trans hvalues2).trans hvaluesAppend, hsafeAppend, hretained,
        fun hprofile' => StoreLe.trans (hpilot1 hprofile')
          (StoreLe.trans (hpilot2 hprofile') (hpilotAppend hprofile')),
        TSame.refl _, hT.ext hX.dom hcur,
        hforbiddenPre.trans (statementStoreForbidden hF2 hg hdisjoint
          (append_except_owner _ _ _ _ _ happ)),
        hmutationPre.trans (statementSingleRootMutation
          (append_except_owner _ _ _ _ _ happ) hchanged), rfl⟩
    · simp [Ty.isRefLike] at hrl
      cases t <;> simp [Ty.isRefLike, Ty.ownerElem?] at hrl hownerElem
    · rw [h3] at hownerElem
      simp [Ty.ownerElem?] at hownerElem
  | popN owner count org =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨typingStart, hrequireShrink, horg, t, bindingWritable, contentsWritable, tn1, hownerTy,
      element, tn2, hownerElement, width, tn3, hcountTy, hcountInt, hwrite,
      htenvEq, htnEq⟩ := ht
    obtain ⟨rho, r1, hrpOwner, _, r2, hrpCount, r3, hreads, r4, hshrinks, haborts⟩ := hr
    have hfinal4E := (PMono.noteAborts r4 () rst' haborts).2
    have hfinal3E := (PMono.addShrinks rho r3 () r4 hshrinks).2.trans hfinal4E
    have hfinalE := (PMono.addReads rho r2 () r3 hreads).2.trans hfinal3E
    have hnoteAborts : PMonoRebinds noteAborts := by
      unfold noteAborts
      exact PMonoRebinds.modify _ (fun _ _ h => h)
    have hfinal4R := hnoteAborts r4 () rst' haborts
    have hfinal3R := (PMonoRebinds.addShrinks rho r3 () r4 hshrinks).trans hfinal4R
    have hfinalR := (PMonoRebinds.addReads rho r2 () r3 hreads).trans hfinal3R
    have hE4 : EffLe r4.eff W.E := (PMono.noteAborts r4 () rst' haborts).2.trans hE
    have hE3 : EffLe r3.eff W.E := ((PMono.addShrinks rho) r3 () r4 hshrinks).2.trans hE4
    have hE2 : EffLe r2.eff W.E := ((PMono.addReads rho) r2 () r3 hreads).2.trans hE3
    have hE1 : EffLe r1.eff W.E := (rpExpr_mono hrpCount).2.trans hE2
    obtain ⟨_, hinShrinks⟩ := statementAddShrinksOk _ _ _ hshrinks
    have hownerElem : t.ownerElem? = some element := by
      have h := (ownerElement_ok _ t element tn1 tn2 hownerElement).2.1
      exact h
    rcases htnEq with ⟨htenvEq', htnEq'⟩
    subst tenv'
    subst tn'
    simp only [execStmt]
    have hchildP : (DemandNode.statement (.popN owner count org)).child? 0 =
        some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
    have hvisibleP : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.popN owner count org)).visibleForChild tenv.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hresultP := statementPlaceChildSpec ih ec observation W tenv penv env s 0 owner hchildP
      hactive haccess hprotected hobserved hclassified hp hF hvisibleP
      (statementPopNPlaceInputSubset ec) typingStart tn1 t bindingWritable contentsWritable
      rst r1 rho hownerTy hrpOwner hE1
    have hchildC : (DemandNode.statement (.popN owner count org)).child? 1 =
        some (DemandNode.expression count) := by
      simp [DemandNode.child?, DemandNode.children]
    have hphaseC : DemandNodeHasPhase (DemandNode.expression count) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 1 count hchildC
    have hvisibleC : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.popN owner count org)).visibleForChild tenv.visible 1 := by
      simp [DemandNode.visibleForChild]
    have houtputC : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.expression count).visibleAfter
          ((DemandNode.statement (.popN owner count org)).visibleForChild active 1) =
          (DemandNode.statement (.popN owner count org)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 1 (DemandNode.expression count) .expression
          hchildC hphaseC
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.popN owner count org))
            stmtPlanContext.approvals.access
            ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 1 = some ⟨
                (DemandNode.statement (.popN owner count org)).visibleForChild
                  context.expected.frame.active 1,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildC]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp only [DemandNode.phaseFuture]
    refine Sat.bind hresultP ?_
    rintro l s1 ⟨hF1, hX1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hpl, hg, howner1, hforbidden1, hmutation1⟩
    have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hrpOwner
    have hinputC' := statementPopNCountInputFrame ec hactive hF1
    have hclassified1' : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store := by
      intro hprofile
      exact hF.classifiedParameters_advance (hclassified hprofile) hX1
    have hresultC := statementExprChildSpecAtFrame ih ec observation W tenv tenv penv env s1
      1 count hchildC hactive haccess hprotected hsafe1 hclassified1' hp childEc rfl hinputC'
      hvisibleC childEc.retained (fun _ hmem => hmem) _ _ _ _ _ _ hcountTy hrpCount hE2
    refine Sat.bind hresultC ?_
    rintro countValue s2 ⟨hF2, hX2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hcountValue, hcountGam, hcountOwner, hforbidden2, hforbiddenCount2, hmutation2⟩
    have hforbiddenPre := hforbidden1.trans hforbidden2
    have hmutationPre := ((hmutation1.weaken (effectMutationRoots.mono m penv.impl
      (rpExpr_mono hrpCount).2 (rpExpr_rebinds_mono hrpCount))).trans hmutation2).weaken
        (effectMutationRoots.mono m penv.impl hfinalE hfinalR)
    have houtputF : childEc.outputFuture = ec.outputFuture := houtputC
    rw [hwrite] at hcountValue
    have hcountTy' : ∃ width value, countValue = .int width value := by
      cases countValue with
      | int width value => exact ⟨width, value, rfl⟩
      | _ => simp [HasTy, FlatTy] at hcountValue
    obtain ⟨width, countValueInt, rfl⟩ := hcountTy'
    have hlengthFrame : Frame m W tenv penv env s2 ec.outputFuture := by
      rw [← houtputF]
      exact hF2
    have hchanged := statementEffectMutationRoot hlengthFrame hg (effect := rst'.eff) (by
      intro target hmem
      simp only [effectMutationTargets, List.mem_append]
      exact Or.inl (Or.inr (hfinal4E.2.2.2.1 target (hinShrinks target hmem))))
    have hOwnerPlace : PlaceOk m W.G W.P penv env s1.store owner l t := hpl
    have hinOwnerShrink : ∀ target, target ∈ rootsTargets rho →
        target ∈ W.E.shrinks := by
      intro target htarget
      exact hE4.2.2.2.1 target (hinShrinks target htarget)
    have hLoc2 : LocTy s2.store l t := by
      rcases hpl with ⟨hrt, hloc, hheader⟩ |
        ⟨x, lv, si, v, hplace, hvar, hscope, hloc, hty, hrl, hroot, htyped⟩ |
        ⟨x, lv, mu0, mu, E, ann, hplace, hvar, hty, htarget, hflat, hpath, hann, hgam, hroot⟩
      · cases ec with
        | pilot profile active =>
          exact access hp (hloc.mono (hpilot2 profile)) hg
            (fun target htarget => Or.inr (Or.inr (Or.inr (hinOwnerShrink target htarget))))
        | @shrink profileContext profile context =>
          let transition := context.child rfl 1 (DemandNode.expression count) .expression
            hchildC hphaseC
          have hMod : tenv.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
          have hVars : tenv.vars = penv.impl.vars :=
            haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
          have hEnv : profileContext.approvals.access = penv.access := by
            have hAccessMod := haccess.2.2.1
            have hAccessImpl := haccess.2.2.2.1
            have hAccessCtx := haccess.2.2.2.2
            cases hAccessValue : profileContext.approvals.access
            rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
            unfold PEnv.access
            congr 1
          have hplaceType : penv.access.placeType? owner = some t :=
            tyPlace_accessType hMod hVars hownerTy
          have hOwnerRoots : ∃ roots, penv.access.placeRoots owner = .ok roots := by
            cases hroots : penv.access.placeRoots owner with
            | error err =>
              have hExpectation :
                  (DemandNode.statement (.popN owner count org)).childExpectation?
                    penv.access
                    ⟨path, .expression, context.expected.frame.active,
                      context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                    some ⟨(DemandNode.statement (.popN owner count org)).visibleForChild
                      context.expected.frame.active 1, context.expected.frame.future⟩ := by
                simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildC]
              have hbad :
                  (DemandNode.statement (.popN owner count org)).childFrame
                    penv.access path context.expected.frame 1 = .error err := by
                simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                  AccessEnv.aliasPlace, hplaceType, hownerElem, hroots,
                  Functor.map, Except.map]
              have htransition := transition.childFrameEq
              rw [hEnv] at htransition
              rw [hbad] at htransition
              cases htransition
            | ok roots => exact ⟨roots, rfl⟩
          obtain ⟨roots, hOwnerRoots⟩ := hOwnerRoots
          let ownerAlias : RetainedAlias :=
            ⟨.ref .mutable t, roots, .operand (path ++ [0])⟩
          have hAliasQuery : penv.access.aliasPlace (path ++ [0]) owner = .ok [ownerAlias] := by
            simp [AccessEnv.aliasPlace, hplaceType, hownerElem, hOwnerRoots, ownerAlias,
              Functor.map, Except.map]
          have hAliasQueryCtx : profileContext.approvals.access.aliasPlace
              (path ++ [0]) owner = .ok [ownerAlias] := by
            rw [hEnv]
            exact hAliasQuery
          have hnew : (DemandNode.statement (.popN owner count org)).retainedForChild
              profileContext.approvals.access path 1 = .ok [ownerAlias] := by
            simp [DemandNode.retainedForChild, hAliasQueryCtx]
          have hAliasMem : ownerAlias ∈ childEc.retained := by
            have hChild := DemandNode.childFrame_newAlias
              (result := transition.childFrame) (aliases := [ownerAlias])
              (alias := ownerAlias) transition.childFrameEq hnew
              (List.mem_cons.mpr (Or.inl rfl))
            change ownerAlias ∈ transition.context.expected.frame.retained
            rw [transition.expectedFrameEq]
            exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
          have hrepresentable : t.refTarget = true ∨ t.isSlice = true := by
            cases t <;> simp_all [Ty.ownerElem?, Ty.refTarget, Ty.isSlice]
          have hAliasSource : AliasAt m W env s1.store ownerAlias (.ref l) :=
            AliasAt.ofAliasPlace hAliasQuery hplaceType hrpOwner hOwnerPlace hg hrepresentable
          have hAliasPost := (hret2 ownerAlias hAliasMem).typed (.ref l) hAliasSource
          have hLocOkPost : LocOk m W.G s2.store l t := by
            rcases hAliasPost.1 with ⟨l', heq, hloc⟩
            cases heq
            rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
            · exact hloc
            · cases t <;> simp_all [Ty.isSlice, Ty.ownerElem?]
          exact access hp hLocOkPost hg
            (fun target htarget => Or.inr (Or.inr (Or.inr (hinOwnerShrink target htarget))))
      · cases t <;> simp_all [Ty.ownerElem?, Ty.isRefLike]
      · rw [htarget] at hownerElem
        simp [Ty.ownerElem?] at hownerElem
    cases t with
    | limited ownerElement capacity =>
      obtain ⟨ownerValue, hread, hflat⟩ := hLoc2
      cases ownerValue with
      | limited actualElement actualCapacity slots oldSize =>
        simp only [FlatTy] at hflat
        obtain ⟨rfl, rfl, hcapacity, hslotsSize, hslots⟩ := hflat
        have hLoc : LocTy s2.store l (.limited ownerElement capacity) :=
          ⟨_, hread, rfl, rfl, hcapacity, hslotsSize, hslots⟩
        simp only [expectInt, sat_pure_bind]
        have hlength : s2.store.length l = .ok oldSize := by simp [Store.length, hread]
        have hlengthStep : ∀ {f : Nat → M Flow} {Q : Flow → St → Prop},
            Sat (f oldSize) s2 Q → Sat (lengthLoc l >>= f) s2 Q := by
          intro f Q hk
          have heq : (lengthLoc l >>= f) s2 = f oldSize s2 := by
            show M.bind' (lengthLoc l) f s2 = _
            simp [M.bind', lengthLoc, hlength]
          unfold Sat
          rw [heq]
          exact hk
        apply hlengthStep
        split
        · simp [Sat, abortAt, M.stop]
        · obtain ⟨destination, htruncate⟩ := statementTruncateLimitedTotal hLoc
            ⟨oldSize, hlength, Nat.sub_le _ _⟩
          have hstep := statementTruncateLimitedFlatStep hLoc htruncate
          apply sat_statementTruncateLoc_bind htruncate
          simp only [sat_pure]
          have hrootsTruncate : PreservesRootTypes m W.G observation.roots s2.store destination :=
            statementModifyPreservesRootTypes hstep.le hLoc htruncate
          obtain ⟨_, hvaluesTruncate, hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
            statementFlatStepPreservation (s := s2) (s' := { s2 with store := destination })
              (env := env) (aliases := childEc.retained) hsafe2 hrootsTruncate hstep
          have hfoot : Footprint (insts env) (Dset W) s2 { s2 with store := destination } :=
            Footprint.of_flatStep hstep
          have hX := (hX1.trans hX2).trans hfoot
          have hretained : RetainsAliases m W env s.store destination ec.retained :=
            hret1.trans ((hret2.trans hretainedTruncate).subset (fun alias hmem =>
              ec.child_retained_subset rfl 1 (DemandNode.expression count) .expression
                hchildC hphaseC hmem))
          exact ⟨hlengthFrame.flatStep hstep, hX.toS,
            (hroots1.trans hroots2).trans hrootsTruncate,
            (hvalues1.trans hvalues2).trans hvaluesTruncate, hsafeTruncate, hretained,
            fun hprofile => StoreLe.trans (hpilot1 hprofile)
              (StoreLe.trans (hpilot2 hprofile) (hpilotTruncate hprofile)),
            TSame.refl _, hT.ext hX.dom hcur,
            hforbiddenPre.trans (statementStoreForbidden hlengthFrame hg hdisjoint
              (truncate_except_owner s2.store destination l (oldSize - countValueInt.toNat) htruncate)),
            hmutationPre.trans (statementSingleRootMutation
              (truncate_except_owner s2.store destination l (oldSize - countValueInt.toNat) htruncate) hchanged), rfl⟩
      | _ => simp [FlatTy] at hflat
    | grow ownerElement =>
      have hLocOwner := hLoc2
      obtain ⟨ownerValue, hread, hflat⟩ := hLoc2
      cases ownerValue with
      | resizable actualElement slots =>
        simp only [FlatTy] at hflat
        obtain ⟨rfl, hslots⟩ := hflat
        simp only [expectInt, sat_pure_bind]
        have hlength : s2.store.length l = .ok slots.size := by simp [Store.length, hread]
        have hlengthStep : ∀ {f : Nat → M Flow} {Q : Flow → St → Prop},
            Sat (f slots.size) s2 Q → Sat (lengthLoc l >>= f) s2 Q := by
          intro f Q hk
          have heq : (lengthLoc l >>= f) s2 = f slots.size s2 := by
            show M.bind' (lengthLoc l) f s2 = _
            simp [M.bind', lengthLoc, hlength]
          unfold Sat
          rw [heq]
          exact hk
        apply hlengthStep
        split
        · simp [Sat, abortAt, M.stop]
        · obtain ⟨destination, htruncate⟩ := statementTruncateGrowTotal hLocOwner
            ⟨slots.size, hlength, Nat.sub_le _ _⟩
          apply sat_statementTruncateLoc_bind htruncate
          simp only [sat_pure]
          have hmutationPhase : DemandNodeHasPhase
              (DemandNode.statement (.popN owner count org)) .mutation := by
            simp [DemandNodeHasPhase, DemandNode.phaseMatches]
          have haccessMutation :=
            (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
          have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
          have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
          change (statementMutationContext ec hmutationPhase).ActiveMatches tenv at hactiveMutation
          change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture at houtputMutation
          have hretainedMutation : ∀ alias, alias ∈ ec.retained →
              alias ∈ (statementMutationContext ec hmutationPhase).retained := by
            intro alias hmem
            exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
          change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv at haccessMutation
          cases hmutation : statementMutationContext ec hmutationPhase with
          | pilot profile active =>
            simp [requireShrink, rej, hF.mod_t, profile] at hrequireShrink
            change Except.error _ = Except.ok _ at hrequireShrink
            cases hrequireShrink
          | @shrink pc profile mutationContext =>
            have hdirect : (DemandNode.statement (.popN owner count org)).directShrinkPlace? =
                some owner := by simp [DemandNode.directShrinkPlace?]
            obtain ⟨ownerRequest, hownerResult, hownerRequests⟩ :=
              mutationContext.sourceAt.directShrinkOwner_result rfl hdirect pc.approvals.accessMatches
            obtain ⟨approval, hpath, hsameOwner, hphase, hframe⟩ :=
              mutationContext.directShrinkApproval hdirect hownerResult
            rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
            have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
              haccessMutation hownerResult hownerTy hrpOwner hg
            have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
              intro x hx
              exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
            have hfutureNeeded : ∀ x, x ∈ ec.outputFuture → x ∈ approval.point.future := by
              intro x hx
              apply (hframe.2.1 x).2
              change x ∈ mutationContext.expected.frame.future
              change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
              rw [houtputMutation]
              exact hx
            have happrovalAccess : approval.access = pc.approvals.access :=
              Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
            have haccessEq : approval.access = penv.access := happrovalAccess.trans hownerFacts.1
            have happrovalTy := hsameOwner ▸ hownerFacts.2.1
            have happrovalRoot := hsameOwner ▸ hownerFacts.2.2
            have hretainedNeeded : ∀ alias, alias ∈ ec.retained → alias ∈ approval.point.retained := by
              intro alias hmem
              exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
            have hheader : l.path = [] := hpl.ownerHeader (by simp [Ty.ownerElem?])
            have hElement : ownerElement = element := by simpa [Ty.ownerElem?] using hownerElem
            have hflat : ownerElement.flat = true := by
              rw [hElement]
              exact statementOwnerElementFlat hpl hownerElem
            have hshrinkAuthority :
                (ec.mayShrink W.ownerP observation l.root ∨
                  ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
                (∀ g, l.root = .global g → g < W.G) := by
              have hownerP : Gam env W.ownerP rho l.root :=
                howner1 ⟨ownerElement, Or.inl rfl⟩
              have hrequestFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hrpOwner hownerP
              have hclassifiedPost := hF.classifiedParameters_advance (hclassified profile) (hX1.trans hX2)
              have authority := statementDirectShrinkAuthority mutationContext profile hdirect
                hownerResult hrequestFacts.2.1 (Or.inl rfl)
                hrequestFacts.2.2 hownerP hlengthFrame hp hclassifiedPost hsafe2.typed hheader hLocOwner
                hinOwnerShrink
              have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase W.ownerP observation l.root
              change (statementMutationContext ec hmutationPhase).mayShrink W.ownerP observation l.root ↔
                ec.mayShrink W.ownerP observation l.root at hmay
              rw [hmutation] at hmay
              exact ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
            obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate, hsafeTruncate,
                hretainedTruncate, hpilotTruncate⟩ :=
              statementResizableTruncatePreservation hlengthFrame haccessEq happrovalTy
                (Or.inl rfl) happrovalRoot hLocOwner hvisibleActive hfutureNeeded profile
                hprotected hsafe2 hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
                hretainedNeeded htruncate
            have hX := (hX1.trans hX2).trans hfoot
            have hretained : RetainsAliases m W env s.store destination ec.retained :=
              hret1.trans ((hret2.subset (fun alias hmem =>
                ec.child_retained_subset rfl 1 (DemandNode.expression count) .expression
                  hchildC hphaseC hmem)).trans hretainedTruncate)
            exact ⟨hpostFrame, hX.toS, (hroots1.trans hroots2).trans hrootsTruncate,
              (hvalues1.trans hvalues2).trans hvaluesTruncate, hsafeTruncate, hretained,
              fun hprofile => StoreLe.trans (hpilot1 hprofile)
                (StoreLe.trans (hpilot2 hprofile) (hpilotTruncate hprofile)),
              TSame.refl _, hT.ext hX.dom hcur,
              hforbiddenPre.trans (statementStoreForbidden hlengthFrame hg hdisjoint
                (truncate_except_owner s2.store destination l (slots.size - countValueInt.toNat) htruncate)),
              hmutationPre.trans (statementSingleRootMutation
                (truncate_except_owner s2.store destination l (slots.size - countValueInt.toNat) htruncate) hchanged), rfl⟩
      | _ => simp [FlatTy] at hflat
    | growshrink ownerElement =>
      have hLocOwner := hLoc2
      obtain ⟨ownerValue, hread, hflat⟩ := hLoc2
      cases ownerValue with
      | resizable actualElement slots =>
        simp only [FlatTy] at hflat
        obtain ⟨rfl, hslots⟩ := hflat
        simp only [expectInt, sat_pure_bind]
        have hlength : s2.store.length l = .ok slots.size := by simp [Store.length, hread]
        have hlengthStep : ∀ {f : Nat → M Flow} {Q : Flow → St → Prop},
            Sat (f slots.size) s2 Q → Sat (lengthLoc l >>= f) s2 Q := by
          intro f Q hk
          have heq : (lengthLoc l >>= f) s2 = f slots.size s2 := by
            show M.bind' (lengthLoc l) f s2 = _
            simp [M.bind', lengthLoc, hlength]
          unfold Sat
          rw [heq]
          exact hk
        apply hlengthStep
        split
        · simp [Sat, abortAt, M.stop]
        · obtain ⟨destination, htruncate⟩ := statementTruncateGrowshrinkTotal hLocOwner
            ⟨slots.size, hlength, Nat.sub_le _ _⟩
          apply sat_statementTruncateLoc_bind htruncate
          simp only [sat_pure]
          have hmutationPhase : DemandNodeHasPhase
              (DemandNode.statement (.popN owner count org)) .mutation := by
            simp [DemandNodeHasPhase, DemandNode.phaseMatches]
          have haccessMutation :=
            (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
          have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
          have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
          change (statementMutationContext ec hmutationPhase).ActiveMatches tenv at hactiveMutation
          change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture at houtputMutation
          have hretainedMutation : ∀ alias, alias ∈ ec.retained →
              alias ∈ (statementMutationContext ec hmutationPhase).retained := by
            intro alias hmem
            exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
          change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv at haccessMutation
          cases hmutation : statementMutationContext ec hmutationPhase with
          | pilot profile active =>
            simp [requireShrink, rej, hF.mod_t, profile] at hrequireShrink
            change Except.error _ = Except.ok _ at hrequireShrink
            cases hrequireShrink
          | @shrink pc profile mutationContext =>
            have hdirect : (DemandNode.statement (.popN owner count org)).directShrinkPlace? =
                some owner := by simp [DemandNode.directShrinkPlace?]
            obtain ⟨ownerRequest, hownerResult, hownerRequests⟩ :=
              mutationContext.sourceAt.directShrinkOwner_result rfl hdirect pc.approvals.accessMatches
            obtain ⟨approval, hpath, hsameOwner, hphase, hframe⟩ :=
              mutationContext.directShrinkApproval hdirect hownerResult
            rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
            have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
              haccessMutation hownerResult hownerTy hrpOwner hg
            have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
              intro x hx
              exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
            have hfutureNeeded : ∀ x, x ∈ ec.outputFuture → x ∈ approval.point.future := by
              intro x hx
              apply (hframe.2.1 x).2
              change x ∈ mutationContext.expected.frame.future
              change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
              rw [houtputMutation]
              exact hx
            have happrovalAccess : approval.access = pc.approvals.access :=
              Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
            have haccessEq : approval.access = penv.access := happrovalAccess.trans hownerFacts.1
            have happrovalTy := hsameOwner ▸ hownerFacts.2.1
            have happrovalRoot := hsameOwner ▸ hownerFacts.2.2
            have hretainedNeeded : ∀ alias, alias ∈ ec.retained → alias ∈ approval.point.retained := by
              intro alias hmem
              exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
            have hheader : l.path = [] := hpl.ownerHeader (by simp [Ty.ownerElem?])
            have hElement : ownerElement = element := by simpa [Ty.ownerElem?] using hownerElem
            have hflat : ownerElement.flat = true := by
              rw [hElement]
              exact statementOwnerElementFlat hpl hownerElem
            have hshrinkAuthority :
                (ec.mayShrink W.ownerP observation l.root ∨
                  ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
                (∀ g, l.root = .global g → g < W.G) := by
              have hownerP : Gam env W.ownerP rho l.root :=
                howner1 ⟨ownerElement, Or.inr rfl⟩
              have hrequestFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hrpOwner hownerP
              have hclassifiedPost := hF.classifiedParameters_advance (hclassified profile) (hX1.trans hX2)
              have authority := statementDirectShrinkAuthority mutationContext profile hdirect
                hownerResult hrequestFacts.2.1 (Or.inr rfl)
                hrequestFacts.2.2 hownerP hlengthFrame hp hclassifiedPost hsafe2.typed hheader hLocOwner
                hinOwnerShrink
              have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase W.ownerP observation l.root
              change (statementMutationContext ec hmutationPhase).mayShrink W.ownerP observation l.root ↔
                ec.mayShrink W.ownerP observation l.root at hmay
              rw [hmutation] at hmay
              exact ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
            obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate, hsafeTruncate,
                hretainedTruncate, hpilotTruncate⟩ :=
              statementResizableTruncatePreservation hlengthFrame haccessEq happrovalTy
                (Or.inr rfl) happrovalRoot hLocOwner hvisibleActive hfutureNeeded profile
                hprotected hsafe2 hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
                hretainedNeeded htruncate
            have hX := (hX1.trans hX2).trans hfoot
            have hretained : RetainsAliases m W env s.store destination ec.retained :=
              hret1.trans ((hret2.subset (fun alias hmem =>
                ec.child_retained_subset rfl 1 (DemandNode.expression count) .expression
                  hchildC hphaseC hmem)).trans hretainedTruncate)
            exact ⟨hpostFrame, hX.toS, (hroots1.trans hroots2).trans hrootsTruncate,
              (hvalues1.trans hvalues2).trans hvaluesTruncate, hsafeTruncate, hretained,
              fun hprofile => StoreLe.trans (hpilot1 hprofile)
                (StoreLe.trans (hpilot2 hprofile) (hpilotTruncate hprofile)),
              TSame.refl _, hT.ext hX.dom hcur,
              hforbiddenPre.trans (statementStoreForbidden hlengthFrame hg hdisjoint
                (truncate_except_owner s2.store destination l (slots.size - countValueInt.toNat) htruncate)),
              hmutationPre.trans (statementSingleRootMutation
                (truncate_except_owner s2.store destination l (slots.size - countValueInt.toNat) htruncate) hchanged), rfl⟩
      | _ => simp [FlatTy] at hflat
    | _ => simp [Ty.ownerElem?] at hownerElem
  | clear owner org =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hrequireShrink, horg, t, bindingWritable, contentsWritable, tn1, hownerTy,
      element, tn2, hownerElement, hwrite, htenvEq, htnEq⟩ := ht
    obtain ⟨rho, r1, hrpOwner, r2, hreads, hshrinks⟩ := hr
    have hfinal2E := (PMono.addShrinks rho r2 () rst' hshrinks).2
    have hfinalE := (PMono.addReads rho r1 () r2 hreads).2.trans hfinal2E
    have hfinal2R := PMonoRebinds.addShrinks rho r2 () rst' hshrinks
    have hfinalR := (PMonoRebinds.addReads rho r1 () r2 hreads).trans hfinal2R
    have hE3 : EffLe rst'.eff W.E := hE
    have hE2 : EffLe r2.eff W.E := (PMono.addShrinks rho r2 () rst' hshrinks).2.trans hE3
    have hE1 : EffLe r1.eff W.E := (PMono.addReads rho r1 () r2 hreads).2.trans hE2
    obtain ⟨_, hinShrinks⟩ := statementAddShrinksOk rho r2 ((), rst') hshrinks
    have hownerElem : t.ownerElem? = some element := by
      have h := (ownerElement_ok _ t element _ _ hownerElement).2.1
      exact h
    subst tenv'
    subst tn'
    simp only [execStmt]
    have hchildP : (DemandNode.statement (.clear owner org)).child? 0 =
        some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
    have hvisibleP : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.clear owner org)).visibleForChild tenv.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hresultP := statementPlaceChildSpec ih ec observation W tenv penv env s 0 owner hchildP
      hactive haccess hprotected hobserved hclassified hp hF hvisibleP
      (statementClearPlaceInputSubset ec) _ _ _ _ _ _ _ _ hownerTy hrpOwner hE1
    have hchildPhase : DemandNodeHasPhase (DemandNode.place owner) .place := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    refine Sat.bind hresultP ?_
    rintro l s1 ⟨hF1, hX1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hpl, hg, howner1, hforbidden1, hmutation1⟩
    have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hrpOwner
    have houtputP :
        (ec.child rfl 0 (DemandNode.place owner) .place hchildP hchildPhase).outputFuture =
          ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.place owner).visibleAfter
          ((DemandNode.statement (.clear owner org)).visibleForChild active 0) =
          (DemandNode.statement (.clear owner org)).visibleAfter active
        simp [DemandNode.visibleAfter, DemandNode.visibleForChild]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.place owner) .place hchildP hchildPhase
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.clear owner org))
            stmtPlanContext.approvals.access
            ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.clear owner org)).visibleForChild
                  context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildP]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp only [DemandNode.phaseFuture]
    have hframe1 : Frame m W tenv penv env s1 ec.outputFuture := by
      rw [← houtputP]
      exact hF1
    have hLoc : LocTy s1.store l t := by
      rcases hpl with ⟨hrt, hloc, hheader⟩ |
        ⟨x, lv, si, v, hplace, hvar, hscope, hloc, hty, hrl, hroot, htyped⟩ |
        ⟨x, lv, mu0, mu, E, ann, hplace, hvar, hty, htarget, hflat, hpath, hann, hgam, hroot⟩
      · exact access hp hloc hg (fun target htarget =>
          Or.inr (Or.inr (Or.inr (hE3.2.2.2.1 target (hinShrinks target htarget)))))
      · cases t <;> simp_all [Ty.ownerElem?, Ty.isRefLike]
      · rw [htarget] at hownerElem
        simp [Ty.ownerElem?] at hownerElem
    have hforbiddenPre := hforbidden1
    have hmutationPre := hmutation1.weaken (effectMutationRoots.mono m penv.impl hfinalE hfinalR)
    have hchanged := statementEffectMutationRoot hframe1 hg (effect := rst'.eff) (by
      intro target hmem
      simp only [effectMutationTargets, List.mem_append]
      exact Or.inl (Or.inr (hinShrinks target hmem)))
    have htruncate := statementTruncateOwnerTotal hLoc hownerElem
    obtain ⟨s2, htruncate⟩ := htruncate
    cases t with
    | limited ownerElement capacity =>
      have hstep := statementTruncateLimitedFlatStep hLoc htruncate
      apply sat_statementTruncateLoc_bind htruncate
      simp only [sat_pure]
      have hrootsTruncate : PreservesRootTypes m W.G observation.roots s1.store s2 :=
        statementModifyPreservesRootTypes hstep.le hLoc htruncate
      obtain ⟨_, hvaluesTruncate, hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
        statementFlatStepPreservation (s := s1) (s' := { s1 with store := s2 })
          (env := env) (aliases := ec.retained) hsafe1 hrootsTruncate hstep
      have hfoot : Footprint (insts env) (Dset W) s1 { s1 with store := s2 } :=
        Footprint.of_flatStep hstep
      have hX := hX1.trans hfoot
      have hretained := hret1.trans hretainedTruncate
      exact ⟨hframe1.flatStep hstep, hX.toS, hroots1.trans hrootsTruncate,
        hvalues1.trans hvaluesTruncate, hsafeTruncate, hretained,
        fun hprofile => StoreLe.trans (hpilot1 hprofile) (hpilotTruncate hprofile),
        TSame.refl _, hT.ext hX.dom hcur,
        hforbiddenPre.trans (statementStoreForbidden hframe1 hg hdisjoint
          (truncate_except_owner s1.store s2 l 0 htruncate)),
        hmutationPre.trans (statementSingleRootMutation
          (truncate_except_owner s1.store s2 l 0 htruncate) hchanged), rfl⟩
    | grow ownerElement =>
      have hmutationPhase : DemandNodeHasPhase
          (DemandNode.statement (.clear owner org)) .mutation := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      have haccessMutation :=
        (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
      have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
      have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
      change (statementMutationContext ec hmutationPhase).ActiveMatches tenv at hactiveMutation
      change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture at houtputMutation
      have hretainedMutation : ∀ alias, alias ∈ ec.retained →
          alias ∈ (statementMutationContext ec hmutationPhase).retained := by
        intro alias hmem
        exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
      change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv at haccessMutation
      cases hmutation : statementMutationContext ec hmutationPhase with
      | pilot profile active =>
        simp [requireShrink, rej, hF.mod_t, profile] at hrequireShrink
        change Except.error _ = Except.ok _ at hrequireShrink
        cases hrequireShrink
      | @shrink pc profile mutationContext =>
        have hdirect : (DemandNode.statement (.clear owner org)).directShrinkPlace? =
            some owner := by simp [DemandNode.directShrinkPlace?]
        obtain ⟨ownerRequest, hownerResult, hownerRequests⟩ :=
          mutationContext.sourceAt.directShrinkOwner_result rfl hdirect pc.approvals.accessMatches
        obtain ⟨approval, hpath, hsameOwner, hphase, hframe⟩ :=
          mutationContext.directShrinkApproval hdirect hownerResult
        rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
        have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
          haccessMutation hownerResult hownerTy hrpOwner hg
        have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
          intro x hx
          exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
        have hfutureNeeded : ∀ x, x ∈ ec.outputFuture → x ∈ approval.point.future := by
          intro x hx
          apply (hframe.2.1 x).2
          change x ∈ mutationContext.expected.frame.future
          change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
          rw [houtputMutation]
          exact hx
        have happrovalAccess : approval.access = pc.approvals.access :=
          Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
        have haccessEq : approval.access = penv.access := happrovalAccess.trans hownerFacts.1
        have happrovalTy := hsameOwner ▸ hownerFacts.2.1
        have happrovalRoot := hsameOwner ▸ hownerFacts.2.2
        have hretainedNeeded : ∀ alias, alias ∈ ec.retained → alias ∈ approval.point.retained := by
          intro alias hmem
          exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
        have hheader : l.path = [] := hpl.ownerHeader (by simp [Ty.ownerElem?])
        have hElement : ownerElement = element := by simpa [Ty.ownerElem?] using hownerElem
        have hflat : ownerElement.flat = true := by
          rw [hElement]
          exact statementOwnerElementFlat hpl hownerElem
        have hshrinkAuthority :
            (ec.mayShrink W.ownerP observation l.root ∨
              ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
            (∀ g, l.root = .global g → g < W.G) := by
          have hownerP : Gam env W.ownerP rho l.root :=
            howner1 ⟨ownerElement, Or.inl rfl⟩
          have hrequestFacts := statementCheckedShrinkOwnerFacts (W := W)
            haccessMutation hownerResult hownerTy hrpOwner hownerP
          have hclassifiedPost := hF.classifiedParameters_advance (hclassified profile) hX1
          have authority := statementDirectShrinkAuthority mutationContext profile hdirect
            hownerResult hrequestFacts.2.1 (Or.inl rfl)
            hrequestFacts.2.2 hownerP hframe1 hp hclassifiedPost hsafe1.typed hheader hLoc
            (fun target htarget => hE3.2.2.2.1 target (hinShrinks target htarget))
          have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase W.ownerP observation l.root
          change (statementMutationContext ec hmutationPhase).mayShrink W.ownerP observation l.root ↔
            ec.mayShrink W.ownerP observation l.root at hmay
          rw [hmutation] at hmay
          exact ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
        obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate, hsafeTruncate,
            hretainedTruncate, hpilotTruncate⟩ :=
          statementResizableTruncatePreservation hframe1 haccessEq happrovalTy
            (Or.inl rfl) happrovalRoot hLoc hvisibleActive hfutureNeeded profile
            hprotected hsafe1 hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
            hretainedNeeded htruncate
        apply sat_statementTruncateLoc_bind htruncate
        simp only [sat_pure]
        have hX := hX1.trans hfoot
        exact ⟨hpostFrame, hX.toS, hroots1.trans hrootsTruncate,
          hvalues1.trans hvaluesTruncate, hsafeTruncate, hret1.trans hretainedTruncate,
          fun hprofile => StoreLe.trans (hpilot1 hprofile) (hpilotTruncate hprofile),
          TSame.refl _, hT.ext hX.dom hcur,
          hforbiddenPre.trans (statementStoreForbidden hframe1 hg hdisjoint
            (truncate_except_owner s1.store s2 l 0 htruncate)),
          hmutationPre.trans (statementSingleRootMutation
            (truncate_except_owner s1.store s2 l 0 htruncate) hchanged), rfl⟩
    | growshrink ownerElement =>
      have hmutationPhase : DemandNodeHasPhase
          (DemandNode.statement (.clear owner org)) .mutation := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      have haccessMutation :=
        (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
      have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
      have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
      change (statementMutationContext ec hmutationPhase).ActiveMatches tenv at hactiveMutation
      change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture at houtputMutation
      have hretainedMutation : ∀ alias, alias ∈ ec.retained →
          alias ∈ (statementMutationContext ec hmutationPhase).retained := by
        intro alias hmem
        exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
      change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv at haccessMutation
      cases hmutation : statementMutationContext ec hmutationPhase with
      | pilot profile active =>
        simp [requireShrink, rej, hF.mod_t, profile] at hrequireShrink
        change Except.error _ = Except.ok _ at hrequireShrink
        cases hrequireShrink
      | @shrink pc profile mutationContext =>
        have hdirect : (DemandNode.statement (.clear owner org)).directShrinkPlace? =
            some owner := by simp [DemandNode.directShrinkPlace?]
        obtain ⟨ownerRequest, hownerResult, hownerRequests⟩ :=
          mutationContext.sourceAt.directShrinkOwner_result rfl hdirect pc.approvals.accessMatches
        obtain ⟨approval, hpath, hsameOwner, hphase, hframe⟩ :=
          mutationContext.directShrinkApproval hdirect hownerResult
        rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
        have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
          haccessMutation hownerResult hownerTy hrpOwner hg
        have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
          intro x hx
          exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
        have hfutureNeeded : ∀ x, x ∈ ec.outputFuture → x ∈ approval.point.future := by
          intro x hx
          apply (hframe.2.1 x).2
          change x ∈ mutationContext.expected.frame.future
          change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
          rw [houtputMutation]
          exact hx
        have happrovalAccess : approval.access = pc.approvals.access :=
          Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
        have haccessEq : approval.access = penv.access := happrovalAccess.trans hownerFacts.1
        have happrovalTy := hsameOwner ▸ hownerFacts.2.1
        have happrovalRoot := hsameOwner ▸ hownerFacts.2.2
        have hretainedNeeded : ∀ alias, alias ∈ ec.retained → alias ∈ approval.point.retained := by
          intro alias hmem
          exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
        have hheader : l.path = [] := hpl.ownerHeader (by simp [Ty.ownerElem?])
        have hElement : ownerElement = element := by simpa [Ty.ownerElem?] using hownerElem
        have hflat : ownerElement.flat = true := by
          rw [hElement]
          exact statementOwnerElementFlat hpl hownerElem
        have hshrinkAuthority :
            (ec.mayShrink W.ownerP observation l.root ∨
              ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
            (∀ g, l.root = .global g → g < W.G) := by
          have hownerP : Gam env W.ownerP rho l.root :=
            howner1 ⟨ownerElement, Or.inr rfl⟩
          have hrequestFacts := statementCheckedShrinkOwnerFacts (W := W)
            haccessMutation hownerResult hownerTy hrpOwner hownerP
          have hclassifiedPost := hF.classifiedParameters_advance (hclassified profile) hX1
          have authority := statementDirectShrinkAuthority mutationContext profile hdirect
            hownerResult hrequestFacts.2.1 (Or.inr rfl)
            hrequestFacts.2.2 hownerP hframe1 hp hclassifiedPost hsafe1.typed hheader hLoc
            (fun target htarget => hE3.2.2.2.1 target (hinShrinks target htarget))
          have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase W.ownerP observation l.root
          change (statementMutationContext ec hmutationPhase).mayShrink W.ownerP observation l.root ↔
            ec.mayShrink W.ownerP observation l.root at hmay
          rw [hmutation] at hmay
          exact ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
        obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate, hsafeTruncate,
            hretainedTruncate, hpilotTruncate⟩ :=
          statementResizableTruncatePreservation hframe1 haccessEq happrovalTy
            (Or.inr rfl) happrovalRoot hLoc hvisibleActive hfutureNeeded profile
            hprotected hsafe1 hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
            hretainedNeeded htruncate
        apply sat_statementTruncateLoc_bind htruncate
        simp only [sat_pure]
        have hX := hX1.trans hfoot
        exact ⟨hpostFrame, hX.toS, hroots1.trans hrootsTruncate,
          hvalues1.trans hvaluesTruncate, hsafeTruncate, hret1.trans hretainedTruncate,
          fun hprofile => StoreLe.trans (hpilot1 hprofile) (hpilotTruncate hprofile),
          TSame.refl _, hT.ext hX.dom hcur,
          hforbiddenPre.trans (statementStoreForbidden hframe1 hg hdisjoint
            (truncate_except_owner s1.store s2 l 0 htruncate)),
          hmutationPre.trans (statementSingleRootMutation
            (truncate_except_owner s1.store s2 l 0 htruncate) hchanged), rfl⟩
    | _ => simp [Ty.ownerElem?] at hownerElem
  | resize owner size fill o =>
    rw [tyStmt] at ht
    rcases (st_bind_ok _ _ _ _).1 ht with ⟨_, s1, hrequire, hrestTy⟩
    rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨_, s2, horg, hrestTy⟩
    rcases (st_bind_ok _ _ _ _).1 hrestTy with
      ⟨info, n1, hownerTy, hrestTy⟩
    obtain ⟨t, bw, cw⟩ := info
    rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨el, s3, hownerElement, hrestTy⟩
    rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨sizeTy, s4, hsizeTy, hrestTy⟩
    rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨sizeWidth, s5, hsizeInt, hrestTy⟩
    rw [rpStmt] at hr
    rcases (st_bind_ok _ _ _ _).1 hr with
      ⟨ownerRoots, r1, hownerRp, hrestRp⟩
    rcases (st_bind_ok _ _ _ _).1 hrestRp with
      ⟨sizeRoots, r2, hsizeRp, hrestRp⟩
    cases fill with
    | none =>
      simp only at hrestTy hrestRp
      rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨_, s6, hwrite, hrestTy⟩
      simp [requireWrite] at hwrite hrestTy
      rcases hrestTy with ⟨rfl, rfl⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r3, hreads, hrestRp⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r4, hshrinks, hrestRp⟩
      have haborts : noteAborts r4 = Except.ok ((), rst') := hrestRp
      have hE4 := (PMono.noteAborts _ _ _ haborts).2.trans hE
      have hE3 := (PMono.addShrinks ownerRoots _ _ _ hshrinks).2.trans hE4
      have hE2 := (PMono.addReads ownerRoots _ _ _ hreads).2.trans hE3
      have hE1 := (rpExpr_mono hsizeRp).2.trans hE2
      simp only [execStmt]
      have hchildP : (DemandNode.statement (.resize owner size none o)).child? 0 =
          some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
      have hvisibleP : ∀ x, x ∈ tenv.visible ↔
          x ∈ (DemandNode.statement (.resize owner size none o)).visibleForChild tenv.visible 0 := by
        simp [DemandNode.visibleForChild]
      have hresultP := statementPlaceChildSpec ih ec observation W tenv penv env s 0 owner hchildP
        hactive haccess hprotected hobserved hclassified hp hF hvisibleP
        (statementResizePlaceInputSubset ec) s2 n1 t bw cw rst r1 ownerRoots hownerTy hownerRp hE1
      refine Sat.bind hresultP ?_
      rintro l sPlace ⟨hFPlace, hXPlace, hrootsPlace, hvaluesPlace, hsafePlace,
        hretPlace, hpilotPlace, hplace, hgamPlace⟩
      have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hownerRp
      have hchildS : (DemandNode.statement (.resize owner size none o)).child? 1 =
          some (DemandNode.expression size) := by simp [DemandNode.child?, DemandNode.children]
      have hphaseS : DemandNodeHasPhase (DemandNode.expression size) .expression := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      have hvisibleS : ∀ x, x ∈ tenv.visible ↔
          x ∈ (DemandNode.statement (.resize owner size none o)).visibleForChild tenv.visible 1 := by
        simp [DemandNode.visibleForChild]
      let sizeEc := statementExprChildContext ec 1 size hchildS
      have hFSize := statementResizeSizeInputFrame ec hactive hFPlace
      have hclassifiedPlace : m.profile = .shrink →
          ClassifiedParameters m W.P W.D observation sPlace.store := by
        intro hprofile
        exact hF.classifiedParameters_advance (hclassified hprofile) hXPlace
      have hresultSize := statementExprChildSpecAtFrame ih ec observation W tenv tenv penv env sPlace
        1 size hchildS hactive haccess hprotected hsafePlace hclassifiedPlace hp sizeEc rfl hFSize
        hvisibleS sizeEc.retained (fun _ hmem => hmem) s3 s4 sizeTy r1 r2 sizeRoots
        hsizeTy hsizeRp hE2
      refine Sat.bind hresultSize ?_
      rintro sizeValue sSize ⟨hFSizeOut, hXSize, hrootsSize, hvaluesSize, hsafeSize,
        hretSize, hpilotSize, hsizeValueTy, hsizeGam⟩
      have hsizeIntFacts := (requireInt_ok "resize size" sizeTy s4 (sizeWidth, s5)).1 hsizeInt
      rw [hsizeIntFacts.1] at hsizeValueTy
      obtain ⟨sizeInt, rfl⟩ := hasTy_int hsizeValueTy
      simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
      have hownerElem : t.ownerElem? = some el :=
        (ownerElement_ok _ _ _ _ _ hownerElement).2.1
      have hownerRefTarget : t.refTarget = true := by
        rcases hplace with ⟨hrt, _, _⟩ |
          ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpath, _⟩
        · exact hrt
        · simp [Ty.isRefLike] at hrl
          cases t <;> simp [Ty.isRefLike, Ty.ownerElem?] at hrl hownerElem
        · rw [hpath] at hownerElem
          simp [Ty.ownerElem?] at hownerElem
      obtain ⟨_, hinRead⟩ := addReads_ok _ _ _ hreads
      obtain ⟨_, hinShrink⟩ := statementAddShrinksOk ownerRoots r3 ((), r4) hshrinks
      have hforbiddenPre := hgamPlace.2.2.1.trans hsizeGam.2.2.1
      have hnoteAborts : PMonoRebinds noteAborts := by
        unfold noteAborts
        exact PMonoRebinds.modify _ (fun _ _ h => h)
      have hfinal4R := hnoteAborts r4 () rst' haborts
      have hfinal3R := (PMonoRebinds.addShrinks ownerRoots r3 () r4 hshrinks).trans hfinal4R
      have hfinal2R := (PMonoRebinds.addReads ownerRoots r2 () r3 hreads).trans hfinal3R
      have hfinal4E := (PMono.noteAborts r4 () rst' haborts).2
      have hfinal3E := (PMono.addShrinks ownerRoots r3 () r4 hshrinks).2.trans hfinal4E
      have hfinal2E := (PMono.addReads ownerRoots r2 () r3 hreads).2.trans hfinal3E
      have hmutationPre :=
        ((hgamPlace.2.2.2.weaken (effectMutationRoots.mono m penv.impl
          (rpExpr_mono hsizeRp).2 (rpExpr_rebinds_mono hsizeRp))).trans hsizeGam.2.2.2.2).weaken
          (effectMutationRoots.mono m penv.impl hfinal2E hfinal2R)
      have hownerLoc : LocTy sSize.store l t := by
        have hlPlace : LocOk m W.G sPlace.store l t := by
          rcases hplace with ⟨_, hl, _⟩ |
            ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, hpath, _⟩
          · exact hl
          · simp [Ty.isRefLike] at hrl
            cases t <;> simp [Ty.isRefLike, Ty.ownerElem?] at hrl hownerElem
          · rw [hpath] at hownerElem
            simp [Ty.ownerElem?] at hownerElem
        cases ec with
        | pilot profile _ =>
          exact access hp (hlPlace.mono (hpilotSize profile)) hgamPlace.1
            (fun target ht => Or.inl (hE3.1 target (hinRead target ht)))
        | @shrink pc profile context =>
          have hMod : tenv.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
          have hVars : tenv.vars = penv.impl.vars :=
            haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
          have hEnv : pc.approvals.access = penv.access := by
            have hAccessMod := haccess.2.2.1
            have hAccessImpl := haccess.2.2.2.1
            have hAccessCtx := haccess.2.2.2.2
            cases hAccessValue : pc.approvals.access
            rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
            unfold PEnv.access
            congr 1
          have hplaceType : penv.access.placeType? owner = some t :=
            tyPlace_accessType hMod hVars hownerTy
          let transition := context.child rfl 1 (DemandNode.expression size) .expression
            hchildS (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
          have hOwnerRoots : ∃ roots, penv.access.placeRoots owner = .ok roots := by
            cases hroots : penv.access.placeRoots owner with
            | error err =>
              have hbad :
                  (DemandNode.statement (.resize owner size none o)).childFrame
                    penv.access path context.expected.frame 1 = .error err := by
                have hExpectation :
                    (DemandNode.statement (.resize owner size none o)).childExpectation?
                        penv.access
                        ⟨path, .expression, context.expected.frame.active,
                          context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                      some ⟨context.expected.frame.active, context.expected.frame.future⟩ := by
                  simp [DemandNode.childExpectation?, DemandNode.childFuture,
                    DemandNode.visibleForChild, DemandNode.child?, DemandNode.children]
                simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                  AccessEnv.aliasPlace, hplaceType, hownerElem, hroots,
                  Functor.map, Except.map]
              have htransition := transition.childFrameEq
              rw [hEnv] at htransition
              rw [hbad] at htransition
              cases htransition
            | ok roots => exact ⟨roots, rfl⟩
          obtain ⟨roots, hOwnerRoots⟩ := hOwnerRoots
          let ownerAlias : RetainedAlias :=
            ⟨.ref .mutable t, roots, .operand (path ++ [0])⟩
          have hAliasQuery : penv.access.aliasPlace (path ++ [0]) owner = .ok [ownerAlias] := by
            simp [AccessEnv.aliasPlace, hplaceType, hownerElem, hOwnerRoots, ownerAlias,
              Functor.map, Except.map]
          have hAliasQueryCtx : pc.approvals.access.aliasPlace (path ++ [0]) owner =
              .ok [ownerAlias] := by
            rw [hEnv]
            exact hAliasQuery
          have hnew : (DemandNode.statement (.resize owner size none o)).retainedForChild
              pc.approvals.access path 1 = .ok [ownerAlias] := by
            simp [DemandNode.retainedForChild, hAliasQueryCtx]
          have hAliasMem : ownerAlias ∈ sizeEc.retained := by
            have hChild := DemandNode.childFrame_newAlias
              (result := transition.childFrame) (aliases := [ownerAlias])
              (alias := ownerAlias) transition.childFrameEq hnew
              (List.mem_cons.mpr (Or.inl rfl))
            change ownerAlias ∈ transition.context.expected.frame.retained
            rw [transition.expectedFrameEq]
            exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
          have hrepresentable : t.refTarget = true ∨ t.isSlice = true :=
            Or.inl hownerRefTarget
          have hAliasSource : AliasAt m W env sPlace.store ownerAlias (.ref l) :=
            AliasAt.ofAliasPlace hAliasQuery hplaceType hownerRp hplace hgamPlace.1 hrepresentable
          have hAliasPost := (hretSize ownerAlias hAliasMem).typed (.ref l) hAliasSource
          have hLocOkPost : LocOk m W.G sSize.store l t := by
            rcases hAliasPost.1 with ⟨l', heq, hloc⟩
            cases heq
            rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
            · exact hloc
            · cases t <;> simp_all [Ty.isSlice, Ty.ownerElem?]
          exact access hp hLocOkPost hgamPlace.1
            (fun target ht => Or.inl (hE3.1 target (hinRead target ht)))
      have hinShrinkFinal : ∀ target, target ∈ rootsTargets ownerRoots → target ∈ rst'.eff.shrinks := by
        intro target htarget
        have hstate := (st_modify_ok _ _ _).1 haborts
        cases hstate
        exact hinShrink target htarget
      have hchanged := statementEffectMutationRoot hFSizeOut hgamPlace.1 (effect := rst'.eff) (by
        intro target htarget
        simp only [effectMutationTargets, List.mem_append]
        exact Or.inl (Or.inr (hinShrinkFinal target htarget)))
      have houtputS := statementResizeSizeOutputFuture ec
      refine Sat.bind (sat_lengthLoc_owner hownerLoc hownerElem
        (Q := fun len s' => s' = sSize ∧ s'.store.length l = .ok len)
        (fun len hlen => ⟨rfl, hlen⟩)) ?_
      rintro len sLength ⟨hstate, hlen⟩
      subst sLength
      by_cases hnegative : wrap .i64 sizeInt < 0
      · simp only [hnegative, if_pos, sat_abort]
      · simp only [hnegative, if_neg, if_false]
        by_cases hshrink : (wrap .i64 sizeInt).toNat < len
        · cases t with
          | limited ownerElement capacity =>
            simp only [hshrink, if_pos]
            have hownerElement : ownerElement = el := by
              simpa [Ty.ownerElem?] using hownerElem
            subst ownerElement
            let newLen := (wrap .i64 sizeInt).toNat
            obtain ⟨destination, htruncate, hstep, _⟩ :=
              statementLimitedTruncateFlatStep hownerLoc hlen (by simpa [newLen] using hshrink)
            have hmodify : sSize.store.modify l (Val.truncate newLen) = .ok destination := by
              simpa [Store.truncate] using htruncate
            have hrootsTruncate : PreservesRootTypes m W.G observation.roots
                sSize.store destination :=
              statementModifyPreservesRootTypes hstep.le hownerLoc hmodify
            obtain ⟨_, hvaluesTruncate, hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
              statementFlatStepPreservation (s := sSize)
                (s' := { sSize with store := destination }) (env := env)
                (aliases := ec.retained) hsafeSize hrootsTruncate hstep
            have hfootTruncate : Footprint (insts env) (Dset W) sSize
                { sSize with store := destination } := Footprint.of_flatStep hstep
            have hX := (hXPlace.trans hXSize).trans hfootTruncate
            have hretained : RetainsAliases m W env s.store
                ({ sSize with store := destination }).store ec.retained :=
              hretPlace.trans
                ((hretSize.subset (fun alias hmem =>
                  ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                    hchildS hphaseS hmem)).trans hretainedTruncate)
            have hrun :
                (do
                  truncateLoc l newLen
                  pure (Flow.normal Val.unit)) sSize =
                  .ok (Flow.normal Val.unit) { sSize with store := destination } := by
              have htruncate' : sSize.store.truncate l newLen = .ok destination := by
                simpa [newLen] using htruncate
              change (M.bind' (truncateLoc l newLen)
                (fun (_ : Unit) => M.pure' (Flow.normal Val.unit))) sSize = _
              simp only [M.bind', truncateLoc, htruncate', M.pure']
            unfold Sat
            rw [hrun]
            exact ⟨houtputS ▸ hFSizeOut.flatStep hstep, hX.toS,
              hrootsPlace.trans (hrootsSize.trans hrootsTruncate),
              hvaluesPlace.trans (hvaluesSize.trans hvaluesTruncate), hsafeTruncate,
              hretained,
              fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                (StoreLe.trans (hpilotSize hprofile) (hpilotTruncate hprofile)),
              TSame.refl _, hT.ext hX.dom hcur,
              hforbiddenPre.trans (statementStoreForbidden hFSizeOut hgamPlace.1 hdisjoint
                (truncate_except_owner sSize.store destination l newLen htruncate)),
              hmutationPre.trans (statementSingleRootMutation
                (truncate_except_owner sSize.store destination l newLen htruncate) hchanged),
              by simp [Stmt.diverges]⟩
          | grow element =>
            have hownerElement : element = el := by simpa [Ty.ownerElem?] using hownerElem
            subst el
            let newLen := (wrap .i64 sizeInt).toNat
            have hownerGS : LocTy sSize.store l (.growshrink element) :=
              hownerLoc.grow_to_growshrink
            obtain ⟨destination, htruncate⟩ := statementTruncateGrowshrinkTotal hownerGS
              ⟨len, hlen, Nat.le_of_lt hshrink⟩
            have htruncate' : sSize.store.truncate l newLen = .ok destination := by
              simpa [newLen] using htruncate
            have hrun :
                (do
                  truncateLoc l newLen
                  pure (Flow.normal Val.unit)) sSize =
                  .ok (Flow.normal Val.unit) { sSize with store := destination } := by
              change (M.bind' (truncateLoc l newLen)
                (fun (_ : Unit) => M.pure' (Flow.normal Val.unit))) sSize = _
              simp only [M.bind', truncateLoc, htruncate', M.pure']
            have hmutationPhase : DemandNodeHasPhase
                (DemandNode.statement (.resize owner size none o)) .mutation := by
              simp [DemandNodeHasPhase, DemandNode.phaseMatches]
            have haccessMutation :=
              (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
            have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
            have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
            change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv
              at haccessMutation
            change (statementMutationContext ec hmutationPhase).ActiveMatches tenv
              at hactiveMutation
            change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture
              at houtputMutation
            have hretainedMutation : ∀ alias, alias ∈ ec.retained →
                alias ∈ (statementMutationContext ec hmutationPhase).retained := by
              intro alias hmem
              exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
            cases hmutation : statementMutationContext ec hmutationPhase with
            | pilot profile _ =>
              simp [requireShrink, rej, hF.mod_t, profile] at hrequire
              change Except.error _ = Except.ok _ at hrequire
              cases hrequire
            | @shrink pc profile mutationContext =>
              have hdirect :
                  (DemandNode.statement (.resize owner size none o)).directShrinkPlace? =
                    some owner := by simp [DemandNode.directShrinkPlace?]
              obtain ⟨_, hownerResult, _⟩ :=
                mutationContext.sourceAt.directShrinkOwner_result rfl hdirect
                  pc.approvals.accessMatches
              obtain ⟨approval, _, hsameOwner, _, hframe⟩ :=
                mutationContext.directShrinkApproval hdirect hownerResult
              rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
              have hownerP : Gam env W.ownerP ownerRoots l.root :=
                hgamPlace.2.1 ⟨element, Or.inl rfl⟩
              have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hownerP
              have hownerBroadFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hgamPlace.1
              have hclassifiedPost := hF.classifiedParameters_advance
                (hclassified profile) (hXPlace.trans hXSize)
              have hheader : l.path = [] :=
                PlaceOk.ownerHeader hplace (by simpa [Ty.ownerElem?] using hownerElem)
              have authority := statementDirectShrinkAuthority mutationContext profile hdirect
                hownerResult hownerFacts.2.1 (Or.inl rfl) hownerFacts.2.2 hownerP
                hFSizeOut hp hclassifiedPost hsafeSize.typed hheader hownerLoc
                (fun target htarget => hE4.2.2.2.1 target (hinShrink target htarget))
              have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
                W.ownerP observation l.root
              change (statementMutationContext ec hmutationPhase).mayShrink
                W.ownerP observation l.root ↔ ec.mayShrink W.ownerP observation l.root at hmay
              rw [hmutation] at hmay
              have hshrinkAuthority :
                  (ec.mayShrink W.ownerP observation l.root ∨
                    ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
                    (∀ g, l.root = .global g → g < W.G) :=
                ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
              have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
                intro x hx
                exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
              have hfutureNeeded : ∀ x, x ∈ sizeEc.outputFuture →
                  x ∈ approval.point.future := by
                intro x hx
                apply (hframe.2.1 x).2
                change x ∈ mutationContext.expected.frame.future
                change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
                rw [houtputMutation]
                rw [← houtputS]
                exact hx
              have happrovalAccess : approval.access = pc.approvals.access :=
                Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
              have haccessEq : approval.access = penv.access :=
                happrovalAccess.trans hownerFacts.1
              have happrovalTy : approval.shrinkOwner.ty = some (.grow element) := by
                rw [hsameOwner]
                exact hownerFacts.2.1
              have happrovalRoot : Gam env W.P approval.shrinkOwner.roots l.root := by
                rw [hsameOwner]
                exact hownerBroadFacts.2.2
              have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
                  alias ∈ approval.point.retained := by
                intro alias hmem
                exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
              have hflat : element.flat = true :=
                statementOwnerElementFlat hplace hownerElem
              obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate,
                hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
                statementResizableTruncatePreservation hFSizeOut haccessEq happrovalTy
                  (Or.inl rfl) happrovalRoot hownerLoc hvisibleActive hfutureNeeded profile
                  hprotected hsafeSize hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
                  hretainedNeeded htruncate
              have hX := (hXPlace.trans hXSize).trans hfoot
              have hretained : RetainsAliases m W env s.store
                  ({ sSize with store := destination }).store ec.retained :=
                hretPlace.trans
                  ((hretSize.subset (fun alias hmem =>
                    ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                      hchildS hphaseS hmem)).trans hretainedTruncate)
              unfold Sat
              simp only [hshrink, if_pos]
              rw [hrun]
              exact ⟨houtputS ▸ hpostFrame, hX.toS,
                hrootsPlace.trans (hrootsSize.trans hrootsTruncate),
                hvaluesPlace.trans (hvaluesSize.trans hvaluesTruncate), hsafeTruncate,
                hretained,
                fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                  (StoreLe.trans (hpilotSize hprofile) (hpilotTruncate hprofile)),
                TSame.refl _, hT.ext hX.dom hcur,
                hforbiddenPre.trans (statementStoreForbidden hFSizeOut hgamPlace.1 hdisjoint
                  (truncate_except_owner sSize.store destination l newLen htruncate)),
                hmutationPre.trans (statementSingleRootMutation
                  (truncate_except_owner sSize.store destination l newLen htruncate) hchanged),
                by simp [Stmt.diverges]⟩
          | growshrink element =>
            have hownerElement : element = el := by simpa [Ty.ownerElem?] using hownerElem
            subst el
            let newLen := (wrap .i64 sizeInt).toNat
            have hownerGS : LocTy sSize.store l (.growshrink element) :=
              hownerLoc
            obtain ⟨destination, htruncate⟩ := statementTruncateGrowshrinkTotal hownerGS
              ⟨len, hlen, Nat.le_of_lt hshrink⟩
            have htruncate' : sSize.store.truncate l newLen = .ok destination := by
              simpa [newLen] using htruncate
            have hrun :
                (do
                  truncateLoc l newLen
                  pure (Flow.normal Val.unit)) sSize =
                  .ok (Flow.normal Val.unit) { sSize with store := destination } := by
              change (M.bind' (truncateLoc l newLen)
                (fun (_ : Unit) => M.pure' (Flow.normal Val.unit))) sSize = _
              simp only [M.bind', truncateLoc, htruncate', M.pure']
            have hmutationPhase : DemandNodeHasPhase
                (DemandNode.statement (.resize owner size none o)) .mutation := by
              simp [DemandNodeHasPhase, DemandNode.phaseMatches]
            have haccessMutation :=
              (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
            have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
            have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
            change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv
              at haccessMutation
            change (statementMutationContext ec hmutationPhase).ActiveMatches tenv
              at hactiveMutation
            change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture
              at houtputMutation
            have hretainedMutation : ∀ alias, alias ∈ ec.retained →
                alias ∈ (statementMutationContext ec hmutationPhase).retained := by
              intro alias hmem
              exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
            cases hmutation : statementMutationContext ec hmutationPhase with
            | pilot profile _ =>
              simp [requireShrink, rej, hF.mod_t, profile] at hrequire
              change Except.error _ = Except.ok _ at hrequire
              cases hrequire
            | @shrink pc profile mutationContext =>
              have hdirect :
                  (DemandNode.statement (.resize owner size none o)).directShrinkPlace? =
                    some owner := by simp [DemandNode.directShrinkPlace?]
              obtain ⟨_, hownerResult, _⟩ :=
                mutationContext.sourceAt.directShrinkOwner_result rfl hdirect
                  pc.approvals.accessMatches
              obtain ⟨approval, _, hsameOwner, _, hframe⟩ :=
                mutationContext.directShrinkApproval hdirect hownerResult
              rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
              have hownerP : Gam env W.ownerP ownerRoots l.root :=
                hgamPlace.2.1 ⟨element, Or.inr rfl⟩
              have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hownerP
              have hownerBroadFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hgamPlace.1
              have hclassifiedPost := hF.classifiedParameters_advance
                (hclassified profile) (hXPlace.trans hXSize)
              have hheader : l.path = [] :=
                PlaceOk.ownerHeader hplace (by simpa [Ty.ownerElem?] using hownerElem)
              have authority := statementDirectShrinkAuthority mutationContext profile hdirect
                hownerResult hownerFacts.2.1 (Or.inr rfl) hownerFacts.2.2 hownerP
                hFSizeOut hp hclassifiedPost hsafeSize.typed hheader hownerLoc
                (fun target htarget => hE4.2.2.2.1 target (hinShrink target htarget))
              have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
                W.ownerP observation l.root
              change (statementMutationContext ec hmutationPhase).mayShrink
                W.ownerP observation l.root ↔ ec.mayShrink W.ownerP observation l.root at hmay
              rw [hmutation] at hmay
              have hshrinkAuthority :
                  (ec.mayShrink W.ownerP observation l.root ∨
                    ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
                    (∀ g, l.root = .global g → g < W.G) :=
                ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
              have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
                intro x hx
                exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
              have hfutureNeeded : ∀ x, x ∈ sizeEc.outputFuture →
                  x ∈ approval.point.future := by
                intro x hx
                apply (hframe.2.1 x).2
                change x ∈ mutationContext.expected.frame.future
                change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
                rw [houtputMutation]
                rw [← houtputS]
                exact hx
              have happrovalAccess : approval.access = pc.approvals.access :=
                Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
              have haccessEq : approval.access = penv.access :=
                happrovalAccess.trans hownerFacts.1
              have happrovalTy : approval.shrinkOwner.ty = some (.growshrink element) := by
                rw [hsameOwner]
                exact hownerFacts.2.1
              have happrovalRoot : Gam env W.P approval.shrinkOwner.roots l.root := by
                rw [hsameOwner]
                exact hownerBroadFacts.2.2
              have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
                  alias ∈ approval.point.retained := by
                intro alias hmem
                exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
              have hheader : l.path = [] :=
                PlaceOk.ownerHeader hplace (by simpa [Ty.ownerElem?] using hownerElem)
              have hflat : element.flat = true :=
                statementOwnerElementFlat hplace hownerElem
              obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate,
                hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
                statementResizableTruncatePreservation hFSizeOut haccessEq happrovalTy
                  (Or.inr rfl) happrovalRoot hownerLoc hvisibleActive hfutureNeeded profile
                  hprotected hsafeSize hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
                  hretainedNeeded htruncate
              have hX := (hXPlace.trans hXSize).trans hfoot
              have hretained : RetainsAliases m W env s.store
                  ({ sSize with store := destination }).store ec.retained :=
                hretPlace.trans
                  ((hretSize.subset (fun alias hmem =>
                    ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                      hchildS hphaseS hmem)).trans hretainedTruncate)
              unfold Sat
              simp only [hshrink, if_pos]
              rw [hrun]
              exact ⟨houtputS ▸ hpostFrame, hX.toS,
                hrootsPlace.trans (hrootsSize.trans hrootsTruncate),
                hvaluesPlace.trans (hvaluesSize.trans hvaluesTruncate), hsafeTruncate,
                hretained,
                fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                  (StoreLe.trans (hpilotSize hprofile) (hpilotTruncate hprofile)),
                TSame.refl _, hT.ext hX.dom hcur,
                hforbiddenPre.trans (statementStoreForbidden hFSizeOut hgamPlace.1 hdisjoint
                  (truncate_except_owner sSize.store destination l newLen htruncate)),
                hmutationPre.trans (statementSingleRootMutation
                  (truncate_except_owner sSize.store destination l newLen htruncate) hchanged),
                by simp [Stmt.diverges]⟩
          | int _ | bool | unit | arr _ _ | ref _ _ | slice _ _ | tuple _ | structT _ _ =>
            simp [Ty.ownerElem?] at hownerElem
        · simp only [hshrink, if_false]
          by_cases hequal : ((wrap .i64 sizeInt).toNat == len) = true
          · simp only [hequal, if_pos, sat_pure]
            have hretained : RetainsAliases m W env s.store sSize.store ec.retained :=
              hretPlace.trans (hretSize.subset (fun alias hmem =>
                ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                  hchildS hphaseS hmem))
            exact ⟨houtputS ▸ hFSizeOut, (hXPlace.trans hXSize).toS,
              hrootsPlace.trans hrootsSize, hvaluesPlace.trans hvaluesSize, hsafeSize,
              hretained,
              fun hprofile => StoreLe.trans (hpilotPlace hprofile) (hpilotSize hprofile),
              TSame.refl _, hT.ext (hXPlace.trans hXSize).dom hcur, hforbiddenPre,
              hmutationPre, by simp [Stmt.diverges]⟩
          · have hnotEqual : ((wrap .i64 sizeInt).toNat == len) = false := by
              cases hbool : ((wrap .i64 sizeInt).toNat == len) <;> simp_all
            simp only [hnotEqual, Bool.false_eq_true, if_false, sat_abort]
    | some e =>
      rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨fillTy, s6, hfillTy, hrestTy⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨fillRoots, r3, hfillRp, hrestRp⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r4, hwrites, hrestRp⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r5, hgrows, hrestRp⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r6, hreads, hrestRp⟩
      rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r7, hshrinks, hrestRp⟩
      have haborts : noteAborts r7 = Except.ok ((), rst') := hrestRp
      have hfillEq : fillTy = el := by
        by_cases heq : fillTy = el
        · exact heq
        · have hbeq : (fillTy == el) = false := by
            cases hbeq : (fillTy == el) with
            | false => rfl
            | true => exact False.elim (heq (beq_iff_eq.mp hbeq))
          have hreject : False := by
            have hbind := (st_bind_ok _ _ _ _).1 (by simpa [hbeq] using hrestTy)
            obtain ⟨_, _, hthrow, _⟩ := hbind
            exact (st_throw_ok _ _ _).1 hthrow
          exact hreject.elim
      subst fillTy
      simp at hrestTy
      change (requireWrite "resize" cw >>= fun _ => pure tenv) s6 =
        Except.ok (tenv', tn') at hrestTy
      rcases (st_bind_ok _ _ _ _).1 hrestTy with ⟨_, s7, hwrite, hrestTy⟩
      simp [requireWrite] at hwrite hrestTy
      rcases hrestTy with ⟨rfl, rfl⟩
      have hE8 := (PMono.noteAborts _ _ _ haborts).2.trans hE
      have hE7 := (PMono.addShrinks ownerRoots _ _ _ hshrinks).2.trans hE8
      have hE6 := (PMono.addReads ownerRoots _ _ _ hreads).2.trans hE7
      have hE5 := (PMono.addGrows ownerRoots _ _ _ hgrows).2.trans hE6
      have hE4 := (PMono.addWrites ownerRoots _ _ _ hwrites).2.trans hE5
      have hE3 := (rpExpr_mono hfillRp).2.trans hE4
      have hE2 := (rpExpr_mono hsizeRp).2.trans hE3
      have hnoteAborts : PMonoRebinds noteAborts := by
        unfold noteAborts
        exact PMonoRebinds.modify _ (fun _ _ h => h)
      have hfinal8R := hnoteAborts r7 () rst' haborts
      have hfinal7R := (PMonoRebinds.addShrinks ownerRoots r6 () r7 hshrinks).trans hfinal8R
      have hfinal6R := (PMonoRebinds.addReads ownerRoots r5 () r6 hreads).trans hfinal7R
      have hfinal5R := (PMonoRebinds.addGrows ownerRoots r4 () r5 hgrows).trans hfinal6R
      have hfinal4R := (PMonoRebinds.addWrites ownerRoots r3 () r4 hwrites).trans hfinal5R
      have hfinal8E := (PMono.noteAborts r7 () rst' haborts).2
      have hfinal7E := (PMono.addShrinks ownerRoots r6 () r7 hshrinks).2.trans hfinal8E
      have hfinal6E := (PMono.addReads ownerRoots r5 () r6 hreads).2.trans hfinal7E
      have hfinal5E := (PMono.addGrows ownerRoots r4 () r5 hgrows).2.trans hfinal6E
      have hfinal4E := (PMono.addWrites ownerRoots r3 () r4 hwrites).2.trans hfinal5E
      simp only [execStmt]
      have hchildP : (DemandNode.statement (.resize owner size (some e) o)).child? 0 =
          some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
      have hvisibleP : ∀ x, x ∈ tenv.visible ↔
          x ∈ (DemandNode.statement (.resize owner size (some e) o)).visibleForChild tenv.visible 0 := by
        simp [DemandNode.visibleForChild]
      have hresultP := statementPlaceChildSpec ih ec observation W tenv penv env s 0 owner hchildP
        hactive haccess hprotected hobserved hclassified hp hF hvisibleP
        (statementResizePlaceInputSubset ec) s2 n1 t bw cw rst r1 ownerRoots hownerTy hownerRp hE2
      refine Sat.bind hresultP ?_
      rintro l sPlace ⟨hFPlace, hXPlace, hrootsPlace, hvaluesPlace, hsafePlace,
        hretPlace, hpilotPlace, hplace, hgamPlace⟩
      have hdisjoint := statementPlaceForbiddenDisjoint ec haccess hchildP hownerRp
      have hchildS : (DemandNode.statement (.resize owner size (some e) o)).child? 1 =
          some (DemandNode.expression size) := by simp [DemandNode.child?, DemandNode.children]
      have hphaseS : DemandNodeHasPhase (DemandNode.expression size) .expression := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      have hvisibleS : ∀ x, x ∈ tenv.visible ↔
          x ∈ (DemandNode.statement (.resize owner size (some e) o)).visibleForChild tenv.visible 1 := by
        simp [DemandNode.visibleForChild]
      let sizeEc := statementExprChildContext ec 1 size hchildS
      have hFSize := statementResizeSizeInputFrame ec hactive hFPlace
      have hclassifiedPlace : m.profile = .shrink →
          ClassifiedParameters m W.P W.D observation sPlace.store := by
        intro hprofile
        exact hF.classifiedParameters_advance (hclassified hprofile) hXPlace
      have hresultSize := statementExprChildSpecAtFrame ih ec observation W tenv tenv penv env sPlace
        1 size hchildS hactive haccess hprotected hsafePlace hclassifiedPlace hp sizeEc rfl hFSize
        hvisibleS sizeEc.retained (fun _ hmem => hmem) s3 s4 sizeTy r1 r2 sizeRoots
        hsizeTy hsizeRp hE3
      refine Sat.bind hresultSize ?_
      rintro sizeValue sSize ⟨hFSizeOut, hXSize, hrootsSize, hvaluesSize, hsafeSize,
        hretSize, hpilotSize, hsizeValueTy, hsizeGam⟩
      have hsizeIntFacts := (requireInt_ok "resize size" sizeTy s4 (sizeWidth, s5)).1 hsizeInt
      rw [hsizeIntFacts.1] at hsizeValueTy
      obtain ⟨sizeInt, rfl⟩ := hasTy_int hsizeValueTy
      simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
      have hchildF : (DemandNode.statement (.resize owner size (some e) o)).child? 2 =
          some (DemandNode.expression e) := by simp [DemandNode.child?, DemandNode.children]
      have hphaseF : DemandNodeHasPhase (DemandNode.expression e) .expression := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      have hvisibleF : ∀ x, x ∈ tenv.visible ↔
          x ∈ (DemandNode.statement (.resize owner size (some e) o)).visibleForChild tenv.visible 2 := by
        simp [DemandNode.visibleForChild]
      let fillEc := statementExprChildContext ec 2 e hchildF
      have hFfill := statementResizeFillInputFrame ec hactive hFSizeOut
      have hclassifiedSize : m.profile = .shrink →
          ClassifiedParameters m W.P W.D observation sSize.store := by
        intro hprofile
        exact hF.classifiedParameters_advance (hclassified hprofile)
          (hXPlace.trans hXSize)
      have hresultFill := statementExprChildSpecAtFrame ih ec observation W tenv tenv penv env sSize
        2 e hchildF hactive haccess hprotected hsafeSize hclassifiedSize hp fillEc rfl hFfill
        hvisibleF fillEc.retained (fun _ hmem => hmem) s5 s6 el r2 r3 fillRoots
        hfillTy hfillRp hE4
      refine Sat.bind hresultFill ?_
      rintro fillValue sFill ⟨hFFillOut, hXFill, hrootsFill, hvaluesFill, hsafeFill,
        hretFill, hpilotFill, hfillValueTy, hfillGam⟩
      simp only [sat_pure_bind]
      have hforbiddenPre := hgamPlace.2.2.1.trans
        (hsizeGam.2.2.1.trans hfillGam.2.2.1)
      have hmutationPre :=
        (((hgamPlace.2.2.2.weaken (effectMutationRoots.mono m penv.impl
          (rpExpr_mono hsizeRp).2 (rpExpr_rebinds_mono hsizeRp))).trans hsizeGam.2.2.2.2).weaken
          (effectMutationRoots.mono m penv.impl (rpExpr_mono hfillRp).2
            (rpExpr_rebinds_mono hfillRp))).trans hfillGam.2.2.2.2 |>.weaken
          (effectMutationRoots.mono m penv.impl hfinal4E hfinal4R)
      have hownerElem : t.ownerElem? = some el :=
        (ownerElement_ok _ _ _ _ _ hownerElement).2.1
      have hownerRefTarget : t.refTarget = true := by
        rcases hplace with ⟨hrt, _, _⟩ |
          ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, hpath, _⟩
        · exact hrt
        · simp [Ty.isRefLike] at hrl
          cases t <;> simp [Ty.isRefLike, Ty.ownerElem?] at hrl hownerElem
        · rw [hpath] at hownerElem
          simp [Ty.ownerElem?] at hownerElem
      obtain ⟨_, hinRead⟩ := addReads_ok _ _ _ hreads
      obtain ⟨_, hinShrink⟩ := statementAddShrinksOk ownerRoots r6 ((), r7) hshrinks
      have hownerLoc : LocTy sFill.store l t := by
        have hlPlace : LocOk m W.G sPlace.store l t := by
          rcases hplace with ⟨_, hl, _⟩ |
            ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, hpath, _⟩
          · exact hl
          · simp [Ty.isRefLike] at hrl
            cases t <;> simp [Ty.isRefLike, Ty.ownerElem?] at hrl hownerElem
          · rw [hpath] at hownerElem
            simp [Ty.ownerElem?] at hownerElem
        cases ec with
        | pilot profile _ =>
          exact access hp
            (hlPlace.mono (StoreLe.trans (hpilotSize profile) (hpilotFill profile)))
            hgamPlace.1 (fun target ht => Or.inl (hE7.1 target (hinRead target ht)))
        | @shrink pc profile context =>
          have hMod : tenv.mod = penv.mod := haccess.1.symm.trans haccess.2.2.1
          have hVars : tenv.vars = penv.impl.vars :=
            haccess.2.1.symm.trans (congrArg Impl.vars haccess.2.2.2.1)
          have hEnv : pc.approvals.access = penv.access := by
            have hAccessMod := haccess.2.2.1
            have hAccessImpl := haccess.2.2.2.1
            have hAccessCtx := haccess.2.2.2.2
            cases hAccessValue : pc.approvals.access
            rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
            unfold PEnv.access
            congr 1
          have hplaceType : penv.access.placeType? owner = some t :=
            tyPlace_accessType hMod hVars hownerTy
          have hOwnerRoots : ∃ roots, penv.access.placeRoots owner = .ok roots := by
            cases hroots : penv.access.placeRoots owner with
            | error err =>
              have hbad : (DemandNode.statement (.resize owner size (some e) o)).childFrame
                  penv.access path context.expected.frame 1 = .error err := by
                have hExpectation :
                    (DemandNode.statement (.resize owner size (some e) o)).childExpectation?
                      penv.access
                      ⟨path, .expression, context.expected.frame.active,
                        context.expected.frame.future, context.expected.frame.retained⟩ 1 = some ⟨
                          (DemandNode.statement (.resize owner size (some e) o)).visibleForChild
                            context.expected.frame.active 1,
                          e.variables ++ context.expected.frame.future⟩ := by
                  simp [DemandNode.childExpectation?, DemandNode.childFuture,
                    DemandNode.child?, DemandNode.children, DemandNode.visibleForChild]
                simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                  AccessEnv.aliasPlace, hplaceType, hownerElem, hroots,
                  Functor.map, Except.map]
              have htransition :=
                (context.child rfl 1 (DemandNode.expression size) .expression hchildS
                  (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).childFrameEq
              rw [hEnv] at htransition
              rw [hbad] at htransition
              cases htransition
            | ok roots => exact ⟨roots, rfl⟩
          obtain ⟨roots, hOwnerRoots⟩ := hOwnerRoots
          let ownerAlias : RetainedAlias :=
            ⟨.ref .mutable t, roots, .operand (path ++ [0])⟩
          have hAliasQuery : penv.access.aliasPlace (path ++ [0]) owner = .ok [ownerAlias] := by
            simp [AccessEnv.aliasPlace, hplaceType, hownerElem, hOwnerRoots, ownerAlias,
              Functor.map, Except.map]
          have hAliasQueryCtx : pc.approvals.access.aliasPlace (path ++ [0]) owner =
              .ok [ownerAlias] := by rw [hEnv]; exact hAliasQuery
          let transitionS := context.child rfl 1 (DemandNode.expression size) .expression hchildS
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
          have hnewS : (DemandNode.statement (.resize owner size (some e) o)).retainedForChild
              pc.approvals.access path 1 = .ok [ownerAlias] := by
            simp [DemandNode.retainedForChild, hAliasQueryCtx]
          have hAliasMemSize : ownerAlias ∈ sizeEc.retained := by
            have hChild := DemandNode.childFrame_newAlias
              (result := transitionS.childFrame) (aliases := [ownerAlias]) (alias := ownerAlias)
              transitionS.childFrameEq hnewS (List.mem_cons.mpr (Or.inl rfl))
            change ownerAlias ∈ transitionS.context.expected.frame.retained
            rw [transitionS.expectedFrameEq]
            exact DemandNode.phaseFrame_retains transitionS.phaseFrameEq hChild
          let transitionF := context.child rfl 2 (DemandNode.expression e) .expression hchildF
            (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
          have hnewF : (DemandNode.statement (.resize owner size (some e) o)).retainedForChild
              pc.approvals.access path 2 = .ok [ownerAlias] := by
            simp [DemandNode.retainedForChild, hAliasQueryCtx]
          have hAliasMemFill : ownerAlias ∈ fillEc.retained := by
            have hChild := DemandNode.childFrame_newAlias
              (result := transitionF.childFrame) (aliases := [ownerAlias]) (alias := ownerAlias)
              transitionF.childFrameEq hnewF (List.mem_cons.mpr (Or.inl rfl))
            change ownerAlias ∈ transitionF.context.expected.frame.retained
            rw [transitionF.expectedFrameEq]
            exact DemandNode.phaseFrame_retains transitionF.phaseFrameEq hChild
          have hrepresentable : t.refTarget = true ∨ t.isSlice = true :=
            Or.inl hownerRefTarget
          have hAliasSource : AliasAt m W env sPlace.store ownerAlias (.ref l) :=
            AliasAt.ofAliasPlace hAliasQuery hplaceType hownerRp hplace hgamPlace.1 hrepresentable
          have hAliasPostSize := (hretSize ownerAlias hAliasMemSize).typed (.ref l) hAliasSource
          have hAliasPostFill := (hretFill ownerAlias hAliasMemFill).typed (.ref l) hAliasPostSize
          have hLocOkPost : LocOk m W.G sFill.store l t := by
            rcases hAliasPostFill.1 with ⟨l', heq, hloc⟩
            cases heq
            rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
            · exact hloc
            · cases t <;> simp_all [Ty.isSlice, Ty.ownerElem?]
          exact access hp hLocOkPost hgamPlace.1
            (fun target ht => Or.inl (hE7.1 target (hinRead target ht)))
      have hinShrinkFinal : ∀ target, target ∈ rootsTargets ownerRoots → target ∈ rst'.eff.shrinks := by
        intro target htarget
        have hstate := (st_modify_ok _ _ _).1 haborts
        cases hstate
        exact hinShrink target htarget
      have hchanged := statementEffectMutationRoot hFFillOut hgamPlace.1 (effect := rst'.eff) (by
        intro target htarget
        simp only [effectMutationTargets, List.mem_append]
        exact Or.inl (Or.inr (hinShrinkFinal target htarget)))
      have houtputF := statementResizeFillOutputFuture ec
      refine Sat.bind (sat_lengthLoc_owner hownerLoc hownerElem
        (Q := fun len s' => s' = sFill ∧ s'.store.length l = .ok len)
        (fun len hlen => ⟨rfl, hlen⟩)) ?_
      rintro len sLength ⟨hstate, hlen⟩
      subst sLength
      by_cases hnegative : wrap .i64 sizeInt < 0
      · simp only [hnegative, if_pos, sat_abort]
      · simp only [hnegative, if_neg, if_false]
        by_cases hshrink : (wrap .i64 sizeInt).toNat < len
        · simp only [hshrink, if_pos]
          cases t with
          | limited ownerElement capacity =>
            have hownerElement : ownerElement = el := by
              simpa [Ty.ownerElem?] using hownerElem
            subst ownerElement
            let newLen := (wrap .i64 sizeInt).toNat
            obtain ⟨destination, htruncate, hstep, _⟩ :=
              statementLimitedTruncateFlatStep hownerLoc hlen (by simpa [newLen] using hshrink)
            have hmodify : sFill.store.modify l (Val.truncate newLen) = .ok destination := by
              simpa [Store.truncate] using htruncate
            have hrootsTruncate : PreservesRootTypes m W.G observation.roots
                sFill.store destination :=
              statementModifyPreservesRootTypes hstep.le hownerLoc hmodify
            obtain ⟨_, hvaluesTruncate, hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
              statementFlatStepPreservation (s := sFill)
                (s' := { sFill with store := destination }) (env := env)
                (aliases := fillEc.retained) hsafeFill hrootsTruncate hstep
            have hfootTruncate : Footprint (insts env) (Dset W) sFill
                { sFill with store := destination } := Footprint.of_flatStep hstep
            have hrun :
                (do
                  truncateLoc l newLen
                  pure (Flow.normal Val.unit)) sFill =
                  .ok (Flow.normal Val.unit) { sFill with store := destination } := by
              have htruncate' : sFill.store.truncate l newLen = .ok destination := by
                simpa [newLen] using htruncate
              change (M.bind' (truncateLoc l newLen)
                (fun (_ : Unit) => M.pure' (Flow.normal Val.unit))) sFill = _
              simp only [M.bind', truncateLoc, htruncate', M.pure']
            have hX := ((hXPlace.trans hXSize).trans hXFill).trans hfootTruncate
            have hretained : RetainsAliases m W env s.store
                ({ sFill with store := destination }).store ec.retained :=
              hretPlace.trans
                ((hretSize.subset (fun alias hmem =>
                  ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                    hchildS hphaseS hmem)).trans
                  ((hretFill.trans hretainedTruncate).subset (fun alias hmem =>
                    ec.child_retained_subset rfl 2 (DemandNode.expression e) .expression
                      hchildF hphaseF hmem)))
            unfold Sat
            rw [hrun]
            exact ⟨houtputF ▸ hFFillOut.flatStep hstep, hX.toS,
              (hrootsPlace.trans hrootsSize).trans (hrootsFill.trans hrootsTruncate),
              (hvaluesPlace.trans hvaluesSize).trans (hvaluesFill.trans hvaluesTruncate),
              hsafeTruncate, hretained,
              fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                (StoreLe.trans (hpilotSize hprofile)
                  (StoreLe.trans (hpilotFill hprofile) (hpilotTruncate hprofile))),
              TSame.refl _, hT.ext hX.dom hcur,
              hforbiddenPre.trans (statementStoreForbidden hFFillOut hgamPlace.1 hdisjoint
                (truncate_except_owner sFill.store destination l newLen htruncate)),
              hmutationPre.trans (statementSingleRootMutation
                (truncate_except_owner sFill.store destination l newLen htruncate) hchanged),
              by simp [Stmt.diverges]⟩
          | grow element =>
            have hownerElement : element = el := by simpa [Ty.ownerElem?] using hownerElem
            subst el
            let newLen := (wrap .i64 sizeInt).toNat
            have hownerGS : LocTy sFill.store l (.growshrink element) :=
              hownerLoc.grow_to_growshrink
            obtain ⟨destination, htruncate⟩ := statementTruncateGrowshrinkTotal hownerGS
              ⟨len, hlen, Nat.le_of_lt hshrink⟩
            have htruncate' : sFill.store.truncate l newLen = .ok destination := by
              simpa [newLen] using htruncate
            have hrun :
                (do
                  truncateLoc l newLen
                  pure (Flow.normal Val.unit)) sFill =
                  .ok (Flow.normal Val.unit) { sFill with store := destination } := by
              change (M.bind' (truncateLoc l newLen)
                (fun (_ : Unit) => M.pure' (Flow.normal Val.unit))) sFill = _
              simp only [M.bind', truncateLoc, htruncate', M.pure']
            have hmutationPhase : DemandNodeHasPhase
                (DemandNode.statement (.resize owner size (some e) o)) .mutation := by
              simp [DemandNodeHasPhase, DemandNode.phaseMatches]
            have haccessMutation :=
              (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
            have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
            have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
            change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv
              at haccessMutation
            change (statementMutationContext ec hmutationPhase).ActiveMatches tenv
              at hactiveMutation
            change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture
              at houtputMutation
            have hretainedMutation : ∀ alias, alias ∈ ec.retained →
                alias ∈ (statementMutationContext ec hmutationPhase).retained := by
              intro alias hmem
              exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
            cases hmutation : statementMutationContext ec hmutationPhase with
            | pilot profile _ =>
              simp [requireShrink, rej, hF.mod_t, profile] at hrequire
              change Except.error _ = Except.ok _ at hrequire
              cases hrequire
            | @shrink pc profile mutationContext =>
              have hdirect :
                  (DemandNode.statement (.resize owner size (some e) o)).directShrinkPlace? =
                    some owner := by simp [DemandNode.directShrinkPlace?]
              obtain ⟨_, hownerResult, _⟩ :=
                mutationContext.sourceAt.directShrinkOwner_result rfl hdirect
                  pc.approvals.accessMatches
              obtain ⟨approval, _, hsameOwner, _, hframe⟩ :=
                mutationContext.directShrinkApproval hdirect hownerResult
              rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
              have hownerP : Gam env W.ownerP ownerRoots l.root :=
                hgamPlace.2.1 ⟨element, Or.inl rfl⟩
              have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hownerP
              have hownerBroadFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hgamPlace.1
              have hclassifiedPost := hF.classifiedParameters_advance
                (hclassified profile) ((hXPlace.trans hXSize).trans hXFill)
              have hheader : l.path = [] :=
                PlaceOk.ownerHeader hplace (by simpa [Ty.ownerElem?] using hownerElem)
              have authority := statementDirectShrinkAuthority mutationContext profile hdirect
                hownerResult hownerFacts.2.1 (Or.inl rfl) hownerFacts.2.2 hownerP
                hFFillOut hp hclassifiedPost hsafeFill.typed hheader hownerLoc
                (fun target htarget => hE8.2.2.2.1 target (hinShrink target htarget))
              have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
                W.ownerP observation l.root
              change (statementMutationContext ec hmutationPhase).mayShrink
                W.ownerP observation l.root ↔ ec.mayShrink W.ownerP observation l.root at hmay
              rw [hmutation] at hmay
              have hshrinkAuthority :
                  (ec.mayShrink W.ownerP observation l.root ∨
                    ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
                    (∀ g, l.root = .global g → g < W.G) :=
                ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
              have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
                intro x hx
                exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
              have hfutureNeeded : ∀ x, x ∈ fillEc.outputFuture →
                  x ∈ approval.point.future := by
                intro x hx
                apply (hframe.2.1 x).2
                change x ∈ mutationContext.expected.frame.future
                change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
                rw [houtputMutation]
                rw [← houtputF]
                exact hx
              have happrovalAccess : approval.access = pc.approvals.access :=
                Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
              have haccessEq : approval.access = penv.access :=
                happrovalAccess.trans hownerFacts.1
              have happrovalTy : approval.shrinkOwner.ty = some (.grow element) := by
                rw [hsameOwner]
                exact hownerFacts.2.1
              have happrovalRoot : Gam env W.P approval.shrinkOwner.roots l.root := by
                rw [hsameOwner]
                exact hownerBroadFacts.2.2
              have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
                  alias ∈ approval.point.retained := by
                intro alias hmem
                exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
              have hflat : element.flat = true :=
                statementOwnerElementFlat hplace hownerElem
              obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate,
                hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
                statementResizableTruncatePreservation hFFillOut haccessEq happrovalTy
                  (Or.inl rfl) happrovalRoot hownerLoc hvisibleActive hfutureNeeded profile
                  hprotected hsafeFill hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
                  hretainedNeeded htruncate
              have hX := ((hXPlace.trans hXSize).trans hXFill).trans hfoot
              have hretained : RetainsAliases m W env s.store
                  ({ sFill with store := destination }).store ec.retained :=
                hretPlace.trans
                  ((hretSize.subset (fun alias hmem =>
                    ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                      hchildS hphaseS hmem)).trans
                    ((hretFill.subset (fun alias hmem =>
                      ec.child_retained_subset rfl 2 (DemandNode.expression e) .expression
                        hchildF hphaseF hmem)).trans hretainedTruncate))
              unfold Sat
              rw [hrun]
              exact ⟨houtputF ▸ hpostFrame, hX.toS,
                (hrootsPlace.trans hrootsSize).trans (hrootsFill.trans hrootsTruncate),
                (hvaluesPlace.trans hvaluesSize).trans (hvaluesFill.trans hvaluesTruncate), hsafeTruncate,
                hretained,
                fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                  (StoreLe.trans (hpilotSize hprofile)
                    (StoreLe.trans (hpilotFill hprofile) (hpilotTruncate hprofile))),
                TSame.refl _, hT.ext hX.dom hcur,
                hforbiddenPre.trans (statementStoreForbidden hFFillOut hgamPlace.1 hdisjoint
                  (truncate_except_owner sFill.store destination l newLen htruncate)),
                hmutationPre.trans (statementSingleRootMutation
                  (truncate_except_owner sFill.store destination l newLen htruncate) hchanged),
                by simp [Stmt.diverges]⟩
          | growshrink element =>
            have hownerElement : element = el := by simpa [Ty.ownerElem?] using hownerElem
            subst el
            let newLen := (wrap .i64 sizeInt).toNat
            have hownerGS : LocTy sFill.store l (.growshrink element) :=
              hownerLoc
            obtain ⟨destination, htruncate⟩ := statementTruncateGrowshrinkTotal hownerGS
              ⟨len, hlen, Nat.le_of_lt hshrink⟩
            have htruncate' : sFill.store.truncate l newLen = .ok destination := by
              simpa [newLen] using htruncate
            have hrun :
                (do
                  truncateLoc l newLen
                  pure (Flow.normal Val.unit)) sFill =
                  .ok (Flow.normal Val.unit) { sFill with store := destination } := by
              change (M.bind' (truncateLoc l newLen)
                (fun (_ : Unit) => M.pure' (Flow.normal Val.unit))) sFill = _
              simp only [M.bind', truncateLoc, htruncate', M.pure']
            have hmutationPhase : DemandNodeHasPhase
                (DemandNode.statement (.resize owner size (some e) o)) .mutation := by
              simp [DemandNodeHasPhase, DemandNode.phaseMatches]
            have haccessMutation :=
              (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
            have hactiveMutation := ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
            have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
            change (statementMutationContext ec hmutationPhase).AccessMatches tenv penv
              at haccessMutation
            change (statementMutationContext ec hmutationPhase).ActiveMatches tenv
              at hactiveMutation
            change (statementMutationContext ec hmutationPhase).outputFuture = ec.outputFuture
              at houtputMutation
            have hretainedMutation : ∀ alias, alias ∈ ec.retained →
                alias ∈ (statementMutationContext ec hmutationPhase).retained := by
              intro alias hmem
              exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
            cases hmutation : statementMutationContext ec hmutationPhase with
            | pilot profile _ =>
              simp [requireShrink, rej, hF.mod_t, profile] at hrequire
              change Except.error _ = Except.ok _ at hrequire
              cases hrequire
            | @shrink pc profile mutationContext =>
              have hdirect :
                  (DemandNode.statement (.resize owner size (some e) o)).directShrinkPlace? =
                    some owner := by simp [DemandNode.directShrinkPlace?]
              obtain ⟨_, hownerResult, _⟩ :=
                mutationContext.sourceAt.directShrinkOwner_result rfl hdirect
                  pc.approvals.accessMatches
              obtain ⟨approval, _, hsameOwner, _, hframe⟩ :=
                mutationContext.directShrinkApproval hdirect hownerResult
              rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
              have hownerP : Gam env W.ownerP ownerRoots l.root :=
                hgamPlace.2.1 ⟨element, Or.inr rfl⟩
              have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hownerP
              have hownerBroadFacts := statementCheckedShrinkOwnerFacts (W := W)
                haccessMutation hownerResult hownerTy hownerRp hgamPlace.1
              have hclassifiedPost := hF.classifiedParameters_advance
                (hclassified profile) ((hXPlace.trans hXSize).trans hXFill)
              have hheader : l.path = [] :=
                PlaceOk.ownerHeader hplace (by simpa [Ty.ownerElem?] using hownerElem)
              have authority := statementDirectShrinkAuthority mutationContext profile hdirect
                hownerResult hownerFacts.2.1 (Or.inr rfl) hownerFacts.2.2 hownerP
                hFFillOut hp hclassifiedPost hsafeFill.typed hheader hownerLoc
                (fun target htarget => hE8.2.2.2.1 target (hinShrink target htarget))
              have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
                W.ownerP observation l.root
              change (statementMutationContext ec hmutationPhase).mayShrink
                W.ownerP observation l.root ↔ ec.mayShrink W.ownerP observation l.root at hmay
              rw [hmutation] at hmay
              have hshrinkAuthority :
                  (ec.mayShrink W.ownerP observation l.root ∨
                    ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
                    (∀ g, l.root = .global g → g < W.G) :=
                ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
              have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
                intro x hx
                exact (hframe.1 x).2 ((hactiveMutation x).2 hx)
              have hfutureNeeded : ∀ x, x ∈ fillEc.outputFuture →
                  x ∈ approval.point.future := by
                intro x hx
                apply (hframe.2.1 x).2
                change x ∈ mutationContext.expected.frame.future
                change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
                rw [houtputMutation]
                rw [← houtputF]
                exact hx
              have happrovalAccess : approval.access = pc.approvals.access :=
                Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
              have haccessEq : approval.access = penv.access :=
                happrovalAccess.trans hownerFacts.1
              have happrovalTy : approval.shrinkOwner.ty = some (.growshrink element) := by
                rw [hsameOwner]
                exact hownerFacts.2.1
              have happrovalRoot : Gam env W.P approval.shrinkOwner.roots l.root := by
                rw [hsameOwner]
                exact hownerBroadFacts.2.2
              have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
                  alias ∈ approval.point.retained := by
                intro alias hmem
                exact (hframe.2.2 alias).2 (hretainedMutation alias hmem)
              have hheader : l.path = [] :=
                PlaceOk.ownerHeader hplace (by simpa [Ty.ownerElem?] using hownerElem)
              have hflat : element.flat = true :=
                statementOwnerElementFlat hplace hownerElem
              obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate,
                hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
                statementResizableTruncatePreservation hFFillOut haccessEq happrovalTy
                  (Or.inr rfl) happrovalRoot hownerLoc hvisibleActive hfutureNeeded profile
                  hprotected hsafeFill hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
                  hretainedNeeded htruncate
              have hX := ((hXPlace.trans hXSize).trans hXFill).trans hfoot
              have hretained : RetainsAliases m W env s.store
                  ({ sFill with store := destination }).store ec.retained :=
                hretPlace.trans
                  ((hretSize.subset (fun alias hmem =>
                    ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                      hchildS hphaseS hmem)).trans
                    ((hretFill.subset (fun alias hmem =>
                      ec.child_retained_subset rfl 2 (DemandNode.expression e) .expression
                        hchildF hphaseF hmem)).trans hretainedTruncate))
              unfold Sat
              rw [hrun]
              exact ⟨houtputF ▸ hpostFrame, hX.toS,
                (hrootsPlace.trans hrootsSize).trans (hrootsFill.trans hrootsTruncate),
                (hvaluesPlace.trans hvaluesSize).trans (hvaluesFill.trans hvaluesTruncate), hsafeTruncate,
                hretained,
                fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                  (StoreLe.trans (hpilotSize hprofile)
                    (StoreLe.trans (hpilotFill hprofile) (hpilotTruncate hprofile))),
                TSame.refl _, hT.ext hX.dom hcur,
                hforbiddenPre.trans (statementStoreForbidden hFFillOut hgamPlace.1 hdisjoint
                  (truncate_except_owner sFill.store destination l newLen htruncate)),
                hmutationPre.trans (statementSingleRootMutation
                  (truncate_except_owner sFill.store destination l newLen htruncate) hchanged),
                by simp [Stmt.diverges]⟩
          | int _ | bool | unit | arr _ _ | ref _ _ | slice _ _ | tuple _ | structT _ _ =>
            simp [Ty.ownerElem?] at hownerElem
        · simp only [hshrink, if_false]
          by_cases hequal : ((wrap .i64 sizeInt).toNat == len) = true
          · simp only [hequal, if_pos, sat_pure]
            have hretained : RetainsAliases m W env s.store sFill.store ec.retained :=
              hretPlace.trans
                ((hretSize.subset (fun alias hmem =>
                  ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                    hchildS hphaseS hmem)).trans
                  (hretFill.subset (fun alias hmem =>
                    ec.child_retained_subset rfl 2 (DemandNode.expression e) .expression
                      hchildF hphaseF hmem)))
            exact ⟨houtputF ▸ hFFillOut, (hXPlace.trans hXSize).trans hXFill |>.toS,
              (hrootsPlace.trans hrootsSize).trans hrootsFill,
              (hvaluesPlace.trans hvaluesSize).trans hvaluesFill, hsafeFill, hretained,
              fun hprofile => StoreLe.trans (hpilotPlace hprofile)
                (StoreLe.trans (hpilotSize hprofile) (hpilotFill hprofile)),
              TSame.refl _, hT.ext ((hXPlace.trans hXSize).trans hXFill).dom hcur,
              hforbiddenPre, hmutationPre, by simp [Stmt.diverges]⟩
          · have hnotEqual : ((wrap .i64 sizeInt).toNat == len) = false := by
              cases hbool : ((wrap .i64 sizeInt).toNat == len) <;> simp_all
            simp only [hnotEqual, Bool.false_eq_true, if_false]
            have hElFlat : el.flat = true := by
              cases t <;> simp_all [Ty.refTarget, Ty.ownerElem?]
            have hfillFlat : FlatTy el fillValue := hfillValueTy.flat hElFlat
            have hreplicated : ∀ (i : Nat) (v : Val),
                (Array.replicate ((wrap .i64 sizeInt).toNat - len) fillValue)[i]? =
                  some v → FlatTy el v := by
              intro i v hv
              rw [Array.getElem?_replicate] at hv
              split at hv
              · cases hv
                exact hfillFlat
              · contradiction
            have haction :
                (do
                  checkAppendCapacity l ((wrap .i64 sizeInt).toNat - len) o
                  let _ ← appendLoc l
                    (Array.replicate ((wrap .i64 sizeInt).toNat - len) fillValue)
                  pure (Flow.normal Val.unit)) =
                checkedAppendLoc l
                  (Array.replicate ((wrap .i64 sizeInt).toNat - len) fillValue) o >>= fun _ =>
                    pure (Flow.normal Val.unit) := by
              simpa [checkedAppendLoc] using
                (statementBindAssoc (checkAppendCapacity l
                    ((wrap .i64 sizeInt).toNat - len) o)
                  (fun _ : Unit => appendLoc l
                    (Array.replicate ((wrap .i64 sizeInt).toNat - len) fillValue))
                  (fun _ : Nat => pure (Flow.normal Val.unit))).symm
            rw [haction]
            refine sat_checkedAppendLoc_bind (l := l)
              (vs := Array.replicate ((wrap .i64 sizeInt).toNat - len) fillValue)
              (owner := t) (E := el) (org := o) (s := sFill)
              (f := fun _ => pure (Flow.normal Val.unit))
              hownerLoc hownerElem hElFlat hreplicated (fun st' i happ hstep => ?_)
            simp only [sat_pure]
            have hrootsAppend : PreservesRootTypes m W.G observation.roots sFill.store st' :=
              statementAppendPreservesRootTypes hownerLoc happ hstep
            obtain ⟨_, hvaluesAppend, hsafeAppend, hretainedAppend, hpilotAppend⟩ :=
              statementFlatStepPreservation (s := sFill) (s' := { sFill with store := st' })
                (env := env) (aliases := fillEc.retained) hsafeFill hrootsAppend hstep
            have hfootAppend : Footprint (insts env) (Dset W) sFill { sFill with store := st' } :=
              Footprint.of_flatStep hstep
            have hretained : RetainsAliases m W env s.store
                ({ sFill with store := st' }).store ec.retained :=
              hretPlace.trans
                ((hretSize.subset (fun alias hmem =>
                  ec.child_retained_subset rfl 1 (DemandNode.expression size) .expression
                    hchildS hphaseS hmem)).trans
                  ((hretFill.trans hretainedAppend).subset (fun alias hmem =>
                    ec.child_retained_subset rfl 2 (DemandNode.expression e) .expression
                      hchildF hphaseF hmem)))
            have hX := ((hXPlace.trans hXSize).trans hXFill).trans hfootAppend
            exact ⟨houtputF ▸ hFFillOut.flatStep hstep, hX.toS,
              (hrootsPlace.trans hrootsSize).trans (hrootsFill.trans hrootsAppend),
              (hvaluesPlace.trans hvaluesSize).trans (hvaluesFill.trans hvaluesAppend),
              hsafeAppend, hretained,
              fun hprofile' => StoreLe.trans (hpilotPlace hprofile')
                (StoreLe.trans (hpilotSize hprofile')
                  (StoreLe.trans (hpilotFill hprofile') (hpilotAppend hprofile'))),
              TSame.refl _, hT.ext hX.dom hcur,
              hforbiddenPre.trans (statementStoreForbidden hFFillOut hgamPlace.1 hdisjoint
                (append_except_owner _ _ _ _ _ happ)),
              hmutationPre.trans (statementSingleRootMutation
                (append_except_owner _ _ _ _ _ happ) hchanged),
              by simp [Stmt.diverges]⟩
  | assignWhole owner replacement org =>
    obtain ⟨hprofile, htenv, element, target, binding, contents, middle, last,
      htarget, hownerTy, hreplacementTy, htn⟩ := statementAssignWholeTypeInputs ht
    subst tenv'
    subst tn'
    have hmProfile : m.profile = .shrink :=
      (congrArg Module.profile hF.mod_t).symm.trans hprofile
    rw [rpStmt] at hr
    rcases (st_bind_ok _ _ _ _).1 hr with ⟨ownerRoots, r1, hownerRp, hrestRp⟩
    rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r2, hreads, hrestRp⟩
    rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r3, hshrinks, hrestRp⟩
    rcases (st_bind_ok _ _ _ _).1 hrestRp with
      ⟨replacementRoots, r4, hreplacementRp, hrestRp⟩
    rcases (st_bind_ok _ _ _ _).1 hrestRp with ⟨_, r5, hwrites, hgrows⟩
    have hfinal5E := (PMono.addGrows ownerRoots r5 () rst' hgrows).2
    have hfinal4E := (PMono.addWrites ownerRoots r4 () r5 hwrites).2.trans hfinal5E
    have hfinal3E := (rpExpr_mono hreplacementRp).2.trans hfinal4E
    have hfinal2E := (PMono.addShrinks ownerRoots r2 () r3 hshrinks).2.trans hfinal3E
    have hfinal1E := (PMono.addReads ownerRoots r1 () r2 hreads).2.trans hfinal2E
    have hfinal5R := PMonoRebinds.addGrows ownerRoots r5 () rst' hgrows
    have hfinal4R := (PMonoRebinds.addWrites ownerRoots r4 () r5 hwrites).trans hfinal5R
    have hfinal3R := (rpExpr_rebinds_mono hreplacementRp).trans hfinal4R
    have hfinal2R := (PMonoRebinds.addShrinks ownerRoots r2 () r3 hshrinks).trans hfinal3R
    have hfinal1R := (PMonoRebinds.addReads ownerRoots r1 () r2 hreads).trans hfinal2R
    have hE1 := hfinal1E.trans hE
    have hE4 := hfinal4E.trans hE
    obtain ⟨_, hinShrinks⟩ := statementAddShrinksOk ownerRoots r2 ((), r3) hshrinks
    have hinShrinksFinal : ∀ t, t ∈ rootsTargets ownerRoots → t ∈ rst'.eff.shrinks := by
      intro t ht
      exact hfinal3E.2.2.2.1 t (hinShrinks t ht)
    have hownerElem : target.ownerElem? = some element := by
      rcases htarget with rfl | rfl <;> simp [Ty.ownerElem?]
    simp only [execStmt]
    have hchildP : (DemandNode.statement (.assignWhole owner replacement org)).child? 0 =
        some (DemandNode.place owner) := by simp [DemandNode.child?, DemandNode.children]
    have hphaseP : DemandNodeHasPhase (DemandNode.place owner) .place := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    have hvisibleP : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.assignWhole owner replacement org)).visibleForChild
          tenv.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hresultP := statementPlaceChildSpec ih ec observation W tenv penv env s 0 owner
      hchildP hactive haccess hprotected hobserved hclassified hp hF hvisibleP
      (statementAssignWholePlaceInputSubset ec) _ _ _ _ _ _ _ _ hownerTy hownerRp hE1
    refine Sat.bind hresultP ?_
    rintro location sPlace ⟨hFPlace, hXPlace, hrootsPlace, hvaluesPlace, hsafePlace,
      hretPlace, hpilotPlace, hplace, hgamPlace, hownerPlace, hforbiddenPlace,
      hmutationPlace⟩
    have hdisjointRuntime := statementPlaceForbiddenDisjoint ec haccess hchildP hownerRp
    have hchildE :
        (DemandNode.statement (.assignWhole owner replacement org)).child? 1 =
          some (DemandNode.expression replacement) := by
      simp [DemandNode.child?, DemandNode.children]
    have hphaseE : DemandNodeHasPhase (DemandNode.expression replacement) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 1 replacement hchildE
    have hFExprInput := statementAssignWholeExprInputFrame ec hactive hFPlace
    have houtputE : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.expression replacement).visibleAfter
          ((DemandNode.statement (.assignWhole owner replacement org)).visibleForChild active 1) =
          (DemandNode.statement (.assignWhole owner replacement org)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 1 (DemandNode.expression replacement) .expression
          hchildE hphaseE
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.assignWhole owner replacement org))
            stmtPlanContext.approvals.access
            ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 1 = some ⟨
                (DemandNode.statement (.assignWhole owner replacement org)).visibleForChild
                  context.expected.frame.active 1,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildE]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    have hownerLoc : LocTy sPlace.store location target := by
      rcases hplace with ⟨_, hloc, _⟩ |
        ⟨x, lv, si, value, _, _, _, _, _, href, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, hpath, _⟩
      · exact access hp hloc hgamPlace (fun t ht =>
          Or.inr (Or.inr (Or.inr (hE.2.2.2.1 t (hinShrinksFinal t ht)))))
      · cases target <;> simp_all [Ty.ownerElem?, Ty.isRefLike]
      · rw [hpath] at hownerElem
        simp [Ty.ownerElem?] at hownerElem
    have hheader : location.path = [] := hplace.ownerHeader (by simp [hownerElem])
    have hownerGS : LocTy sPlace.store location (.growshrink element) := by
      rcases htarget with rfl | rfl
      · exact hownerLoc.grow_to_growshrink
      · exact hownerLoc
    refine statementAssignWholeTruncateBind hownerGS ?_
    intro destination htruncate
    obtain ⟨ownerRequest, haccessSome, hownerResultP, hrequestTy, hrequestRoot,
      hcheckedRoots, hFClear, hfootClear, hrootsClear, hvaluesClear, hsafeClear,
      hretainedClear, hpilotClear, hclassifiedClearActual⟩ :=
      statementAssignWholeClearFrame ec hmProfile hactive haccess hprotected hp
        htarget hownerTy hownerRp hplace hownerLoc hgamPlace
        (hownerPlace ⟨element, htarget⟩)
        (fun t ht => hE.2.2.2.1 t (hinShrinksFinal t ht)) hFPlace hsafePlace
        (hF.classifiedParameters_advance (hclassified hmProfile) hXPlace) htruncate
    have hXClear := hXPlace.trans hfootClear
    have hclassifiedClear : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation destination :=
      fun _ => hclassifiedClearActual
    have hvisibleE : ∀ x, x ∈ tenv.visible ↔
        x ∈ (DemandNode.statement (.assignWhole owner replacement org)).visibleForChild
          tenv.visible 1 := by
      simp [DemandNode.visibleForChild]
    have hresultE := statementExprChildSpecAtFrame ih ec observation W tenv tenv penv env
      { sPlace with store := destination } 1 replacement hchildE hactive haccess hprotected
      hsafeClear hclassifiedClear hp childEc rfl hFClear hvisibleE ec.retained
      (fun alias hmem => ec.child_retained_subset rfl 1
        (DemandNode.expression replacement) .expression hchildE hphaseE hmem)
      middle last target r3 r4 replacementRoots hreplacementTy hreplacementRp hE4
    have hownerForbidden : ownerRequest ∈ childEc.forbiddenOwners := by
      exact ec.child_assignWhole_owner rfl 1 (DemandNode.expression replacement)
        .expression hchildE hphaseE penv.access haccessSome owner replacement org
        rfl rfl ownerRequest hownerResultP
    have hrequestType : ownerRequest.ty = some (.grow element) ∨
        ownerRequest.ty = some (.growshrink element) := by
      rcases htarget with rfl | rfl
      · exact Or.inl hrequestTy
      · exact Or.inr hrequestTy
    have hstaticDisjoint := statementPlaceForbiddenStaticDisjoint ec haccess hchildP
      hcheckedRoots
    have hparentSubset : ∀ excluded, excluded ∈ ec.forbiddenOwners →
        excluded ∈ childEc.forbiddenOwners := by
      exact ec.child_forbidden_subset rfl 1 (DemandNode.expression replacement)
        .expression hchildE hphaseE
    have hchanged := statementAssignWholeMutationRoot hFExprInput hgamPlace
      hinShrinksFinal
    have hforbiddenClear := statementStoreForbidden
      (s' := { sPlace with store := destination }) hFExprInput hgamPlace
      hdisjointRuntime (truncate_except_owner sPlace.store destination location 0 htruncate)
    have hmutationClear := statementSingleRootMutation
      (s := sPlace) (s' := { sPlace with store := destination })
      (truncate_except_owner sPlace.store destination location 0 htruncate) hchanged
    refine statementAssignWholeReplacement (m := m) (tenv := tenv) (penv := penv)
      (observation := observation) (shrinking := ec.mayShrink W.ownerP observation)
      (before := sPlace)
      (clear := { sPlace with store := destination }) (future := childEc.outputFuture)
      (aliases := ec.retained) (forbidden := childEc.forbiddenOwners)
      (parentForbidden := ec.forbiddenOwners)
      (effectRoots := effectMutationRoots m penv.impl rst'.eff)
      htarget hownerLoc htruncate hheader hownerForbidden hrequestType
      hrequestRoot hchanged hparentSubset hstaticDisjoint ?_ |>.mono ?_
    · refine hresultE.mono ?_
      intro value evaluated ⟨hFEvaluated, hXEvaluated, hrootsEvaluated,
        hvaluesEvaluated, hsafeEvaluated, hretainedEvaluated, hpilotEvaluated,
        hvalueTy, _, _, hforbiddenParentEvaluated, hforbiddenChildEvaluated,
        hmutationEvaluated⟩
      exact ⟨hFEvaluated, hXEvaluated, hrootsEvaluated, hvaluesEvaluated,
        hsafeEvaluated, hretainedEvaluated, hpilotEvaluated, hvalueTy,
        hforbiddenChildEvaluated,
        (fun hprofile' => hFClear.classifiedParameters_advance
          (hclassifiedClear hprofile') hXEvaluated),
        hmutationEvaluated.weaken
          (effectMutationRoots.mono m penv.impl hfinal4E hfinal4R)⟩
    · intro flow final ⟨hFFinal, hXFinal, hrootsFinal, hvaluesFinal, hsafeFinal,
        hretainedFinal, hpilotFinal, _, _, hforbiddenFinal, hmutationFinal, hflow⟩
      have hX := hXClear.trans hXFinal
      have hforbiddenPre := hforbiddenPlace.trans
        (hforbiddenClear.trans hforbiddenFinal)
      have hmutationPre :=
        ((hmutationPlace.weaken
          (effectMutationRoots.mono m penv.impl hfinal1E hfinal1R)).trans
          hmutationClear).trans hmutationFinal
      exact ⟨houtputE ▸ hFFinal, hX.toS,
        (hrootsPlace.trans hrootsClear).trans hrootsFinal,
        (hvaluesPlace.trans hvaluesClear).trans hvaluesFinal, hsafeFinal,
        (hretPlace.trans hretainedClear).trans hretainedFinal,
        fun hprofile' => StoreLe.trans (hpilotPlace hprofile')
          (StoreLe.trans (hpilotClear hprofile') (hpilotFinal hprofile')),
        TSame.refl _, hT.ext hX.dom hcur, hforbiddenPre, hmutationPre,
        by subst flow; simp [Stmt.diverges]⟩
  | _ => exact hsel.elim

/-- Lift the binding and write step with the shrink classification carried by
the recursive soundness specification. -/
theorem step_stmt_a (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (st : Stmt)
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    (match st with
      | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append ..
        | .popN .. | .clear .. | .resize .. | .assignWhole .. => True
      | _ => False) →
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) →
    ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt (n + 1) ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ec.outputFuture ∧ FootprintS env (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ TSame tenv tenv' ∧ TopB env lo rst'.nextVar s' ∧
      (match fl with
       | .normal _ => st.diverges m.noReturn = false
       | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
       | .cont => tenv.loops ≠ 0
       | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  intro path st ec observation W tenv tenv' penv env s sc tn tn' rst rst' lo
    hsel hactive haccess hprotected hobserved hclassified hp hF hsc hT hlo ht hr hE
  have hcore := step_stmt_a_core ih path st ec observation W tenv tenv' penv env s sc
    tn tn' rst rst' lo hsel hactive haccess hprotected hobserved hclassified hp hF hsc hT
    hlo ht hr hE
  exact hcore.mono (fun fl s' hresult => by
    rcases hresult with ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hsame, htop, hforbidden, hmutation, hflow⟩
    exact ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hsame, htop, hflow,
      (fun hprofile => ClassifiedParameters.advanceS (hclassified hprofile) hF hfp),
      hforbidden, hmutation⟩)

set_option maxHeartbeats 1600000 in
theorem step_expr_pop (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (owner : Place) (org : OriginId)
    (ec : EvaluationContext m plans path (.expression (.pop owner org)) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) →
    ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyExpr tenv (.pop owner org) tn = .ok (ty, tn') →
    rpExpr penv (.pop owner org) rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env (.pop owner org)) s (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      OwnerRooted env W.ownerP rho v ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  intro path owner org ec observation W tenv penv env s tn tn' ty rst rst' rho
    hactive haccess hprotected hobserved hclassified hp hF ht hr hE
  simp only [tyExpr] at ht
  inv at ht
  obtain ⟨typingStart, hrequireShrink, horg, t, bindingWritable, contentsWritable,
    tn1, hownerTy, element, tn2, hownerElement, hwrite, hty, htn⟩ := ht
  subst ty
  subst tn'
  simp only [rpExpr] at hr
  inv at hr
  obtain ⟨ownerRoots, r1, hownerRp, r2, hreads, r3, hshrinks, r4, haborts,
    hrho, hrst⟩ := hr
  subst rho
  subst rst'
  have hfinal3E := (PMono.noteAborts r3 () r4 haborts).2
  have hfinal2E := (PMono.addShrinks ownerRoots r2 () r3 hshrinks).2.trans hfinal3E
  have hfinalE := (PMono.addReads ownerRoots r1 () r2 hreads).2.trans hfinal2E
  have hnoteAborts : PMonoRebinds noteAborts := by
    unfold noteAborts
    exact PMonoRebinds.modify _ (fun _ _ h => h)
  have hfinal3R := hnoteAborts r3 () r4 haborts
  have hfinal2R := (PMonoRebinds.addShrinks ownerRoots r2 () r3 hshrinks).trans hfinal3R
  have hfinalR := (PMonoRebinds.addReads ownerRoots r1 () r2 hreads).trans hfinal2R
  have hE4 : EffLe r4.eff W.E := hE
  have hE3 : EffLe r3.eff W.E := hfinal3E.trans hE
  have hE2 : EffLe r2.eff W.E :=
    (PMono.addShrinks ownerRoots r2 () r3 hshrinks).2.trans hE3
  have hE1 : EffLe r1.eff W.E :=
    (PMono.addReads ownerRoots r1 () r2 hreads).2.trans hE2
  obtain ⟨_, hinShrinks⟩ := statementAddShrinksOk ownerRoots r2 ((), r3) hshrinks
  have hownerElem : t.ownerElem? = some element :=
    (ownerElement_ok tenv t element tn1 tn2 hownerElement).2.1
  simp only [evalExpr]
  let child := ec.child rfl 0 (.place owner) .place rfl (by trivial)
  have hChildActive := ec.child_activeMatches rfl 0 (.place owner) .place rfl
    (by trivial) tenv tenv hactive (by intro x; rfl)
  have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.place owner) .place rfl
    (by trivial) tenv penv).mpr haccess
  have hChildShrink : child.mayShrink W.ownerP observation =
      ec.mayShrink W.ownerP observation := by
    funext root
    exact propext (ec.child_mayShrink_iff rfl 0 (.place owner) .place rfl
      (by trivial) W.ownerP observation root)
  have hChildFuture : child.outputFuture = ec.outputFuture := by
    cases ec with
    | pilot profile active => simp [child, EvaluationContext.child,
        EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
    | shrink profile context =>
      let transition := context.child rfl 0 (.place owner) .place rfl (by trivial)
      change transition.context.expected.frame.future = context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
      exact DemandNode.childFrame_future transition.childFrameEq rfl
  have hChildInputFormula : child.inputFuture = owner.variables ++ child.outputFuture := by
    cases ec <;> rfl
  have hChildInput : child.inputFuture = ec.inputFuture := by
    rw [hChildInputFormula, hChildFuture]
    cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
      NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
      Place.variables, Expr.variables, DemandNode.visibleAfter]
  refine Sat.bind (ih.place (path ++ [0]) owner child observation W tenv penv env s
    _ _ _ _ _ _ _ _ hChildActive hChildAccess (by simpa [hChildShrink] using hprotected)
    (by simpa [hChildShrink] using hobserved) hclassified hp
    (by simpa [hChildInput] using hF) hownerTy hownerRp hE1) ?_
  rintro l s1 ⟨hF1, hX1, hroots1, hvalues1, hsafe1, hret1, hpilot1,
    hplace, hgam, _, hownerRooted, hforbiddenPlace, hmutationPlace⟩
  have hframe1 : Frame m W tenv penv env s1 ec.outputFuture := by
    simpa [hChildFuture] using hF1
  have hsafe1' : ObservedSafe m W (ec.mayShrink W.ownerP observation)
      observation s1.store := by
    simpa [hChildShrink] using hsafe1
  have hretainedPlace := hret1.subset (fun alias hmem =>
    ec.child_retained_subset rfl 0 (.place owner) .place rfl (by trivial) hmem)
  have hforbiddenPlace' := PreservesForbiddenOwnerRoots.subset hforbiddenPlace
    (fun forbidden hforbidden => ec.child_forbidden_subset rfl 0 (.place owner) .place
      rfl (by trivial) forbidden hforbidden)
  have hmutationPre := hmutationPlace.weaken
    (effectMutationRoots.mono m penv.impl hfinalE hfinalR)
  have hownerPlace : PlaceOk m W.G W.P penv env s1.store owner l t := hplace
  have hLoc : LocTy s1.store l t := by
    rcases hplace with ⟨_, hloc, _⟩ |
      ⟨x, lv, si, v, hplaceEq, hvar, hscope, hloc, hty, hrefLike, hroot, htyped⟩ |
      ⟨x, lv, mu0, mu, E, ann, hplaceEq, hvar, hty, htarget, hflat, hpath,
        hann, hgam', hroot⟩
    · exact access hp hloc hgam (fun target htarget =>
        Or.inr (Or.inr (Or.inr (hE4.2.2.2.1 target
          (hfinal3E.2.2.2.1 target (hinShrinks target htarget))))))
    · cases t <;> simp_all [Ty.ownerElem?, Ty.isRefLike]
    · rw [htarget] at hownerElem
      simp [Ty.ownerElem?] at hownerElem
  have hchanged := statementEffectMutationRoot hframe1 hgam (effect := r4.eff) (by
    intro target hmem
    simp only [effectMutationTargets, List.mem_append]
    exact Or.inl (Or.inr (hfinal3E.2.2.2.1 target (hinShrinks target hmem))))
  have hdisjoint : ∀ forbidden, forbidden ∈ ec.forbiddenOwners →
      DemandRootsDisjoint forbidden.roots ownerRoots := by
    cases ec with
    | pilot profile active => simp [EvaluationContext.forbiddenOwners]
    | @shrink pc profile context =>
      intro forbidden hforbidden
      let transition := context.child rfl 0 (.place owner) .place rfl (by trivial)
      have hchildForbidden := transition.forbiddenSubset forbidden hforbidden
      obtain ⟨checkedRoots, hchecked, hcheckedDisjoint⟩ :=
        transition.context.placeWholeRootsChecked forbidden hchildForbidden
      have haccessEq : pc.approvals.access = penv.access := by
        have hAccessMod := haccess.2.2.1
        have hAccessImpl := haccess.2.2.2.1
        have hAccessCtx := haccess.2.2.2.2
        cases hAccessValue : pc.approvals.access
        rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
        unfold PEnv.access
        congr 1
      rw [haccessEq] at hchecked
      have hincluded := rpPlace_accessRoots penv owner rst ownerRoots r1 checkedRoots
        hownerRp hchecked
      intro forbiddenRoot hforbiddenRoot checkedRoot hcheckedRoot
      exact hcheckedDisjoint forbiddenRoot hforbiddenRoot checkedRoot
        (hincluded checkedRoot hcheckedRoot)
  have helementFlat : element.flat = true :=
    statementOwnerElementFlat hownerPlace hownerElem
  refine Sat.bind (R := fun len state => state = s1 ∧ s1.store.length l = .ok len)
    (sat_lengthLoc_owner hLoc hownerElem
    (fun len hlength => ⟨rfl, hlength⟩)) ?_
  rintro len state ⟨hstate, hlength⟩
  subst state
  split
  · simp [Sat, abortAt, M.stop]
  · rename_i hnonempty
    have hpositive : 0 < len := by
      have hne : len ≠ 0 := by simpa using hnonempty
      omega
    have hlenSucc : len = (len - 1) + 1 := by omega
    cases t with
    | limited storedElement capacity =>
      have helementEq : storedElement = element := by
        simpa [Ty.ownerElem?] using hownerElem
      subst element
      obtain ⟨ownerValue, hownerRead, hownerFlat⟩ := hLoc
      cases ownerValue with
      | limited actualElement actualCapacity slots currentLen =>
        simp only [FlatTy] at hownerFlat
        obtain ⟨rfl, rfl, hcapacity, hcurrentSlots, hslots⟩ := hownerFlat
        have hLocLimited : LocTy s1.store l (.limited storedElement capacity) :=
          ⟨.limited storedElement capacity slots currentLen, hownerRead,
            ⟨rfl, rfl, hcapacity, hcurrentSlots, hslots⟩⟩
        have hcurrentLen : currentLen = len := by
          have hlength' : s1.store.length l = .ok currentLen := by
            simp [Store.length, hownerRead]
          exact Except.ok.inj (hlength'.symm.trans hlength)
        subst currentLen
        have hindex : len - 1 < slots.size := by omega
        let popped := slots[len - 1]
        have hpopped : slots[len - 1]? = some popped :=
          Array.getElem?_eq_getElem hindex
        have hreadPopped : s1.store.read ⟨l.root, l.path ++ [len - 1]⟩ = .ok popped :=
          (read_limitedElem_iff hownerRead).2 hpopped
        have hflatPopped : FlatTy storedElement popped := hslots _ _ hpopped
        have hlocPopped : LocTy s1.store ⟨l.root, l.path ++ [len - 1]⟩ storedElement :=
          ⟨popped, hreadPopped, hflatPopped⟩
        refine sat_readLoc_bind hlocPopped (fun value hreadValue hflatValue => ?_)
        obtain ⟨destination, htruncate⟩ := statementTruncateLimitedTotal hLocLimited
          ⟨len, hlength, Nat.sub_le _ _⟩
        have hstep := statementTruncateLimitedFlatStep hLocLimited htruncate
        apply sat_statementTruncateLoc_bind htruncate
        simp only [sat_pure]
        have hrootsTruncate : PreservesRootTypes m W.G observation.roots
            s1.store destination :=
          statementModifyPreservesRootTypes hstep.le hLocLimited htruncate
        obtain ⟨_, hvaluesTruncate, hsafeTruncate, hretainedTruncate,
            hpilotTruncate⟩ :=
          statementFlatStepPreservation (s := s1) (s' := { s1 with store := destination })
            (env := env) (aliases := ec.retained) hsafe1' hrootsTruncate hstep
        have hfoot : Footprint (insts env) (Dset W) s1 { s1 with store := destination } :=
          Footprint.of_flatStep hstep
        have hX := hX1.trans hfoot
        refine ⟨hframe1.flatStep hstep, hX, hroots1.trans hrootsTruncate,
          hvalues1.trans hvaluesTruncate, hsafeTruncate,
          hretainedPlace.trans hretainedTruncate,
          fun hprofile => StoreLe.trans (hpilot1 hprofile) (hpilotTruncate hprofile),
          hasTy_of_flat hflatValue (Or.inl helementFlat), flat_no_targets hflatValue,
          (fun hprofile => hF.classifiedParameters_advance (hclassified hprofile) hX), ?_,
          hforbiddenPlace'.trans (statementStoreForbidden hframe1 hgam hdisjoint
            (truncate_except_owner s1.store destination l (len - 1) htruncate)),
          hmutationPre.trans (statementSingleRootMutation
            (truncate_except_owner s1.store destination l (len - 1) htruncate) hchanged)⟩
        unfold OwnerRooted
        intro howner
        rcases howner with ⟨mu, ownerElement, howner | howner⟩ <;>
          cases howner <;> simp [Ty.flat] at helementFlat
      | _ => simp [FlatTy] at hownerFlat
    | grow storedElement =>
      have helementEq : storedElement = element := by
        simpa [Ty.ownerElem?] using hownerElem
      subst element
      obtain ⟨ownerValue, hownerRead, hownerFlat⟩ := hLoc
      cases ownerValue with
      | resizable actualElement slots =>
        simp only [FlatTy] at hownerFlat
        obtain ⟨rfl, hslots⟩ := hownerFlat
        have hLocGrow : LocTy s1.store l (.grow storedElement) :=
          ⟨.resizable storedElement slots, hownerRead, ⟨rfl, hslots⟩⟩
        have hsize : len = slots.size := by
          have hlength' : s1.store.length l = .ok slots.size := by
            simp [Store.length, hownerRead]
          exact Except.ok.inj (hlength.symm.trans hlength')
        have hindex : len - 1 < slots.size := by omega
        let popped := slots[len - 1]
        have hpopped : slots[len - 1]? = some popped :=
          Array.getElem?_eq_getElem hindex
        have hreadPopped : s1.store.read ⟨l.root, l.path ++ [len - 1]⟩ = .ok popped :=
          (read_resizableElem_iff hownerRead).2 hpopped
        have hflatPopped : FlatTy storedElement popped := hslots _ _ hpopped
        have hlocPopped : LocTy s1.store ⟨l.root, l.path ++ [len - 1]⟩ storedElement :=
          ⟨popped, hreadPopped, hflatPopped⟩
        refine sat_readLoc_bind hlocPopped (fun value hreadValue hflatValue => ?_)
        obtain ⟨destination, htruncate⟩ := statementTruncateGrowTotal hLocGrow
          ⟨len, hlength, Nat.sub_le _ _⟩
        have hmutationPhase : DemandNodeHasPhase
            (DemandNode.expression (.pop owner org)) .mutation := by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches]
        let mutationEc := ec.phase rfl .mutation hmutationPhase
        have haccessMutation :=
          (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
        have hactiveMutation :=
          ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
        have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
        change mutationEc.AccessMatches tenv penv at haccessMutation
        change mutationEc.ActiveMatches tenv at hactiveMutation
        change mutationEc.outputFuture = ec.outputFuture at houtputMutation
        have hretainedMutation : ∀ alias, alias ∈ ec.retained →
            alias ∈ mutationEc.retained := by
          intro alias hmem
          exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
        cases hmutation : mutationEc with
        | pilot profile active =>
          simp [requireShrink, rej, hF.mod_t, profile] at hrequireShrink
          change Except.error _ = Except.ok _ at hrequireShrink
          cases hrequireShrink
        | @shrink pc profile mutationContext =>
          have hdirect : (DemandNode.expression (.pop owner org)).directShrinkPlace? =
              some owner := by simp [DemandNode.directShrinkPlace?]
          obtain ⟨ownerRequest, hownerResult, _⟩ :=
            mutationContext.sourceAt.directShrinkOwner_result rfl hdirect
              pc.approvals.accessMatches
          obtain ⟨approval, _, hsameOwner, _, happrovalFrame⟩ :=
            mutationContext.directShrinkApproval hdirect hownerResult
          rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
          have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
            haccessMutation hownerResult hownerTy hownerRp hgam
          have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
            intro x hx
            exact (happrovalFrame.1 x).2 ((hactiveMutation x).2 hx)
          have hfutureNeeded : ∀ x, x ∈ ec.outputFuture → x ∈ approval.point.future := by
            intro x hx
            apply (happrovalFrame.2.1 x).2
            change x ∈ mutationContext.expected.frame.future
            change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
            rw [houtputMutation]
            exact hx
          have happrovalAccess : approval.access = pc.approvals.access :=
            Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
          have haccessEq : approval.access = penv.access :=
            happrovalAccess.trans hownerFacts.1
          have happrovalTy := hsameOwner ▸ hownerFacts.2.1
          have happrovalRoot := hsameOwner ▸ hownerFacts.2.2
          have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
              alias ∈ approval.point.retained := by
            intro alias hmem
            exact (happrovalFrame.2.2 alias).2 (hretainedMutation alias hmem)
          have hheader : l.path = [] :=
            hownerPlace.ownerHeader (by simp [Ty.ownerElem?])
          have hflat : storedElement.flat = true := helementFlat
          have hshrinkAuthority :
              (ec.mayShrink W.ownerP observation l.root ∨
                ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
              (∀ g, l.root = .global g → g < W.G) := by
            have hownerP : Gam env W.ownerP ownerRoots l.root :=
              hownerRooted ⟨storedElement, Or.inl rfl⟩
            have hrequestFacts := statementCheckedShrinkOwnerFacts (W := W)
              haccessMutation hownerResult hownerTy hownerRp hownerP
            have hclassifiedPost :=
              hF.classifiedParameters_advance (hclassified profile) hX1
            have authority := statementDirectShrinkAuthority mutationContext profile hdirect
              hownerResult hrequestFacts.2.1 (Or.inl rfl) hrequestFacts.2.2 hownerP
              hframe1 hp hclassifiedPost hsafe1'.typed hheader hLocGrow
              (fun target htarget => hE4.2.2.2.1 target
                (hfinal3E.2.2.2.1 target (hinShrinks target htarget)))
            have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
              W.ownerP observation l.root
            change mutationEc.mayShrink W.ownerP observation l.root ↔
              ec.mayShrink W.ownerP observation l.root at hmay
            rw [hmutation] at hmay
            exact ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
          obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate,
              hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
            statementResizableTruncatePreservation hframe1 haccessEq happrovalTy
              (Or.inl rfl) happrovalRoot hLocGrow hvisibleActive hfutureNeeded profile
              hprotected hsafe1' hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
              hretainedNeeded htruncate
          apply sat_statementTruncateLoc_bind htruncate
          simp only [sat_pure]
          have hX := hX1.trans hfoot
          refine ⟨hpostFrame, hX, hroots1.trans hrootsTruncate,
            hvalues1.trans hvaluesTruncate, hsafeTruncate,
            hretainedPlace.trans hretainedTruncate,
            fun hprofile => StoreLe.trans (hpilot1 hprofile) (hpilotTruncate hprofile),
            hasTy_of_flat hflatValue (Or.inl helementFlat), flat_no_targets hflatValue,
            (fun hprofile => hF.classifiedParameters_advance (hclassified hprofile) hX), ?_,
            hforbiddenPlace'.trans (statementStoreForbidden hframe1 hgam hdisjoint
              (truncate_except_owner s1.store destination l (len - 1) htruncate)),
            hmutationPre.trans (statementSingleRootMutation
              (truncate_except_owner s1.store destination l (len - 1) htruncate) hchanged)⟩
          unfold OwnerRooted
          intro howner
          rcases howner with ⟨mu, ownerElement, howner | howner⟩ <;>
            cases howner <;> simp [Ty.flat] at helementFlat
      | _ => simp [FlatTy] at hownerFlat
    | growshrink storedElement =>
      have helementEq : storedElement = element := by
        simpa [Ty.ownerElem?] using hownerElem
      subst element
      obtain ⟨ownerValue, hownerRead, hownerFlat⟩ := hLoc
      cases ownerValue with
      | resizable actualElement slots =>
        simp only [FlatTy] at hownerFlat
        obtain ⟨rfl, hslots⟩ := hownerFlat
        have hLocGrowshrink : LocTy s1.store l (.growshrink storedElement) :=
          ⟨.resizable storedElement slots, hownerRead, ⟨rfl, hslots⟩⟩
        have hsize : len = slots.size := by
          have hlength' : s1.store.length l = .ok slots.size := by
            simp [Store.length, hownerRead]
          exact Except.ok.inj (hlength.symm.trans hlength')
        have hindex : len - 1 < slots.size := by omega
        let popped := slots[len - 1]
        have hpopped : slots[len - 1]? = some popped :=
          Array.getElem?_eq_getElem hindex
        have hreadPopped : s1.store.read ⟨l.root, l.path ++ [len - 1]⟩ = .ok popped :=
          (read_resizableElem_iff hownerRead).2 hpopped
        have hflatPopped : FlatTy storedElement popped := hslots _ _ hpopped
        have hlocPopped : LocTy s1.store ⟨l.root, l.path ++ [len - 1]⟩ storedElement :=
          ⟨popped, hreadPopped, hflatPopped⟩
        refine sat_readLoc_bind hlocPopped (fun value hreadValue hflatValue => ?_)
        obtain ⟨destination, htruncate⟩ :=
          statementTruncateGrowshrinkTotal hLocGrowshrink
            ⟨len, hlength, Nat.sub_le _ _⟩
        have hmutationPhase : DemandNodeHasPhase
            (DemandNode.expression (.pop owner org)) .mutation := by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches]
        let mutationEc := ec.phase rfl .mutation hmutationPhase
        have haccessMutation :=
          (ec.phase_accessMatches_iff rfl .mutation hmutationPhase tenv penv).2 haccess
        have hactiveMutation :=
          ec.phase_activeMatches rfl .mutation hmutationPhase tenv hactive
        have houtputMutation := ec.phase_outputFuture rfl .mutation hmutationPhase
        change mutationEc.AccessMatches tenv penv at haccessMutation
        change mutationEc.ActiveMatches tenv at hactiveMutation
        change mutationEc.outputFuture = ec.outputFuture at houtputMutation
        have hretainedMutation : ∀ alias, alias ∈ ec.retained →
            alias ∈ mutationEc.retained := by
          intro alias hmem
          exact ec.phase_retained_subset rfl .mutation hmutationPhase hmem
        cases hmutation : mutationEc with
        | pilot profile active =>
          simp [requireShrink, rej, hF.mod_t, profile] at hrequireShrink
          change Except.error _ = Except.ok _ at hrequireShrink
          cases hrequireShrink
        | @shrink pc profile mutationContext =>
          have hdirect : (DemandNode.expression (.pop owner org)).directShrinkPlace? =
              some owner := by simp [DemandNode.directShrinkPlace?]
          obtain ⟨ownerRequest, hownerResult, _⟩ :=
            mutationContext.sourceAt.directShrinkOwner_result rfl hdirect
              pc.approvals.accessMatches
          obtain ⟨approval, _, hsameOwner, _, happrovalFrame⟩ :=
            mutationContext.directShrinkApproval hdirect hownerResult
          rw [hmutation] at haccessMutation hactiveMutation houtputMutation hretainedMutation
          have hownerFacts := statementCheckedShrinkOwnerFacts (W := W)
            haccessMutation hownerResult hownerTy hownerRp hgam
          have hvisibleActive : ∀ x, x ∈ tenv.visible → x ∈ approval.point.active := by
            intro x hx
            exact (happrovalFrame.1 x).2 ((hactiveMutation x).2 hx)
          have hfutureNeeded : ∀ x, x ∈ ec.outputFuture → x ∈ approval.point.future := by
            intro x hx
            apply (happrovalFrame.2.1 x).2
            change x ∈ mutationContext.expected.frame.future
            change mutationContext.expected.frame.future = ec.outputFuture at houtputMutation
            rw [houtputMutation]
            exact hx
          have happrovalAccess : approval.access = pc.approvals.access :=
            Option.some.inj (approval.accessMatches.symm.trans pc.approvals.accessMatches)
          have haccessEq : approval.access = penv.access :=
            happrovalAccess.trans hownerFacts.1
          have happrovalTy := hsameOwner ▸ hownerFacts.2.1
          have happrovalRoot := hsameOwner ▸ hownerFacts.2.2
          have hretainedNeeded : ∀ alias, alias ∈ ec.retained →
              alias ∈ approval.point.retained := by
            intro alias hmem
            exact (happrovalFrame.2.2 alias).2 (hretainedMutation alias hmem)
          have hheader : l.path = [] :=
            hownerPlace.ownerHeader (by simp [Ty.ownerElem?])
          have hflat : storedElement.flat = true := helementFlat
          have hshrinkAuthority :
              (ec.mayShrink W.ownerP observation l.root ∨
                ∃ a si x, l.root = .local a si x ∧ W.base ≤ si) ∧
              (∀ g, l.root = .global g → g < W.G) := by
            have hownerP : Gam env W.ownerP ownerRoots l.root :=
              hownerRooted ⟨storedElement, Or.inr rfl⟩
            have hrequestFacts := statementCheckedShrinkOwnerFacts (W := W)
              haccessMutation hownerResult hownerTy hownerRp hownerP
            have hclassifiedPost :=
              hF.classifiedParameters_advance (hclassified profile) hX1
            have authority := statementDirectShrinkAuthority mutationContext profile hdirect
              hownerResult hrequestFacts.2.1 (Or.inr rfl) hrequestFacts.2.2 hownerP
              hframe1 hp hclassifiedPost hsafe1'.typed hheader hLocGrowshrink
              (fun target htarget => hE4.2.2.2.1 target
                (hfinal3E.2.2.2.1 target (hinShrinks target htarget)))
            have hmay := ec.phase_mayShrink_iff rfl .mutation hmutationPhase
              W.ownerP observation l.root
            change mutationEc.mayShrink W.ownerP observation l.root ↔
              ec.mayShrink W.ownerP observation l.root at hmay
            rw [hmutation] at hmay
            exact ⟨authority.1.elim (fun h => Or.inl (hmay.1 h)) Or.inr, authority.2⟩
          obtain ⟨hpostFrame, hfoot, hrootsTruncate, hvaluesTruncate,
              hsafeTruncate, hretainedTruncate, hpilotTruncate⟩ :=
            statementResizableTruncatePreservation hframe1 haccessEq happrovalTy
              (Or.inr rfl) happrovalRoot hLocGrowshrink hvisibleActive hfutureNeeded profile
              hprotected hsafe1' hshrinkAuthority.1 hheader hflat hshrinkAuthority.2
              hretainedNeeded htruncate
          apply sat_statementTruncateLoc_bind htruncate
          simp only [sat_pure]
          have hX := hX1.trans hfoot
          refine ⟨hpostFrame, hX, hroots1.trans hrootsTruncate,
            hvalues1.trans hvaluesTruncate, hsafeTruncate,
            hretainedPlace.trans hretainedTruncate,
            fun hprofile => StoreLe.trans (hpilot1 hprofile) (hpilotTruncate hprofile),
            hasTy_of_flat hflatValue (Or.inl helementFlat), flat_no_targets hflatValue,
            (fun hprofile => hF.classifiedParameters_advance (hclassified hprofile) hX), ?_,
            hforbiddenPlace'.trans (statementStoreForbidden hframe1 hgam hdisjoint
              (truncate_except_owner s1.store destination l (len - 1) htruncate)),
            hmutationPre.trans (statementSingleRootMutation
              (truncate_except_owner s1.store destination l (len - 1) htruncate) hchanged)⟩
          unfold OwnerRooted
          intro howner
          rcases howner with ⟨mu, ownerElement, howner | howner⟩ <;>
            cases howner <;> simp [Ty.flat] at helementFlat
      | _ => simp [FlatTy] at hownerFlat
    | int width => simp [Ty.ownerElem?] at hownerElem
    | bool => simp [Ty.ownerElem?] at hownerElem
    | unit => simp [Ty.ownerElem?] at hownerElem
    | arr element size => simp [Ty.ownerElem?] at hownerElem
    | ref mu target => simp [Ty.ownerElem?] at hownerElem
    | slice mu element => simp [Ty.ownerElem?] at hownerElem
    | tuple elements => simp [Ty.ownerElem?] at hownerElem
    | structT id fields => simp [Ty.ownerElem?] at hownerElem

end Goose.Core.Sound
