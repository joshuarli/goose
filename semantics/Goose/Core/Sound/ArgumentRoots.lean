import Goose.Core.Sound.AccessReplay

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

private theorem forInUnit_member {α : Type} (xs : List α)
    (f : α → V (ForInStep PUnit.{1}))
    (yielded : ∀ a step, f a = .ok step → step = .yield ⟨⟩)
    (checked : forIn (m := V) xs (PUnit.unit : PUnit.{1}) (fun a _ => f a) = .ok PUnit.unit) :
    ∀ a, a ∈ xs → f a = .ok (.yield ⟨⟩) := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, head, tail⟩ := (ex_bind_ok _ _ _).1 checked
    have equal := yielded a step head
    subst step
    intro b member
    rcases List.mem_cons.1 member with rfl | member
    · exact head
    · exact ih tail b member

private theorem zip_rightMember {α β : Type} (left : List α) (right : List β)
    (lengths : left.length = right.length) {b : β} (member : b ∈ right) :
    ∃ a, (a, b) ∈ left.zip right := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := List.length_eq_zero_iff.1 lengths.symm
    simp [empty] at member
  | cons a left ih =>
    cases right with
    | nil => simp at lengths
    | cons c right =>
      rcases List.mem_cons.1 member with rfl | member
      · exact ⟨a, by simp⟩
      · obtain ⟨a', pair⟩ := ih right (by simpa using lengths) member
        exact ⟨a', by simp [pair]⟩

theorem checkResultShape_rootDeclaration {m : Module} {impl : Impl} {ctx : Context}
    (checked : checkResultShape m impl ctx = .ok ())
    {q : RootRef} (member : q ∈ ctx.resultRoots.flatten) :
    match q with
    | .global g => ∃ gl, m.globals[g]? = some gl
    | .local _ => False
    | .param _ => True := by
  unfold checkResultShape at checked
  inv at checked
  obtain ⟨lengths, loop⟩ := checked
  obtain ⟨rs, sets, rootMember⟩ := List.mem_flatten.1 member
  obtain ⟨t, pair⟩ := zip_rightMember impl.results.toList ctx.resultRoots
    (by simpa using lengths.symm) sets
  have row := forInUnit_member (impl.results.toList.zip ctx.resultRoots) _ (by
    intro pair step success
    rcases pair with ⟨t, rs⟩
    dsimp only at success
    split at success
    · inv at success
    · simp only [ex_bind_ok, ex_pure_ok] at success
      obtain ⟨_, _, equal⟩ := success
      exact equal) loop (t, rs) pair
  dsimp only at row
  split at row
  · inv at row
  · simp only [ex_bind_ok, ex_pure_ok] at row
    obtain ⟨loopUnit, roots, _⟩ := row
    cases loopUnit
    have root := forInUnit_member rs _ (by
      intro root step success
      cases root with
      | «local» _ => dsimp only at success; inv at success
      | global g =>
        dsimp only at success
        split at success <;> inv at success
        exact success
      | param j =>
        dsimp only at success
        split at success
        · split at success <;> inv at success
          exact success
        · inv at success) roots q rootMember
    cases q with
    | «local» _ => dsimp only at root; inv at root
    | param _ => trivial
    | global g =>
      dsimp only at root
      split at root
      · rename_i bound
        exact ⟨m.globals[g], Array.getElem?_eq_getElem bound⟩
      · inv at root

theorem checkContentShape_rootDeclaration {m : Module} {impl : Impl} {ctx : Context}
    (checked : checkContentShape m impl ctx = .ok ())
    {x : Nat} {rs : List RootRef}
    (annotation : (ctx.contentRoots.find? (·.1 == x)).map (·.2) = some rs)
    {q : RootRef} (member : q ∈ rs) :
    match q with
    | .global g => ∃ gl, m.globals[g]? = some gl
    | .local _ => False
    | .param _ => True := by
  unfold checkContentShape at checked
  cases found : ctx.contentRoots.find? (·.1 == x) with
  | none => simp [found] at annotation
  | some pair =>
    have pairMember := List.mem_of_find?_eq_some found
    obtain ⟨y, roots⟩ := pair
    have index : y = x := by simpa using List.find?_some found
    subst y
    have same : roots = rs := by simpa [found] using annotation
    subst roots
    have row := (forAll_ok _ _).1 checked (x, rs) pairMember
    dsimp only at row
    inv at row
    obtain ⟨_, row⟩ := row
    cases hvar : impl.vars[x]? with
    | none => simp only [hvar] at row; inv at row
    | some lv =>
      simp only [hvar] at row
      inv at row
      obtain ⟨_, _, loop⟩ := row
      have root := (forAll_ok _ _).1 loop q member
      cases q with
      | «local» _ => dsimp only at root; inv at root
      | param _ => trivial
      | global g =>
        dsimp only at root
        inv at root
        exact ⟨m.globals[g], Array.getElem?_eq_getElem root⟩

theorem checkAnnotationShape_rootDeclaration {m : Module} {impl : Impl} {ctx : Context}
    (checked : checkAnnotationShape m impl ctx = .ok ())
    {x : Nat} {rs : List RootRef}
    (annotation : (ctx.varRoots.find? (·.1 == x)).map (·.2) = some rs)
    {q : RootRef} (member : q ∈ rs) :
    match q with
    | .global g => ∃ gl, m.globals[g]? = some gl
    | .local y => ∃ lv, impl.vars[y]? = some lv ∧ lv.ty.isRefLike = false
    | .param _ => True := by
  unfold checkAnnotationShape at checked
  simp only [ex_bind_ok] at checked
  obtain ⟨loopUnit, firstLoop, _⟩ := checked
  cases loopUnit
  cases found : ctx.varRoots.find? (·.1 == x) with
  | none => simp [found] at annotation
  | some pair =>
    have pairMember := List.mem_of_find?_eq_some found
    obtain ⟨y, roots⟩ := pair
    have index : y = x := by simpa using List.find?_some found
    subst y
    have same : roots = rs := by simpa [found] using annotation
    subst roots
    have row := forInUnit_member ctx.varRoots _ (by
      intro pair step success
      rcases pair with ⟨y, roots⟩
      dsimp only at success
      split at success
      · inv at success
      · split at success
        · simp only [ex_bind_ok, ex_pure_ok] at success
          obtain ⟨_, _, equal⟩ := success
          exact equal
        · inv at success) firstLoop (x, rs) pairMember
    dsimp only at row
    cases hvar : impl.vars[x]? with
    | none => simp only [hvar] at row; inv at row
    | some lv =>
      simp only [hvar] at row
      split at row
      · simp only [ex_bind_ok, ex_pure_ok] at row
        obtain ⟨loopUnit, loop, _⟩ := row
        cases loopUnit
        have root := forInUnit_member rs _ (by
          intro root step success
          cases root with
          | «local» y =>
            dsimp only at success
            split at success
            · inv at success
            · split at success <;> inv at success
              exact success
          | global g =>
            dsimp only at success
            split at success <;> inv at success
            exact success
          | param i =>
            dsimp only at success
            split at success <;> inv at success
            exact success) loop q member
        cases q with
        | «local» y =>
          dsimp only at root
          cases localVar : impl.vars[y]? with
          | none => simp only [localVar] at root; inv at root
          | some ly =>
            simp only [localVar] at root
            split at root
            · inv at root
            · rename_i nonref
              exact ⟨ly, localVar, by simpa using nonref⟩
        | global g =>
          dsimp only at root
          split at root
          · rename_i bound
            exact ⟨m.globals[g], Array.getElem?_eq_getElem bound⟩
          · inv at root
        | param _ => trivial
      · inv at row

/-- Argument roots name declared globals. A reference holder in an open caller
scope must still be visible so its binding can classify its stored value. -/
def ArgumentRootDeclarations (m : Module) (tenv : TEnv) (env : Env)
    (ars : List (List RootRef)) : Prop :=
  ∀ (i : Nat) (q : RootRef), q ∈ ars[i]?.getD [] → match q with
    | .global g => ∃ gl, m.globals[g]? = some gl
    | .local x => ∀ lv si, env.vars[x]? = some lv →
        env.scopes.lookup lv.scope = some si → lv.ty.isRefLike = true → x ∈ tenv.visible
    | .param _ => True

theorem ArgumentRootDeclarations.included
    {m : Module} {tenv : TEnv} {env : Env} {actual expected : List (List RootRef)}
    (declarations : ArgumentRootDeclarations m tenv env expected)
    (included : RootListsIncluded actual expected) :
    ArgumentRootDeclarations m tenv env actual := by
  intro i q member
  cases ha : actual[i]? with
  | none => simp [ha] at member
  | some roots =>
    obtain ⟨expectedRoots, he, subset⟩ := included i roots ha
    exact declarations i q (by simpa [he] using subset q (by simpa [ha] using member))

/-- Existing non-reference storage is observed by declaration type; visible
reference holders are classified from the frame's stored binding. -/
theorem Frame.classifiedArgumentRoots
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {ars : List (List RootRef)}
    {oldObs newObs : Observation} {newD : RootInst → Ty → Prop}
    (frame : Frame m W tenv penv env s future)
    (declarations : ArgumentRootDeclarations m tenv env ars)
    (inherited : ClassifiedParameters m W.P W.D oldObs s.store)
    (roots : ∀ r T, oldObs.roots r T → newObs.roots r T)
    (storage : ∀ r T, StorageRootTypes env r T → s.store.roots[r]? ≠ none →
      newObs.roots r T)
    (slices : ∀ r E, W.D r E → newD r E) :
    ClassifiedParameters m (fun i r => Gam env W.P (ars[i]?.getD []) r)
      newD newObs s.store := by
  intro i r parameter
  obtain ⟨q, member, denotes⟩ := parameter
  cases q with
  | global g =>
    change r = .global g at denotes
    subst r
    exact declarations i _ member
  | param j =>
    exact (inherited.mono (fun _ _ h => h) roots slices) j r denotes
  | «local» x =>
    obtain ⟨lv, si, hvar, hscope, rfl⟩ := denotes
    cases href : lv.ty.isRefLike with
    | false =>
      cases present : s.store.roots[RootInst.local env.act si x]? with
      | none => exact Or.inr (Or.inr (Or.inr present))
      | some v =>
        exact Or.inl ⟨lv.ty, storage _ _
          ⟨x, lv, si, hvar, hscope, rfl, href, rfl⟩ (by simp [present])⟩
    | true =>
      have visible := declarations i _ member lv si hvar hscope href
      obtain ⟨lv', si', v, hvar', hscope', _, present, reference⟩ :=
        frame.bindings x visible
      have sameVar : lv' = lv := Option.some.inj (hvar'.symm.trans hvar)
      subst lv'
      have sameScope : si' = si := Option.some.inj (hscope'.symm.trans hscope)
      subst si'
      exact Or.inr (Or.inr (Or.inl ⟨v, present, reference href⟩))

end Goose.Core.Sound
