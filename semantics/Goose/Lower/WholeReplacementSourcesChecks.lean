import Goose.Lower.WholeReplacementSources

namespace Goose.Lower.WholeReplacementSourcesChecks

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

def ownerType (growOnly : Bool) : Ty :=
  if growOnly then .grow .bool else .growshrink .bool

def replacement (growOnly : Bool) : Expr :=
  .arrLit (ownerType growOnly) [.bool true]

def statement (growOnly : Bool) : Stmt :=
  .assignWhole (.global 0) (replacement growOnly) 0

def implementation (growOnly : Bool) : Impl :=
  { initImpl with body := .mk 0 [statement growOnly] none }

def module (growOnly : Bool) : Module :=
  { files := #["whole-replacement-source.goose"], types := #[],
    globals := #[⟨"owner", ownerType growOnly, .mutable,
      .arrLit (ownerType growOnly) [.bool false], 0⟩],
    impls := #[implementation growOnly], contexts := #[initContext], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def before : St :=
  { St.initial with store := Store.empty.introduce (.global 0) (.resizable .bool #[.bool false]), nextAct := 1 }

def cleared : St :=
  { before with store := { roots := (before.store.roots.erase (.global 0)).insert (.global 0) (.resizable .bool #[]) }, nextAct := 2, nextScope := 1 }


#guard [true, false].all fun growOnly =>
  match Core.validate (module growOnly) with
  | .ok _ => true
  | .error _ => false

theorem actual_clear_source (profile : NumProfile) (growOnly : Bool)
    (accepted : Core.validate (module growOnly) = .ok ()) :
    ∃ child : ExprSource ⟨profile, module growOnly⟩ ⟨#[], 1, [(0, 0)], 1⟩
      (replacement growOnly) cleared, child.ty = ownerType growOnly := by
  have globalsDone : initGlobals 4 ⟨profile, module growOnly⟩ [0] St.initial =
      .ok () before := by cases growOnly <;> cbv
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, body, _, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, module growOnly⟩) accepted 4 globalsDone
  have contextEq : ctx = initContext := by simpa [module] using contextAt.symm
  subst ctx
  have implEq : impl = implementation growOnly := by
    simpa [module, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, _, _, _, _⟩ := body.enter
  obtain ⟨source, _, _, _⟩ := statements.split
  obtain ⟨destination, _, _, _, _, children⟩ := source.assignWholeChildren
  obtain ⟨child, _, _, _, _, typeEq, _⟩ :=
    children 1 ⟨.global 0, []⟩ _ cleared.store (by cbv)
      (by cases growOnly <;> cbv)
  refine ⟨child, typeEq.trans ?_⟩
  have typed := destination.typed
  simp only [tyPlace] at typed
  split at typed
  · rw [destination.frame.mod_t] at typed
    change Except.ok ((⟨ownerType growOnly, true, true⟩ : PlaceInfo), destination.typingStart) =
      Except.ok (⟨destination.ty, destination.mutable, destination.contents⟩,
        destination.typingEnd) at typed
    exact (congrArg (fun value : PlaceInfo × Nat => value.1.ty) (Except.ok.inj typed)).symm
  · inv at typed

def ownerEmpty : Expr := .cmp .eq (.len (.of (.global 0))) (.lit .i64 0)

def dependentModule (growOnly : Bool) : Module :=
  { module growOnly with impls := #[{ implementation growOnly with body := .mk 0 [.assignWhole (.global 0) (.arrLit (ownerType growOnly) [ownerEmpty]) 0] none }] }

#guard [true, false].all fun growOnly =>
  match Core.validate (dependentModule growOnly) with
  | .error ⟨.whole, _⟩ => true
  | _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  [true, false].all fun growOnly =>
    match evalExpr 8 ⟨profile, module growOnly⟩ ⟨#[], 1, [(0, 0)], 1⟩ ownerEmpty before,
        evalExpr 8 ⟨profile, module growOnly⟩ ⟨#[], 1, [(0, 0)], 1⟩ ownerEmpty cleared with
    | .ok (.bool false) _, .ok (.bool true) _ => true
    | _, _ => false

end Goose.Lower.WholeReplacementSourcesChecks
