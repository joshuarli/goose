import Goose.Lower.SourceContexts

namespace Goose.Lower.SourceContextChecks

open Goose.Core Goose.Core.Sound Goose.Proofs.Memory

def body : Block := .mk 0
  [.letS 0 (.ref .mutable (.global 0)) 0, .expr (.read (.var 0)) 0] none

def implementation : Impl :=
  { initImpl with name := "main", vars := #[⟨"alias", .ref .readOnly .bool, .immutable, 0, 0⟩], body := body }

def context : Context := { initContext with varRoots := [(0, [.global 0])] }

def module : Module :=
  { files := #["source-context.goose"], types := #[],
    globals := #[⟨"flag", .bool, .mutable, .bool true, 0⟩], impls := #[implementation],
    contexts := #[context], entry := 0, origins := #[⟨0, 1, "expr"⟩] }

#guard match Core.validate module with | .ok _ => true | .error _ => false

#guard Ty.passableTo (.ref .mutable .bool) (.ref .readOnly .bool)
#guard !Ty.passableTo (.ref .readOnly .bool) (.ref .mutable .bool)

def initialState : St :=
  { St.initial with store := Store.empty.introduce (.global 0) (.bool true) }

example : Core.validate module = .ok () := by cbv

theorem initialInvariant : StoreInv module module.globals.size initialState := by
  constructor
  · intro r v present demanded
    simp only [initialState, get_introduce] at present
    split at present
    · cases present
      trivial
    · simp [St.initial, Store.empty] at present
  · intro r v present target pointed
    simp only [initialState, get_introduce] at present
    split at present
    · cases present
      cases pointed
    · simp [St.initial, Store.empty] at present
  · intro act scope x present
    simp [initialState, St.initial, get_introduce, Store.empty] at present
  · intro g global bounded present
    have gEq : g = 0 := by change g < 1 at bounded; omega
    subst g
    have glEq : global = ⟨"flag", .bool, .mutable, .bool true, 0⟩ := by
      simpa [module] using present.symm
    subst global
    refine ⟨.bool true, ?_, ?_⟩
    · cbv
    · trivial
  · intro g v present
    simp only [initialState, get_introduce] at present
    split at present
    · cases present
      simp [IsRef]
    · simp [St.initial, Store.empty] at present
  · intro g v present
    simp only [initialState, get_introduce] at present
    split at present
    · rename_i same
      have gEq : g = 0 := by simpa using same.symm
      subst g
      exact Or.inl (by decide)
    · simp [St.initial, Store.empty] at present

theorem entrySource (profile : NumProfile) :
    ∃ source : BlockSource ⟨profile, module⟩ ⟨implementation.vars, 0, [], 1⟩ [] body
        { initialState with nextAct := 1 },
      source.rootsEnv = ⟨module, implementation, context, []⟩ := by
  obtain ⟨ctx, impl, contextAt, implementationAt, noParameters, noResults,
    source, typingEq, rootsEq⟩ := acceptedEntrySource (cfg := ⟨profile, module⟩)
      (by cbv) initialInvariant
  have contextEq : ctx = context := by simpa [module] using contextAt.symm
  subst ctx
  have implementationEq : impl = implementation := by
    simpa [module, context, initContext] using implementationAt.symm
  subst impl
  exact ⟨source, rootsEq⟩

def enteredEnv : Env := ⟨implementation.vars, 0, [(0, 0)], 1⟩

def enteredState : St := { initialState with nextAct := 1, nextScope := 1 }

def declaredState : St :=
  { enteredState with store := enteredState.store.introduce (.local 0 0 0) (.ref ⟨.global 0, []⟩) }

theorem initialStatements (profile : NumProfile) :
    ∃ statements : StmtsSource ⟨profile, module⟩ enteredEnv body.stmts enteredState,
      statements.rootsEnv = ⟨module, implementation, context, [0]⟩ := by
  obtain ⟨source, rootsEq⟩ := entrySource profile
  obtain ⟨statements, typingEq, finalEq, rootsEq', _⟩ := source.enter
  exact ⟨statements, by rw [rootsEq', rootsEq]; rfl⟩

theorem secondStatementSource (profile : NumProfile) :
    ∃ tail : StmtsSource ⟨profile, module⟩ enteredEnv [.expr (.read (.var 0)) 0] declaredState,
      0 ∈ tail.typingEnv.visible ∧
      tail.rootsEnv = ⟨module, implementation, context, [0]⟩ := by
  obtain ⟨statements, rootsEq⟩ := initialStatements profile
  obtain ⟨head, typingEq, headRootsEq, next⟩ := statements.split
  have firstDone : execStmt 4 ⟨profile, module⟩ enteredEnv (.letS 0 (.ref .mutable (.global 0)) 0)
      enteredState = .ok (.normal .unit) declaredState := by cbv
  obtain ⟨tail, tailTypingEq, tailRootsEq, tailFinalEq⟩ := next 4 .unit declaredState firstDone
  have visible : 0 ∈ head.typingAfter.visible := by
    have typed := head.typed
    simp only [tyStmt] at typed
    inv at typed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, afterEq, _⟩ := typed
    rw [afterEq]
    exact List.mem_cons_self
  refine ⟨tail, ?_, tailRootsEq.trans rootsEq⟩
  rw [tailTypingEq]
  exact visible

example (profile : NumProfile) :
    ∃ tail : StmtsSource ⟨profile, module⟩ enteredEnv [.expr (.read (.var 0)) 0] declaredState,
      Core.Sound.Frame module tail.world tail.typingEnv tail.rootsEnv enteredEnv declaredState
        (blockSuffixFuture tail.context tail.offset) ∧
      0 ∈ tail.typingEnv.visible ∧
      declaredState.store.roots[RootInst.local 0 0 0]? = some (.ref ⟨.global 0, []⟩) := by
  obtain ⟨tail, visible, rootsEq⟩ := secondStatementSource profile
  exact ⟨tail, tail.frame, visible, by cbv⟩

example (profile : NumProfile) :
    ∃ tail : StmtsSource ⟨profile, module⟩ enteredEnv [.expr (.read (.var 0)) 0] declaredState,
      StmtsResult tail (.normal .unit) declaredState := by
  obtain ⟨tail, _, _⟩ := secondStatementSource profile
  refine ⟨tail, tail.result 5 (.normal .unit) ?_⟩
  cbv

example (profile : NumProfile) :
    ∃ source : ExprSource ⟨profile, module⟩ noEnv (.bool true) St.initial,
      source.ty = .bool := by
  obtain ⟨source, _, _, typeEq, _⟩ := acceptedGlobalSource (cfg := ⟨profile, module⟩)
    (g := 0) (global := ⟨"flag", .bool, .mutable, .bool true, 0⟩)
    (state := St.initial) (by cbv) rfl (initialStoreInvariant module) 0
  exact ⟨source, typeEq⟩

def callee : Impl :=
  { initImpl with name := "value", results := #[.bool], body := .mk 0 [.print [.text "global"] 0] (some (.bool true)), summary := .known ⟨[], [], [], [], [], false, true⟩ }

def entryImplementation : Impl :=
  { initImpl with name := "main", vars := #[⟨"entry-local", .bool, .immutable, 0, 0⟩], body := .mk 0 [.letS 0 (.bool false) 0] none }

def calleeContext : Context := ⟨1, "value", [], [[]], []⟩

def callModule (artifact : ArtifactProfile) : Module :=
  { files := #["call-boundary.goose"], types := #[],
    globals := #[⟨"flag", .bool, .mutable, .call 1 [] 0, 0⟩],
    impls := #[entryImplementation, callee], contexts := #[initContext, calleeContext], entry := 0,
    origins := #[⟨0, 1, "global"⟩], profile := artifact }

#guard match Core.validate (callModule .pilot) with | .ok _ => true | .error _ => false
#guard match Core.validate (callModule .shrink) with | .ok _ => true | .error _ => false

theorem calleeFromInitializer (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (callModule artifact) = .ok ()) :
    ∃ body : BlockSource ⟨profile, callModule artifact⟩ ⟨callee.vars, 0, [], 1⟩ [] callee.body
        { St.initial with nextAct := 1 },
      body.typingEnv = { implEnv (callModule artifact) callee with visible := [] } ∧
      body.rootsEnv = ⟨callModule artifact, callee, calleeContext, []⟩ := by
  obtain ⟨source, typingEq, rootsEq, typeEq, _⟩ := acceptedGlobalSource
    (cfg := ⟨profile, callModule artifact⟩) (state := St.initial) (g := 0)
    (global := ⟨"flag", .bool, .mutable, .call 1 [] 0, 0⟩) accepted rfl
    (initialStoreInvariant (callModule artifact)) 0
  obtain ⟨ctx, impl, contextAt, implementationAt, body, typingEq, rootsEq⟩ :=
    source.calleeAfterArgs 1 [] rfl
  have contextEq : ctx = calleeContext := by simpa [callModule] using contextAt.symm
  subst ctx
  have implEq : impl = callee := by simpa [callModule, calleeContext] using implementationAt.symm
  subst impl
  exact ⟨body, typingEq, rootsEq⟩

example (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (callModule artifact) = .ok ()) :
    ∃ body : BlockSource ⟨profile, callModule artifact⟩ ⟨callee.vars, 0, [], 1⟩ [] callee.body
        { St.initial with nextAct := 1 },
      BlockResult body (.normal (.bool true)) { St.initial with nextAct := 1, nextScope := 1, trace := "global\n" } := by
  obtain ⟨body, _, _⟩ := calleeFromInitializer artifact profile accepted
  refine ⟨body, body.result 4 (.normal (.bool true)) ?_⟩
  cbv

example (profile : NumProfile) :
    ∃ body : BlockSource ⟨profile, callModule .pilot⟩ ⟨callee.vars, 0, [], 1⟩ [] callee.body
        { St.initial with nextAct := 1 },
      body.rootsEnv = ⟨callModule .pilot, callee, calleeContext, []⟩ := by
  obtain ⟨body, _, rootsEq⟩ := calleeFromInitializer .pilot profile (by cbv)
  exact ⟨body, rootsEq⟩

def afterEffectfulGlobals : St :=
  { store := Store.empty.introduce (.global 0) (.bool true), trace := "global\n", nextAct := 2, nextScope := 1 }

theorem globalsDone (profile : NumProfile) :
    initGlobals 8 ⟨profile, callModule .pilot⟩ [0] St.initial = .ok () afterEffectfulGlobals := by
  cbv

example (profile : NumProfile) :
    InitializedGlobals (callModule .pilot) 1 afterEffectfulGlobals :=
  initializedGlobals_of_success (cfg := ⟨profile, callModule .pilot⟩) (by cbv) 8 (globalsDone profile)

theorem entryAfterEffectfulGlobals (profile : NumProfile) :
    ∃ source : BlockSource ⟨profile, callModule .pilot⟩ ⟨entryImplementation.vars, 2, [], 1⟩ []
        entryImplementation.body { afterEffectfulGlobals with nextAct := 3 },
      source.rootsEnv = ⟨callModule .pilot, entryImplementation, initContext, []⟩ := by
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, source, _, rootsEq⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, callModule .pilot⟩) (by cbv) 8 (globalsDone profile)
  have contextEq : ctx = initContext := by simpa [callModule] using contextAt.symm
  subst ctx
  have implEq : impl = entryImplementation := by simpa [callModule, initContext] using implementationAt.symm
  subst impl
  exact ⟨source, rootsEq⟩

example (profile : NumProfile) :
    ∃ statements : StmtsSource ⟨profile, callModule .pilot⟩
        ⟨entryImplementation.vars, 2, [(0, 1)], 1⟩ [.letS 0 (.bool false) 0]
        { afterEffectfulGlobals with nextAct := 3, nextScope := 2 },
      statements.rootsEnv = ⟨callModule .pilot, entryImplementation, initContext, [0]⟩ := by
  obtain ⟨source, rootsEq⟩ := entryAfterEffectfulGlobals profile
  obtain ⟨statements, _, _, statementRoots, _⟩ := source.enter
  exact ⟨statements, by rw [statementRoots, rootsEq]; rfl⟩

example (profile : NumProfile) :
    ∃ child : ExprSource ⟨profile, module⟩ enteredEnv (.ref .mutable (.global 0)) enteredState,
      ExprResult child (.ref ⟨.global 0, []⟩) enteredState ∧
      HasTy module child.world.G enteredState.store (.ref ⟨.global 0, []⟩) (.ref .readOnly .bool) := by
  obtain ⟨statements, _⟩ := initialStatements profile
  obtain ⟨head, _, _, _⟩ := statements.split
  obtain ⟨child, declaration, variableAt, _, _, passable⟩ := head.letChild
  have declarationEq : declaration = ⟨"alias", .ref .readOnly .bool, .immutable, 0, 0⟩ := by
    simpa [enteredEnv, implementation] using variableAt.symm
  subst declaration
  have result := child.result 2 (.ref ⟨.global 0, []⟩) (by cbv)
  exact ⟨child, result, result.value_passable passable⟩

def returnImplementation : Impl :=
  { callee with body := .mk 0 [.ret (some (.bool true)) 0] none, summary := .known ⟨[], [], [], [], [], false, false⟩ }

def returnModule : Module :=
  { callModule .pilot with impls := #[entryImplementation, returnImplementation] }

example (profile : NumProfile) :
    ∃ child : ExprSource ⟨profile, returnModule⟩ ⟨#[], 1, [(0, 0)], 1⟩ (.bool true)
        { St.initial with nextAct := 2, nextScope := 1 },
      child.typingEnv.impl = some returnImplementation ∧ child.ty.passableTo .bool = true := by
  obtain ⟨caller, _, _, _, _⟩ := acceptedGlobalActivation (cfg := ⟨profile, returnModule⟩)
    (state := St.initial) (g := 0) (global := ⟨"flag", .bool, .mutable, .call 1 [] 0, 0⟩)
    (by cbv) rfl (initialStoreInvariant returnModule)
  obtain ⟨ctx, impl, contextAt, implementationAt, body, bodyTyping, bodyRoots⟩ := caller.calleeAfterArgs 1 [] rfl
  have contextEq : ctx = calleeContext := by simpa [returnModule, callModule] using contextAt.symm
  subst ctx
  have implEq : impl = returnImplementation := by
    simpa [returnModule, callModule, calleeContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, statementsTyping, _, _, _⟩ := body.enter
  obtain ⟨head, headTyping, _, _⟩ := statements.split
  obtain ⟨child, implementation, target, implementationAt, resultType, childTyping, _, passable⟩ := head.retChild
  have typedImplementation : child.typingEnv.impl = some returnImplementation := by
    rw [childTyping, headTyping, statementsTyping]
    have same := body.same.impl
    rw [bodyTyping] at same
    exact same
  have implementationEq : implementation = returnImplementation := by
    have same := implementationAt
    rw [← childTyping, typedImplementation] at same
    exact Option.some.inj same.symm
  subst implementation
  have targetEq : target = .bool := by simpa [returnImplementation, callee] using resultType.symm
  subst target
  exact ⟨child, typedImplementation, passable⟩

def conditionalImplementation : Impl :=
  { initImpl with body := .mk 0 [.ifS (.bool true) (.mk 1 [] none) none 0] none }

def conditionalModule : Module :=
  { (callModule .pilot) with globals := #[], impls := #[conditionalImplementation], contexts := #[initContext], origins := #[⟨0, 1, "expr"⟩] }

#guard match Core.validate conditionalModule with | .ok _ => true | .error _ => false

example (profile : NumProfile) :
    ∃ child : BlockSource ⟨profile, conditionalModule⟩ ⟨#[], 0, [(0, 0)], 1⟩ [] (.mk 1 [] none)
      { St.initial with nextAct := 1, nextScope := 1 },
      child.typingEnv.impl = some conditionalImplementation := by
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, source, bodyTyping, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, conditionalModule⟩) (by cbv) 1 (by cbv)
  have contextEq : ctx = initContext := by simpa [conditionalModule, callModule] using contextAt.symm
  subst ctx
  have implEq : impl = conditionalImplementation := by simpa [conditionalModule, callModule, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, statementsTyping, _, _, _⟩ := source.enter
  obtain ⟨head, headTyping, _, _⟩ := statements.split
  obtain ⟨child, childTyping, _, _, _⟩ := head.ifThenChild 1 (by cbv)
  refine ⟨child, ?_⟩
  rw [childTyping, headTyping, statementsTyping]
  have same := source.same.impl
  rw [bodyTyping] at same
  exact same

def loopImplementation : Impl :=
  { initImpl with body := .mk 0 [.while (.bool true) (.mk 1 [] none) 0] none }

def loopModule : Module :=
  { conditionalModule with impls := #[loopImplementation] }

#guard match Core.validate loopModule with | .ok _ => true | .error _ => false

example (profile : NumProfile) :
    ∃ next : StmtSource ⟨profile, loopModule⟩ ⟨#[], 0, [(0, 0)], 1⟩
      (.while (.bool true) (.mk 1 [] none) 0) { St.initial with nextAct := 1, nextScope := 2 },
      next.typingEnv.impl = some loopImplementation := by
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, source, bodyTyping, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, loopModule⟩) (by cbv) 1 (by cbv)
  have contextEq : ctx = initContext := by simpa [loopModule, conditionalModule, callModule] using contextAt.symm
  subst ctx
  have implEq : impl = loopImplementation := by simpa [loopModule, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, statementsTyping, _, _, _⟩ := source.enter
  obtain ⟨head, headTyping, _, _⟩ := statements.split
  obtain ⟨next, nextTyping, _, _, _⟩ := head.whileAfterBody 1 2 (.normal .unit) (by cbv) (by cbv) (Or.inl ⟨.unit, rfl⟩)
  refine ⟨next, ?_⟩
  rw [nextTyping, headTyping, statementsTyping]
  have same := source.same.impl
  rw [bodyTyping] at same
  exact same

def assertImplementation : Impl :=
  { initImpl with body := .mk 0 [.assertS (.bool true) 0] none }

def assertModule : Module :=
  { conditionalModule with impls := #[assertImplementation] }

#guard match Core.validate assertModule with | .ok _ => true | .error _ => false

example (profile : NumProfile) :
    ∃ child : ExprSource ⟨profile, assertModule⟩ ⟨#[], 0, [(0, 0)], 1⟩ (.bool true)
      { St.initial with nextAct := 1, nextScope := 1 }, child.ty = .bool := by
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, source, _, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, assertModule⟩) (by cbv) 1 (by cbv)
  have contextEq : ctx = initContext := by simpa [assertModule, conditionalModule, callModule] using contextAt.symm
  subst ctx
  have implEq : impl = assertImplementation := by simpa [assertModule, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, _, _, _, _⟩ := source.enter
  obtain ⟨head, _, _, _⟩ := statements.split
  obtain ⟨child, _, _, typeEq⟩ := head.assertChild
  exact ⟨child, typeEq⟩

def exitImplementation : Impl :=
  { initImpl with body := .mk 0 [.exit (.lit .i32 0) 0] none }

def exitModule : Module :=
  { conditionalModule with impls := #[exitImplementation] }

#guard match Core.validate exitModule with | .ok _ => true | .error _ => false

example (profile : NumProfile) :
    ∃ child : ExprSource ⟨profile, exitModule⟩ ⟨#[], 0, [(0, 0)], 1⟩ (.lit .i32 0)
      { St.initial with nextAct := 1, nextScope := 1 }, child.ty = (.int .i32) := by
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, source, _, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, exitModule⟩) (by cbv) 1 (by cbv)
  have contextEq : ctx = initContext := by simpa [exitModule, conditionalModule, callModule] using contextAt.symm
  subst ctx
  have implEq : impl = exitImplementation := by simpa [exitModule, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, _, _, _, _⟩ := source.enter
  obtain ⟨head, _, _, _⟩ := statements.split
  obtain ⟨child, integer, _, _, typeEq⟩ := head.exitChild
  have integerEq : integer = .i32 := by
    have typed := child.typed
    change Except.ok (.int .i32, child.typingStart) = Except.ok (child.ty, child.typingEnd) at typed
    have typeKnown : child.ty = .int .i32 := (congrArg Prod.fst (Except.ok.inj typed)).symm
    exact Ty.int.inj (typeEq.symm.trans typeKnown)
  subst integer
  exact ⟨child, typeEq⟩

def assignmentImplementation : Impl :=
  { initImpl with body := .mk 0 [.assign (.global 0) (.bool false) 0] none }

def assignmentModule : Module :=
  { (callModule .pilot) with impls := #[assignmentImplementation, callee] }

#guard match Core.validate assignmentModule with | .ok _ => true | .error _ => false

example (profile : NumProfile) :
    ∃ destination : PlaceSource ⟨profile, assignmentModule⟩ ⟨#[], 2, [(0, 1)], 1⟩ (.global 0)
      { afterEffectfulGlobals with nextAct := 3, nextScope := 2 },
      ∃ child : ExprSource ⟨profile, assignmentModule⟩ ⟨#[], 2, [(0, 1)], 1⟩ (.bool false)
        { afterEffectfulGlobals with nextAct := 3, nextScope := 2 },
        child.ty = destination.ty ∧ child.ty = .bool := by
  have globalDone : initGlobals 8 ⟨profile, assignmentModule⟩ [0] St.initial = .ok () afterEffectfulGlobals := by cbv
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, source, _, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, assignmentModule⟩) (by cbv) 8 globalDone
  have contextEq : ctx = initContext := by simpa [assignmentModule, callModule] using contextAt.symm
  subst ctx
  have implEq : impl = assignmentImplementation := by simpa [assignmentModule, callModule, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, _, _, _, _⟩ := source.enter
  obtain ⟨head, _, _, _⟩ := statements.split
  obtain ⟨destination, _, _, _, _, children⟩ := head.assignChildren
  obtain ⟨child, _, _, _, _, typeEq⟩ := children 1 ⟨.global 0, []⟩ _ (by cbv)
  refine ⟨destination, child, typeEq, ?_⟩
  have typed := child.typed
  change Except.ok (.bool, child.typingStart) = Except.ok (child.ty, child.typingEnd) at typed
  exact (congrArg Prod.fst (Except.ok.inj typed)).symm

def ownerImplementation (statement : Stmt) : Impl :=
  { initImpl with body := .mk 0 [statement] none }

def ownerModule (statement : Stmt) : Module :=
  { files := #["owner-source.goose"], types := #[],
    globals := #[⟨"owner", .growshrink .bool, .mutable, .arrLit (.growshrink .bool) [.bool true], 0⟩],
    impls := #[ownerImplementation statement], contexts := #[initContext], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def afterOwnerGlobals : St :=
  { St.initial with store := Store.empty.introduce (.global 0) (.resizable .bool #[.bool true]), nextAct := 1 }

#guard match Core.validate (ownerModule (.clear (.global 0) 0)) with | .ok _ => true | .error _ => false
#guard match Core.validate (ownerModule (.popN (.global 0) (.lit .i32 1) 0)) with | .ok _ => true | .error _ => false

private theorem ownerStatement (profile : NumProfile) (statement : Stmt)
    (accepted : Core.validate (ownerModule statement) = .ok ()) :
    ∃ source : StmtSource ⟨profile, ownerModule statement⟩ ⟨#[], 1, [(0, 0)], 1⟩ statement
      { afterOwnerGlobals with nextAct := 2, nextScope := 1 }, True := by
  have globalsDone : initGlobals 4 ⟨profile, ownerModule statement⟩ [0] St.initial = .ok () afterOwnerGlobals := by cbv
  obtain ⟨ctx, impl, contextAt, implementationAt, _, _, body, _, _⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, ownerModule statement⟩) accepted 4 globalsDone
  have contextEq : ctx = initContext := by simpa [ownerModule] using contextAt.symm
  subst ctx
  have implEq : impl = ownerImplementation statement := by simpa [ownerModule, initContext] using implementationAt.symm
  subst impl
  obtain ⟨statements, _, _, _, _⟩ := body.enter
  obtain ⟨head, _, _, _⟩ := statements.split
  exact ⟨head, trivial⟩

example (profile : NumProfile)
    (accepted : Core.validate (ownerModule (.clear (.global 0) 0)) = .ok ()) :
    ∃ child : PlaceSource ⟨profile, ownerModule (.clear (.global 0) 0)⟩ ⟨#[], 1, [(0, 0)], 1⟩ (.global 0)
      { afterOwnerGlobals with nextAct := 2, nextScope := 1 }, child.contents = true := by
  obtain ⟨source, _⟩ := ownerStatement profile (.clear (.global 0) 0) accepted
  obtain ⟨child, element, _, _, _, _, _, contents⟩ := source.clearChild
  exact ⟨child, contents⟩

example (profile : NumProfile)
    (accepted : Core.validate (ownerModule (.popN (.global 0) (.lit .i32 1) 0)) = .ok ()) :
    ∃ child : ExprSource ⟨profile, ownerModule (.popN (.global 0) (.lit .i32 1) 0)⟩ ⟨#[], 1, [(0, 0)], 1⟩ (.lit .i32 1)
      { afterOwnerGlobals with nextAct := 2, nextScope := 1 }, ∃ integer, child.ty = .int integer := by
  obtain ⟨source, _⟩ := ownerStatement profile (.popN (.global 0) (.lit .i32 1) 0) accepted
  obtain ⟨destination, element, _, _, _, _, _, _, children⟩ := source.popNChildren
  obtain ⟨child, integer, _, _, _, _, typeEq⟩ := children 1 ⟨.global 0, []⟩ _ (by cbv)
  exact ⟨child, integer, typeEq⟩

end Goose.Lower.SourceContextChecks
