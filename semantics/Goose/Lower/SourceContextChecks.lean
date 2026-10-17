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

end Goose.Lower.SourceContextChecks
