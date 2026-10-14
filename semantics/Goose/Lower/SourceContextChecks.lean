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
    contexts := #[context], entry := 0, origins := #[⟨0, 1, "source-context"⟩] }

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
  obtain ⟨statements, typingEq, finalEq, rootsEq'⟩ := source.enter
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
  obtain ⟨source, _, _, typeEq⟩ := acceptedGlobalSource (cfg := ⟨profile, module⟩)
    (g := 0) (global := ⟨"flag", .bool, .mutable, .bool true, 0⟩)
    (state := St.initial) (by cbv) rfl (initialStoreInvariant module)
  exact ⟨source, typeEq⟩

end Goose.Lower.SourceContextChecks
