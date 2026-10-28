import Goose.Proofs.ConstructionAcceptedScalarParameterEffects
import Goose.Proofs.ConstructionAcceptedArgumentTargets

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem paramGlobals_noParameter (callee : Impl) (context : Context) (argument id : Nat) :
    .param id ∉ paramGlobals callee context argument := by
  unfold paramGlobals
  split <;> simp_all
  intro _ root member
  cases root <;> simp

theorem mapCallTargets_noParameter (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (targets : List Target) (clear : ∀ roots, roots ∈ arguments → ∀ id, .param id ∉ rootsTargets roots) :
    ∀ id, .param id ∉ mapCallTargets callee context arguments targets := by
  induction targets with
  | nil => simp [mapCallTargets]
  | cons target rest ih =>
    intro id member
    cases target with
    | global global =>
      simp only [mapCallTargets, List.mem_cons] at member
      rcases member with same | later
      · cases same
      · exact ih id later
    | param parameter =>
      simp only [mapCallTargets, List.mem_append] at member
      rcases member with (rootsMember | globalMember) | later
      · cases found : arguments[parameter]? with
        | none => simp [found, rootsTargets] at rootsMember
        | some roots =>
          have belongs : roots ∈ arguments := List.mem_of_getElem? found
          exact clear roots belongs id (by simpa [found] using rootsMember)
      · exact paramGlobals_noParameter callee context parameter id globalMember
      · exact ih id later

theorem callEffects_noParameter (callee : Impl) (context : Context) (arguments : List (List RootRef))
    (summary : Summary) (before : Eff) (known : callee.summary = .known summary)
    (clear : NoParameterAccess before)
    (argumentsClear : ∀ roots, roots ∈ arguments → ∀ id, .param id ∉ rootsTargets roots) :
    NoParameterAccess (callEffects callee context arguments before) := by
  intro id member
  simp only [callEffects, known, Eff.accessTargets, List.mem_append, callEffects_addTargets_members] at member
  have reads := mapCallTargets_noParameter callee context arguments summary.reads argumentsClear id
  have writes := mapCallTargets_noParameter callee context arguments summary.writes argumentsClear id
  have grows := mapCallTargets_noParameter callee context arguments summary.grows argumentsClear id
  have shrinks := mapCallTargets_noParameter callee context arguments summary.shrinks argumentsClear id
  rcases member with (((read | readNew) | (write | writeNew)) | (grow | growNew)) | (shrink | shrinkNew)
  · exact clear id (by simp [Eff.accessTargets, read])
  · exact reads readNew
  · exact clear id (by simp [Eff.accessTargets, write])
  · exact writes writeNew
  · exact clear id (by simp [Eff.accessTargets, grow])
  · exact grows growNew
  · exact clear id (by simp [Eff.accessTargets, shrink])
  · exact shrinks shrinkNew

theorem scalarLocal_argument_roots (source : PEnv) (id : Nat) (descriptor : LocalVar)
    (before after : RState) (roots : List RootRef)
    (declared : source.impl.vars[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (rooted : rpExpr source (.read (.var id)) before = .ok (roots, after)) : roots = [] := by
  have refLike : descriptor.ty.isRefLike = false := by
    rcases scalar with ⟨integer, same⟩ | same <;> simp [same, Ty.isRefLike]
  unfold rpExpr rpPlace readRoots at rooted
  simp [declared, refLike, bind, StateT.bind, pure, StateT.pure, Except.pure] at rooted
  repeat' first
    | split at rooted
    | simp_all [Except.bind]
  all_goals simp_all

#print axioms scalarLocal_argument_roots
#print axioms callEffects_noParameter
#print axioms paramGlobals_noParameter
#print axioms mapCallTargets_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
