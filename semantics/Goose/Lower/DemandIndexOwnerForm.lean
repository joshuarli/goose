import Goose.Lower.DemandIndexAssignmentStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

inductive IndexOwnerPlace : Place → Prop
  | scalar {place : Place} (form : ScalarReadPlace place) : IndexOwnerPlace place
  | field {place : Place} (index : Nat) (form : ScalarReadPlace place) : IndexOwnerPlace (.field place index)

theorem IndexOwnerPlace.indexed {owner : Place} (form : IndexOwnerPlace owner) (index : Expr) (origin : OriginId) :
    IndexedScalarPlace (.elem (.of owner) index origin) := by
  cases form with
  | scalar scalar => exact .element index origin scalar
  | field field scalar => exact .fieldElement field index origin scalar

theorem PlaceSource.index_owner_view_alias {cfg : Cfg} {env : Env} {owner : Place} {index : Expr}
    {origin : OriginId} {state : St} (source : PlaceSource cfg env (.elem (.of owner) index origin) state)
    (form : IndexOwnerPlace owner) :
    ∃ aliases, source.rootsEnv.access.aliasView (source.path ++ [0]) (.of owner) = .ok aliases := by
  cases form with
  | scalar scalar => exact source.index_scalar_view_alias scalar
  | field field scalar =>
    obtain ⟨_, view, typing, roots, canonical, _⟩ := source.elemChildren origin
    have element := tyView_accessElement (view.frame.mod_t.trans view.frame.mod_p.symm)
      (view.frame.vars_t.trans view.frame.vars_p.symm) view.typed
    rw [roots] at element
    cases scalar with
    | global global =>
      refine ⟨[⟨.slice .readOnly view.element, [.global global], .operand (source.path ++ [0])⟩], ?_⟩
      simp only [AccessEnv.aliasView, element, AccessEnv.viewRoots, AccessEnv.placeRoots, bind, pure]
      rfl
    | slot slot =>
      refine ⟨[⟨.slice .readOnly view.element, [.local slot], .operand (source.path ++ [0])⟩], ?_⟩
      simp only [AccessEnv.aliasView, element, AccessEnv.viewRoots, AccessEnv.placeRoots, bind, pure]
      rfl


#print axioms IndexOwnerPlace.indexed
#print axioms PlaceSource.index_owner_view_alias
end Goose.Lower
