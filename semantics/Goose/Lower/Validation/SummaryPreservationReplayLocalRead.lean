import Goose.Lower.Validation.SummaryPreservationReplayLocalReadOrigins

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.Core.Sound Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem localRead {env : PEnv} {variableId : VarId} {localVar : LocalVar}
    {before after : RState} {sourceRoots : List RootRef}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (checked : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variableRow : env.impl.vars[variableId]? = some localVar)
    (source : rpExpr env (.read (.var variableId)) before = .ok (sourceRoots, after))
    (slotBound : variableId < le.slots.size)
    (slotRoots : RootsRefine func (rootsAt slots variableId) (env.ann variableId |>.getD []))
    (scalarType : ls.cur.isSome = true → localVar.ty.isRefLike = false →
      valRefLike vt (ls.vals.size + 1) = false) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerExpr (.read (.var variableId)) le ls).2 next ∧
      ((lowerExpr (.read (.var variableId)) le ls).2.cur.isSome = true →
        ReplayValue func next (lowerExpr (.read (.var variableId)) le ls).2
          (lowerExpr (.read (.var variableId)) le ls).1 sourceRoots (.data localVar.ty) ∧
        rootsAt next.vals (lowerExpr (.read (.var variableId)) le ls).1 =
          if valRefLike vt (lowerExpr (.read (.var variableId)) le ls).1 then rootsAt slots variableId else []) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, completed, value, retained, _⟩ := ready.localReadWithOrigins
    checked variableRow source slotBound slotRoots scalarType
  exact ⟨next, completed, value, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
