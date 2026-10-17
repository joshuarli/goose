import Goose.Lower.Validation.SummaryPreservationReturnFramesSource
import Goose.Lower.Validation.CfgReturnFreeTyping
import Goose.Lower.Validate

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def ReturnMembershipFrame (before after : LS) : Prop :=
  ∀ values origin, .term (.ret values origin) ∈ after.insts → .term (.ret values origin) ∈ before.insts

def ReturnFrameRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) → ReturnMembershipFrame before after

theorem ReturnFrameRun.of_absence {action : B α}
    (checked : ∀ avoid, ReturnFrames.ReturnAbsentRun (avoid := avoid) action) : ReturnFrameRun action := by
  intro env before result after run values origin member
  classical
  apply Classical.byContradiction
  intro missing
  have beforeAbsent : ReturnFrames.BuilderReturnAbsent (avoid := (values, origin)) before := by
    intro index block row instruction
    exact missing (List.mem_flatMap.mpr ⟨block, Array.mem_toList_iff.mpr (Array.mem_of_getElem? row), instruction⟩)
  have afterAbsent := checked (values, origin) env before result after run beforeAbsent
  obtain ⟨block, blockMember, instruction⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  exact afterAbsent index block row instruction

theorem ReturnMembershipFrame.refl (state : LS) : ReturnMembershipFrame state state := fun _ _ member => member

theorem ReturnMembershipFrame.trans {first middle last : LS}
    (head : ReturnMembershipFrame first middle) (tail : ReturnMembershipFrame middle last) :
    ReturnMembershipFrame first last := fun values origin member => head values origin (tail values origin member)

theorem returnFrame_lowerExpr (expression : Expr) (free : ReturnFreeExpr expression) :
    ReturnFrameRun (lowerExpr expression) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerExpr expression free)

theorem returnFrame_lowerPlace (place : Place) (free : ReturnFreePlace place) :
    ReturnFrameRun (lowerPlace place) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerPlace place free)

theorem returnFrame_lowerView (view : View) (free : ReturnFreeView view) :
    ReturnFrameRun (lowerView view) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerView view free)

theorem returnFrame_lowerEachSource (view : View) (free : ReturnFreeView view) :
    ReturnFrameRun (lowerEachSource view) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerEachSource view free)

theorem returnFrame_lowerBound (bound : Bound) (free : ReturnFreeBound bound) :
    ReturnFrameRun (lowerBound bound) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerBound bound free)

theorem returnFrame_lowerExprs (expressions : List Expr) (free : ReturnFreeExprs expressions) :
    ReturnFrameRun (lowerExprs expressions) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerExprs expressions free)

theorem returnFrame_lowerArg (argument : Arg) (free : ReturnFreeArg argument) :
    ReturnFrameRun (lowerArg argument) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerArg argument free)

theorem returnFrame_lowerArgs (arguments : List Arg) (free : ReturnFreeArgs arguments) :
    ReturnFrameRun (lowerArgs arguments) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerArgs arguments free)

theorem returnFrame_lowerBlock (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (want : Bool) (block : Core.Block) (free : ReturnFreeBlock block) :
    ReturnFrameRun (lowerBlock loop pre want block) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerBlock loop pre want block free)

theorem returnFrame_lowerStmt (loop : Option LoopCtx) (statement : Stmt) (free : ReturnFreeStmt statement) :
    ReturnFrameRun (lowerStmt loop statement) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerStmt loop statement free)

theorem returnFrame_lowerStmts (loop : Option LoopCtx) (statements : List Stmt) (free : ReturnFreeStmts statements) :
    ReturnFrameRun (lowerStmts loop statements) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerStmts loop statements free)

theorem returnFrame_lowerPrintArgs (arguments : List PrintArg) (free : ReturnFreePrintArgs arguments) :
    ReturnFrameRun (lowerPrintArgs arguments) :=
  .of_absence (fun _ => ReturnFrames.returnAbsent_lowerPrintArgs arguments free)

theorem source_expression_return_frame {env : TEnv} {expression : Expr} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env expression start = .ok (ty, finish)) : ReturnFrameRun (lowerExpr expression) :=
  returnFrame_lowerExpr expression (tyExpr_returnFree expression source)

theorem source_place_return_frame {env : TEnv} {place : Place} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env place start = .ok (info, finish)) : ReturnFrameRun (lowerPlace place) :=
  returnFrame_lowerPlace place (tyPlace_returnFree place source)

theorem source_view_return_frame {env : TEnv} {view : View} {info : Ty × Bool} {start finish : Nat}
    (source : Core.tyView env view start = .ok (info, finish)) : ReturnFrameRun (lowerView view) :=
  returnFrame_lowerView view (tyView_returnFree view source)

#print axioms returnFrame_lowerExpr
#print axioms returnFrame_lowerPlace
#print axioms returnFrame_lowerView
#print axioms returnFrame_lowerBlock
#print axioms returnFrame_lowerStmt
#print axioms source_expression_return_frame
#print axioms source_place_return_frame
#print axioms source_view_return_frame

end Goose.Lower.Validation.SummaryPreservation
