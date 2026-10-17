import Goose.Lower.Validation.SummaryPreservationReturnLedger

namespace Goose.Lower.Validation.SummaryPreservation.BuilderReturnsBound

open Goose.Core Goose.GIR

variable {before after : LS} {oldUpper newUpper : Prov} {target : List RootRef}
  {le : LEnv} {scopeCount : Nat}

theorem bound {env : TEnv} {bound : Bound} {start finish : Nat} {value : Bnd}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyBound env bound start = .ok ((), finish))
    (run : lowerBound bound le before = (value, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained
    (returnFrame_lowerBound bound (tyBound_returnFree bound source) le before value after run)

theorem plain_statement {env output : TEnv} {statement : Stmt} {scope start finish : Nat}
    (loop : Option LoopCtx)
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyStmt env scope statement start = .ok (output, finish))
    (plain : statement.isPlain = true)
    (run : lowerStmt loop statement le before = ((), after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained
    (returnFrame_lowerStmt loop statement (tyStmt_returnFree_of_plain_or_inExpr statement source (Or.inr plain))
      le before () after run)

theorem expression_block {env : TEnv} {body : Core.Block} {preTypes : List (VarId × Ty)}
    {preValues : List (SlotId × ValueId × OriginId)} {type : Ty} {start finish : Nat} {value : ValueId}
    (loop : Option LoopCtx) (want : Bool)
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyBlock env preTypes body start = .ok (type, finish))
    (inside : env.inExpr = true)
    (run : lowerBlock loop preValues want body le before = (value, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained
    (returnFrame_lowerBlock loop preValues want body (tyBlock_returnFree body preTypes source inside)
      le before value after run)

theorem printed_arguments {env : TEnv} {args : List PrintArg} {start finish : Nat} {parts : List PrintPart}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (source : Core.tyPrintArgs env args start = .ok ((), finish))
    (run : lowerPrintArgs args le before = (parts, after))
    (retained : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index) :
    BuilderReturnsBound newUpper target after :=
  prior.frame symbols size retained
    (returnFrame_lowerPrintArgs args (tyPrintArgs_returnFree args source) le before parts after run)

#print axioms bound
#print axioms plain_statement
#print axioms expression_block
#print axioms printed_arguments

end Goose.Lower.Validation.SummaryPreservation.BuilderReturnsBound
