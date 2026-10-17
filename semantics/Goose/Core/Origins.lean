import Goose.Core.Syntax

namespace Goose.Core

def OriginRecordValid (nFiles : Nat) (origin : Origin) : Prop :=
  origin.file < nFiles ∧ 0 < origin.line ∧ origin.kind ∈ originKinds

def checkOriginRecord (nFiles : Nat) (origin : Origin) : Except String Unit :=
  if ¬ origin.file < nFiles then
    .error s!"file: index {origin.file} outside its table of {nFiles}"
  else if ¬ 0 < origin.line then
    .error "origin: line below 1"
  else if origin.kind ∉ originKinds then
    .error s!"origin: unknown node kind {origin.kind.quote}"
  else .ok ()

theorem checkOriginRecord_iff (nFiles : Nat) (origin : Origin) :
    checkOriginRecord nFiles origin = .ok () ↔ OriginRecordValid nFiles origin := by
  by_cases file : origin.file < nFiles <;>
    by_cases line : 0 < origin.line <;>
    by_cases kind : origin.kind ∈ originKinds <;>
    simp [checkOriginRecord, OriginRecordValid, file, line, kind]

end Goose.Core
