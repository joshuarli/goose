import paranoid_roots

open Lean Elab Command GooseParanoidAudit

axiom unapproved : True

theorem directGood : True := True.intro
opaque hiddenGood : True := True.intro
theorem throughOpaque : True := hiddenGood
theorem throughAxiom : True := unapproved
opaque hiddenBad : True := unapproved
theorem throughOpaqueAxiom : True := hiddenBad

#guard_msgs(drop warning) in
theorem throughSorry : True := by sorry

theorem throughRecursor (b : Bool) : b = b := by cases b <;> rfl

def expectFailure (messagePrefix : String) (action : IO α) : IO Unit := do
  try
    discard action
    throw (IO.userError "expected rejection")
  catch error =>
    unless messagePrefix.isPrefixOf error.toString do throw error

run_cmd do
  let env ← getEnv
  let names ← liftIO <| validateProofs env #[``directGood, ``throughOpaque, ``throughRecursor]
  liftIO <| verifyCoverage names names
  for name in [``True, ``True.intro, ``hiddenGood, ``Bool, ``Bool.rec, ``Bool.true, ``Bool.false] do
    unless names.contains name do throwError "omitted dependency {name}"
  for name in [``throughAxiom, ``throughSorry] do
    liftIO <| expectFailure "disallowed axiom:" (validateProofs env #[name])
  liftIO <| expectFailure "disallowed axiom: unapproved" (validateProofs env #[``throughOpaqueAxiom])
  liftIO <| expectFailure "missing dependency:" (collect env #[`nonexistentDependency])
  liftIO <| expectFailure "missing exported dependency:" (verifyCoverage names {})

def parseControl (text : String) : IO NameSet :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr text
    handle.flush
    exportedNames path

run_cmd do
  let names ← liftIO <| parseControl "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"escaped.dot\"}}\n{\"def\":{\"name\":1}}\n"
  unless names.contains (.str .anonymous "escaped.dot") do
    throwError "split a single exported name component"
  liftIO <| expectFailure "missing declaration name index:"
    (parseControl "{\"def\":{\"name\":1}}\n")
  liftIO <| expectFailure "missing name index:"
    (parseControl "{\"in\":1,\"str\":{\"pre\":2,\"str\":\"missingParent\"}}\n")
