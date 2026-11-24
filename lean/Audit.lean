import Paper

/-!
# Axiom audit

Every declaration of `GraphStability`, `RhombicFamily`, and `Paper`, including
private and compiler-generated declarations, is checked for its axiom
dependencies. The build fails if any declaration uses `sorry` or any axiom
other than `propext`, `Classical.choice`, and `Quot.sound`.
-/

open Lean

/-- The modules audited: the two libraries and the restatement of the paper. -/
private def isAudited (module : Name) : Bool :=
  [`GraphStability, `RhombicFamily, `Paper].any (·.isPrefixOf module)

/-- The only axioms a declaration of this package may depend on. -/
private def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array Name)) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if isAudited env.header.moduleNames[idx.toNat]! then names.push name else names
    | none => names
  if names.isEmpty then
    throwError "axiom audit: no declarations found"
  let collect : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, result) := (collect.run env).run {}
  for ax in result.axioms do
    unless allowedAxioms.contains ax do
      throwError "axiom audit: unexpected axiom {ax}"
  logInfo m!"axiom audit: {names.size} declarations; axioms used: {result.axioms}"
