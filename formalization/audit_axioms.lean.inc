
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if auditModules.contains env.header.moduleNames[idx.toNat]! then
        declarations := declarations + 1
        if info.isTheorem then
          theorems := theorems + 1
        let axioms ← collectAxioms name
        let rejected := axioms.filter (fun ax ↦ !allowed.contains ax)
        unless rejected.isEmpty do
          throwError "Unapproved axioms in {name}: {rejected}"
  if declarations == 0 then
    throwError "No local declarations were audited"
  logInfo m!"Axiom audit passed: {declarations} declarations, including {theorems} theorems, across {auditModules.size} modules."
