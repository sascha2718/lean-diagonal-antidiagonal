module

import Solution
import Lean

open Lean Elab Command

/-! Internal audit of the completed library and solution only. No Challenge import:
the three deliberate statement holes must not be confused with completed proofs. -/
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if ["BoxLike", "Challenge", "Solution"].any (fun s => (Name.mkSimple s).isPrefixOf name) then
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          throwError "Forbidden axiom {ax} in completed declaration {name}"
      count := count + 1
  unless (env.find? ``Challenge.audit_main1).isSome &&
      (env.find? ``Challenge.audit_main2).isSome &&
      (env.find? ``Challenge.audit_main_extended).isSome do
    throwError "A completed headline is missing"
  logInfo m!"Completed-declaration axiom audit passed for {count} constants."
