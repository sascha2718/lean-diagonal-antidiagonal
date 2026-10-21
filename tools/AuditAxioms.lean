module

import Solution
import Lean

open Lean Elab Command

/-! Internal audit of the completed library and solution only. No Challenge import:
the three deliberate statement holes must not be confused with completed proofs. The audit also
covers every constant of the copied library `ExactOverlaps` (`vendor/`) in this environment. -/
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let completed (name : Name) : Bool :=
    ["BoxLike", "Challenge", "Solution"].any (fun s => (Name.mkSimple s).isPrefixOf name)
  let vendored (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some idx => (`ExactOverlaps).isPrefixOf env.header.moduleNames[idx]!
    | none => false
  let mut count : Nat := 0
  let mut vendoredCount : Nat := 0
  for (name, _) in env.constants.toList do
    let isCompleted := completed name
    let isVendored := vendored name
    if isCompleted || isVendored then
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          throwError "Forbidden axiom {ax} in declaration {name}"
      if isCompleted then count := count + 1
      if isVendored then vendoredCount := vendoredCount + 1
  unless (env.find? ``Challenge.audit_main1).isSome &&
      (env.find? ``Challenge.audit_main2).isSome &&
      (env.find? ``Challenge.audit_main_extended).isSome do
    throwError "A completed headline is missing"
  logInfo m!"Completed-declaration axiom audit passed for {count} constants and for \
    {vendoredCount} constants of the copied library ExactOverlaps."
