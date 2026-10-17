module

import Challenge
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let roots := #[``Challenge.audit_main1, ``Challenge.audit_main2,
    ``Challenge.audit_main_extended]
  let mut pending := #[]
  for n in roots do
    pending := pending ++ (env.find? n).get!.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n || !(Name.mkSimple "Challenge").isPrefixOf n then
      continue
    seen := seen.insert n
    if let some info := env.find? n then
      pending := pending ++ info.type.getUsedConstants
      if let .inductInfo ind := info then
        pending := pending ++ ind.ctors.toArray
      if let some v := info.value? (allowOpaque := true) then
        pending := pending ++ v.getUsedConstants
  for n in seen.toArray.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"NEEDED {n}"
