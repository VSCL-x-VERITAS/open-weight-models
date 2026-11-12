import HDP
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[`HDP.Basic, `HDP.LimitTheorems, `HDP.Moments, `HDP.PoissonLimit, `HDP.Tails]
  let indices := mods.filterMap env.getModuleIdx?
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if (env.getModuleIdxFor? name).any (fun i => indices.contains i) then
      count := count + 1
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .axiomInfo _ => "AXIOM"
        | .opaqueInfo _ => "OPAQUE"
        | _ => "other"
      let privateName := name.isInternal
      logInfo m!"AUDIT_CONSTANT {name} KIND={kind} INTERNAL={privateName}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "forbidden axiom {ax} in {name}"
      match ci with
      | .axiomInfo _ => throwError "custom local axiom {name}"
      | .opaqueInfo _ => throwError "opaque local declaration {name} requires investigation"
      | .defnInfo v => if v.safety != .safe then throwError "unsafe or partial declaration {name}"
      | _ => pure ()
      elabCommand (← `(#print axioms $(mkIdent name)))
  logInfo m!"AUDIT_TOTAL {count}"
