import Riemann
-- The same Lean.collectAxioms used by #print axioms, also for private Names.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Riemann." || name.toString.startsWith "_private.Riemann." then
      let axs ← collectAxioms name
      let deps := String.intercalate ", " (axs.toList.map Name.toString)
      logInfo m!"'{name}' depends on axioms: [{deps}]"
