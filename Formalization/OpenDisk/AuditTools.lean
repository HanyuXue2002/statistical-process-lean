import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Transitive axiom audit for every declaration in the OpenDisk modules

The command inspects the imported module inventory and follows dependencies
through the kernel's axiom collector. Only Lean's three standard logical
axioms are permitted; a hidden `sorryAx` or a postulated mathematical result
causes the audit build to fail. Audit commands themselves are excluded.
-/

open Lean Elab Command

elab "#audit_open_disk_axioms" : command => do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut modules : Nat := 0
  let mut declarations : Nat := 0
  let mut allAxioms : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if (`Formalization.OpenDisk).isPrefixOf modName &&
        modName != `Formalization.OpenDisk.AuditTools && modName != `Formalization.OpenDisk.Audit then
      modules := modules + 1
      for name in env.header.moduleData[i]!.constNames do
        let axioms ← collectAxioms name
        for ax in axioms do
          if !allowed.contains ax then
            throwError "Unexpected axiom {ax} in {name} from {modName}"
          allAxioms := allAxioms.insert ax
        declarations := declarations + 1
  logInfo m!"OpenDisk kernel audit PASS: {modules} modules; {declarations} declarations; allowed axioms only: {allAxioms.toArray}"
