import DuistermaatVanDerKallen
import Lean.Util.CollectAxioms

/-! Audit by defining module, including private and generated declarations.
Namespace filtering alone could miss a declaration outside the expected namespace. -/

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    if (`DuistermaatVanDerKallen).isPrefixOf moduleName then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      match info with
      | .axiomInfo _ => throwError "Project axiom: {name}"
      | _ => pure ()
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
        unless used.contains ax do
          used := used.push ax
  logInfo m!"Axiom audit passed: {declarations} project declarations, {theorems} theorem declarations (including generated)."
  logInfo m!"Transitive axioms used: {used.qsort Name.lt}"
