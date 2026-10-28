import FormalConjectures.WrittenOnTheWallII.GraphConjecture72
import Proofs.WOWII72.Full
import Lean.Util.CollectAxioms

/-! # Original WOWII72 source-reading and transitive-axiom audit

The full certificate negates the original assertion at every nontrivial finite order.
The admitted original is used only to check its type.
-/

open Lean Meta Elab Command in
run_elab do
  let certificate := `WOWII72.full_conjecture72
  let original := `WrittenOnTheWallII.GraphConjecture72.conjecture72
  let certType ← inferType (mkConst certificate)
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let size := mkApp2 (mkConst ``Nat.add) n (mkNatLit 2)
    let vertex := mkApp (mkConst ``Fin) size
    let fi ← synthInstance (← mkAppM ``Fintype #[vertex])
    let de ← synthInstance (← mkAppM ``DecidableEq #[vertex])
    let nt ← synthInstance (← mkAppM ``Nontrivial #[vertex])
    let originalInstance := mkAppN (mkConst original [Level.zero]) #[vertex,fi,de,nt]
    let originalType ← mkForallFVars #[n] (← inferType originalInstance)
    let originalNegation ← mkAppM ``Not #[originalType]
    unless ← isDefEq originalNegation certType do
      throwError "The certified proposition changes the original source reading"
    logInfo "SOURCE READING: exact negation of the original predicate on every Fin(n+2)"
  if ← isDefEq certType (mkConst ``False) then
    throwError "Changed proposition accepted"
  logInfo "NEGATIVE CONTROL: changed proposition rejected"

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``WOWII72.full_conjecture72, ``WOWII72.tree_upper,
      ``WOWII72.average_lower, ``WOWII72.small_obstruction] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {name}: {ax}"
    Lean.logInfo m!"AXIOMS {name}: {axioms}"

#print axioms WrittenOnTheWallII.GraphConjecture72.conjecture72
