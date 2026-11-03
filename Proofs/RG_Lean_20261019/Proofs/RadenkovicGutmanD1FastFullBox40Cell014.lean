/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Log

/-!
# Acceptance of cell 014 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells07.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell014_checked : accepts 1 3 4 cell014=true := by
  apply decide_eq_true
  exact ⟨cell014_parameters_checked.1, cell014_parameters_checked.2,
    cell014_arithmetic_checked, cell014_affine_checked,
    cell014_positive_checked, cell014_log_checked⟩
#print axioms cell014_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
