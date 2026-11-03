/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell017Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell017Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell017Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell017Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell017Log

/-!
# Acceptance of cell 017 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells08.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell017_checked : accepts 1 3 4 cell017=true := by
  apply decide_eq_true
  exact ⟨cell017_parameters_checked.1, cell017_parameters_checked.2,
    cell017_arithmetic_checked, cell017_affine_checked,
    cell017_positive_checked, cell017_log_checked⟩
#print axioms cell017_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
