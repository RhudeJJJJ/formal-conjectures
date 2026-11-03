/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell013Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell013Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell013Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell013Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell013Log

/-!
# Acceptance of cell 013 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells06.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell013_checked : accepts 1 3 4 cell013=true := by
  apply decide_eq_true
  exact ⟨cell013_parameters_checked.1, cell013_parameters_checked.2,
    cell013_arithmetic_checked, cell013_affine_checked,
    cell013_positive_checked, cell013_log_checked⟩
#print axioms cell013_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
