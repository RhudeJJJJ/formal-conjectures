/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell009Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell009Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell009Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell009Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell009Log

/-!
# Acceptance of cell 009 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/4ab5802ec7da33fcb4a54633e2e7c9863c974244/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells04.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell009_checked : accepts 1 3 4 cell009=true := by
  apply decide_eq_true
  exact ⟨cell009_parameters_checked.1, cell009_parameters_checked.2,
    cell009_arithmetic_checked, cell009_affine_checked,
    cell009_positive_checked, cell009_log_checked⟩
#print axioms cell009_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
