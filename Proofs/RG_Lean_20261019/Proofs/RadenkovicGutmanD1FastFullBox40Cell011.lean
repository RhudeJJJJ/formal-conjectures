/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell011Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell011Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell011Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell011Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell011Log

/-!
# Acceptance of cell 011 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells05.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell011_checked : accepts 1 3 4 cell011=true := by
  apply decide_eq_true
  exact ⟨cell011_parameters_checked.1, cell011_parameters_checked.2,
    cell011_arithmetic_checked, cell011_affine_checked,
    cell011_positive_checked, cell011_log_checked⟩
#print axioms cell011_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
