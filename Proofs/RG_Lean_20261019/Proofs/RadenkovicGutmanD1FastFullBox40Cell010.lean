/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell010Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell010Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell010Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell010Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell010Log

/-!
# Acceptance of cell 010 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells05.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell010_checked : accepts 1 3 4 cell010=true := by
  apply decide_eq_true
  exact ⟨cell010_parameters_checked.1, cell010_parameters_checked.2,
    cell010_arithmetic_checked, cell010_affine_checked,
    cell010_positive_checked, cell010_log_checked⟩
#print axioms cell010_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
