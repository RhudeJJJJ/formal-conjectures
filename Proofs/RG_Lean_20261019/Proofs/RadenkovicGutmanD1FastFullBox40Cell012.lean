/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell012Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell012Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell012Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell012Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell012Log

/-!
# Acceptance of cell 012 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells06.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell012_checked : accepts 1 3 4 cell012=true := by
  apply decide_eq_true
  exact ⟨cell012_parameters_checked.1, cell012_parameters_checked.2,
    cell012_arithmetic_checked, cell012_affine_checked,
    cell012_positive_checked, cell012_log_checked⟩
#print axioms cell012_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
