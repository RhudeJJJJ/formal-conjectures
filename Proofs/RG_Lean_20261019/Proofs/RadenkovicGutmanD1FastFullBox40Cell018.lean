/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell018Parameters
import Proofs.RadenkovicGutmanD1FastFullBox40Cell018Arithmetic
import Proofs.RadenkovicGutmanD1FastFullBox40Cell018Affine
import Proofs.RadenkovicGutmanD1FastFullBox40Cell018Positive
import Proofs.RadenkovicGutmanD1FastFullBox40Cell018Log

/-!
# Acceptance of cell 018 for degree-one full box 40

The positive parameters, polynomial identity, affine substitution, positivity and logarithm checks establish acceptance of the original cell.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells09.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell018_checked : accepts 1 3 4 cell018=true := by
  apply decide_eq_true
  exact ⟨cell018_parameters_checked.1, cell018_parameters_checked.2,
    cell018_arithmetic_checked, cell018_affine_checked,
    cell018_positive_checked, cell018_log_checked⟩
#print axioms cell018_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
