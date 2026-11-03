/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell016Data

/-!
# Positive parameters for cell 016

The Young parameter and every width of the original parameter box are positive.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells08.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell016_parameters_checked : 0 < cell016.young ∧ (∀ i, 0 < cell016.width i) := by decide +kernel
#print axioms cell016_parameters_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
