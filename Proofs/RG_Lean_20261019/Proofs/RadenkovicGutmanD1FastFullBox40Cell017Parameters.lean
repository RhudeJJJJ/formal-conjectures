/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell017Data

/-!
# Positive parameters for cell 017

The Young parameter and every width of the original parameter box are positive.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells08.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell017_parameters_checked : 0 < cell017.young ∧ (∀ i, 0 < cell017.width i) := by decide +kernel
#print axioms cell017_parameters_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
