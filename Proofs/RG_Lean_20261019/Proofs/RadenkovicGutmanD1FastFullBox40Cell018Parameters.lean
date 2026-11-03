/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell018Data

/-!
# Positive parameters for cell 018

The Young parameter and every width of the original parameter box are positive.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells09.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell018_parameters_checked : 0 < cell018.young ∧ (∀ i, 0 < cell018.width i) := by decide +kernel
#print axioms cell018_parameters_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
