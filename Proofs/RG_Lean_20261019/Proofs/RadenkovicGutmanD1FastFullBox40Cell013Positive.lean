/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell013Data

/-!
# Polynomial positivity for cell 013

The original affine polynomial passes the Bernstein positivity check at the recorded degrees.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells06.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell013_positive_checked : NestedHorner.positiveCheck 3 cell013.degrees cell013.affine=true := by decide +kernel
#print axioms cell013_positive_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
