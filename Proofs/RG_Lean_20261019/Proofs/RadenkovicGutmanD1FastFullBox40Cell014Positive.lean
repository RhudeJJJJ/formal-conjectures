/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Data

/-!
# Polynomial positivity for cell 014

The original affine polynomial passes the Bernstein positivity check at the recorded degrees.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells07.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell014_positive_checked : NestedHorner.positiveCheck 3 cell014.degrees cell014.affine=true := by decide +kernel
#print axioms cell014_positive_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
