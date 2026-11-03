/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell016Data

/-!
# Polynomial identity for cell 016

The stored polynomial agrees with the degree-one reciprocal gap program for arm classes 3 and 4.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells08.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell016_arithmetic_checked : NestedArithmetic.accepts (program 1 3 4 cell016) cell016.poly=true := by decide +kernel
#print axioms cell016_arithmetic_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
