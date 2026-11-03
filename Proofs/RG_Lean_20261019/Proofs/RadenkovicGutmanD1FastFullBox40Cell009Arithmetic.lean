/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell009Data

/-!
# Polynomial identity for cell 009

The stored polynomial agrees with the degree-one reciprocal gap program for arm classes 3 and 4.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/4ab5802ec7da33fcb4a54633e2e7c9863c974244/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells04.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell009_arithmetic_checked : NestedArithmetic.accepts (program 1 3 4 cell009) cell009.poly=true := by decide +kernel
#print axioms cell009_arithmetic_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
