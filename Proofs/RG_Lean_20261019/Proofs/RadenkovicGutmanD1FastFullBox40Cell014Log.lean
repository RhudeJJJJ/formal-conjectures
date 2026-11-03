/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell014Data

/-!
# Logarithm bound for cell 014

The original square lower bound and payment satisfy the rational logarithm certificate.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells07.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell014_log_checked : RationalLog.accepts cell014.squareLower cell014.payment cell014.logarithmK cell014.logarithmN=true := by decide +kernel
#print axioms cell014_log_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
