/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1FastFullBox40Cell011Data

/-!
# Logarithm bound for cell 011

The original square lower bound and payment satisfy the rational logarithm certificate.

Source: [original cell data and acceptance theorem](https://github.com/RhudeJJJJ/formal-conjectures/blob/acfbe187a3d062fccb3da255c8532b8152789d4b/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1FastFullBox40Cells05.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
open FastNestedCellData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cell011_log_checked : RationalLog.accepts cell011.squareLower cell011.payment cell011.logarithmK cell011.logarithmN=true := by decide +kernel
#print axioms cell011_log_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass40
