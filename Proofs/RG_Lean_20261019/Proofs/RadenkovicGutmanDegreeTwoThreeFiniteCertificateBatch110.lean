/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5500
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5501
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5502
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5503
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5504
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5505
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5506
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase5507
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys110 : ∀ k ∈ keys110, Certified k := by
  apply certified_cons (by exact certified5500)
  apply certified_cons (by exact certified5501)
  apply certified_cons (by exact certified5502)
  apply certified_cons (by exact certified5503)
  apply certified_cons (by exact certified5504)
  apply certified_cons (by exact certified5505)
  apply certified_cons (by exact certified5505swap)
  apply certified_cons (by exact certified5506)
  apply certified_cons (by exact certified5506swap)
  apply certified_cons (by exact certified5507)
  apply certified_cons (by exact certified5507swap)
  simp
#print axioms certified_keys110
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
