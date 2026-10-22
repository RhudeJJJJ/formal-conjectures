/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase1200
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase1201
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase1202
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneMiddleResidualFiniteActualCases
theorem certified_keys024 : ∀ k ∈ keys024, Certified k := by
  apply certified_cons (by exact certified1200)
  apply certified_cons (by exact certified1201)
  apply certified_cons (by exact certified1202)
  simp
#print axioms certified_keys024
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
