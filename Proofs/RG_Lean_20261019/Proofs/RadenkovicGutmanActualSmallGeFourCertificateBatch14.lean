/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase238
import Proofs.RadenkovicGutmanActualSmallGeFourCase239
import Proofs.RadenkovicGutmanActualSmallGeFourCase240
import Proofs.RadenkovicGutmanActualSmallGeFourCase241
import Proofs.RadenkovicGutmanActualSmallGeFourCase242
import Proofs.RadenkovicGutmanActualSmallGeFourCase243
import Proofs.RadenkovicGutmanActualSmallGeFourCase244
import Proofs.RadenkovicGutmanActualSmallGeFourCase245
import Proofs.RadenkovicGutmanActualSmallGeFourCase246
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys14 : ∀ k ∈ keys14, Certified k := by
  apply certified_cons (by exact certified238)
  apply certified_cons (by exact certified239)
  apply certified_cons (by exact certified240)
  apply certified_cons (by exact certified241)
  apply certified_cons (by exact certified242)
  apply certified_cons (by exact certified243)
  apply certified_cons (by exact certified244)
  apply certified_cons (by exact certified245)
  apply certified_cons (by exact certified246)
  simp
#print axioms certified_keys14
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
