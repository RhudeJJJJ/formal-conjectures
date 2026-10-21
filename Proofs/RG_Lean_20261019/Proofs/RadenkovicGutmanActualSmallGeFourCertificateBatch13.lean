/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase221
import Proofs.RadenkovicGutmanActualSmallGeFourCase222
import Proofs.RadenkovicGutmanActualSmallGeFourCase223
import Proofs.RadenkovicGutmanActualSmallGeFourCase224
import Proofs.RadenkovicGutmanActualSmallGeFourCase225
import Proofs.RadenkovicGutmanActualSmallGeFourCase226
import Proofs.RadenkovicGutmanActualSmallGeFourCase227
import Proofs.RadenkovicGutmanActualSmallGeFourCase228
import Proofs.RadenkovicGutmanActualSmallGeFourCase229
import Proofs.RadenkovicGutmanActualSmallGeFourCase230
import Proofs.RadenkovicGutmanActualSmallGeFourCase231
import Proofs.RadenkovicGutmanActualSmallGeFourCase232
import Proofs.RadenkovicGutmanActualSmallGeFourCase233
import Proofs.RadenkovicGutmanActualSmallGeFourCase234
import Proofs.RadenkovicGutmanActualSmallGeFourCase235
import Proofs.RadenkovicGutmanActualSmallGeFourCase236
import Proofs.RadenkovicGutmanActualSmallGeFourCase237
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys13 : ∀ k ∈ keys13, Certified k := by
  apply certified_cons (by exact certified221)
  apply certified_cons (by exact certified222)
  apply certified_cons (by exact certified223)
  apply certified_cons (by exact certified224)
  apply certified_cons (by exact certified225)
  apply certified_cons (by exact certified226)
  apply certified_cons (by exact certified227)
  apply certified_cons (by exact certified228)
  apply certified_cons (by exact certified229)
  apply certified_cons (by exact certified230)
  apply certified_cons (by exact certified231)
  apply certified_cons (by exact certified232)
  apply certified_cons (by exact certified233)
  apply certified_cons (by exact certified234)
  apply certified_cons (by exact certified235)
  apply certified_cons (by exact certified236)
  apply certified_cons (by exact certified237)
  simp
#print axioms certified_keys13
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
