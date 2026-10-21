/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase187
import Proofs.RadenkovicGutmanActualSmallGeFourCase188
import Proofs.RadenkovicGutmanActualSmallGeFourCase189
import Proofs.RadenkovicGutmanActualSmallGeFourCase190
import Proofs.RadenkovicGutmanActualSmallGeFourCase191
import Proofs.RadenkovicGutmanActualSmallGeFourCase192
import Proofs.RadenkovicGutmanActualSmallGeFourCase193
import Proofs.RadenkovicGutmanActualSmallGeFourCase194
import Proofs.RadenkovicGutmanActualSmallGeFourCase195
import Proofs.RadenkovicGutmanActualSmallGeFourCase196
import Proofs.RadenkovicGutmanActualSmallGeFourCase197
import Proofs.RadenkovicGutmanActualSmallGeFourCase198
import Proofs.RadenkovicGutmanActualSmallGeFourCase199
import Proofs.RadenkovicGutmanActualSmallGeFourCase200
import Proofs.RadenkovicGutmanActualSmallGeFourCase201
import Proofs.RadenkovicGutmanActualSmallGeFourCase202
import Proofs.RadenkovicGutmanActualSmallGeFourCase203
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys11 : ∀ k ∈ keys11, Certified k := by
  apply certified_cons (by exact certified187)
  apply certified_cons (by exact certified188)
  apply certified_cons (by exact certified189)
  apply certified_cons (by exact certified190)
  apply certified_cons (by exact certified191)
  apply certified_cons (by exact certified192)
  apply certified_cons (by exact certified193)
  apply certified_cons (by exact certified194)
  apply certified_cons (by exact certified195)
  apply certified_cons (by exact certified196)
  apply certified_cons (by exact certified197)
  apply certified_cons (by exact certified198)
  apply certified_cons (by exact certified199)
  apply certified_cons (by exact certified200)
  apply certified_cons (by exact certified201)
  apply certified_cons (by exact certified202)
  apply certified_cons (by exact certified203)
  simp
#print axioms certified_keys11
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
