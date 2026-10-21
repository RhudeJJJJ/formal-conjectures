/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase204
import Proofs.RadenkovicGutmanActualSmallGeFourCase205
import Proofs.RadenkovicGutmanActualSmallGeFourCase206
import Proofs.RadenkovicGutmanActualSmallGeFourCase207
import Proofs.RadenkovicGutmanActualSmallGeFourCase208
import Proofs.RadenkovicGutmanActualSmallGeFourCase209
import Proofs.RadenkovicGutmanActualSmallGeFourCase210
import Proofs.RadenkovicGutmanActualSmallGeFourCase211
import Proofs.RadenkovicGutmanActualSmallGeFourCase212
import Proofs.RadenkovicGutmanActualSmallGeFourCase213
import Proofs.RadenkovicGutmanActualSmallGeFourCase214
import Proofs.RadenkovicGutmanActualSmallGeFourCase215
import Proofs.RadenkovicGutmanActualSmallGeFourCase216
import Proofs.RadenkovicGutmanActualSmallGeFourCase217
import Proofs.RadenkovicGutmanActualSmallGeFourCase218
import Proofs.RadenkovicGutmanActualSmallGeFourCase219
import Proofs.RadenkovicGutmanActualSmallGeFourCase220
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys12 : ∀ k ∈ keys12, Certified k := by
  apply certified_cons (by exact certified204)
  apply certified_cons (by exact certified205)
  apply certified_cons (by exact certified206)
  apply certified_cons (by exact certified207)
  apply certified_cons (by exact certified208)
  apply certified_cons (by exact certified209)
  apply certified_cons (by exact certified210)
  apply certified_cons (by exact certified211)
  apply certified_cons (by exact certified212)
  apply certified_cons (by exact certified213)
  apply certified_cons (by exact certified214)
  apply certified_cons (by exact certified215)
  apply certified_cons (by exact certified216)
  apply certified_cons (by exact certified217)
  apply certified_cons (by exact certified218)
  apply certified_cons (by exact certified219)
  apply certified_cons (by exact certified220)
  simp
#print axioms certified_keys12
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
