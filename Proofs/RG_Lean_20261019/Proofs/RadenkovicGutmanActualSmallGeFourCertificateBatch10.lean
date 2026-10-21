/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase170
import Proofs.RadenkovicGutmanActualSmallGeFourCase171
import Proofs.RadenkovicGutmanActualSmallGeFourCase172
import Proofs.RadenkovicGutmanActualSmallGeFourCase173
import Proofs.RadenkovicGutmanActualSmallGeFourCase174
import Proofs.RadenkovicGutmanActualSmallGeFourCase175
import Proofs.RadenkovicGutmanActualSmallGeFourCase176
import Proofs.RadenkovicGutmanActualSmallGeFourCase177
import Proofs.RadenkovicGutmanActualSmallGeFourCase178
import Proofs.RadenkovicGutmanActualSmallGeFourCase179
import Proofs.RadenkovicGutmanActualSmallGeFourCase180
import Proofs.RadenkovicGutmanActualSmallGeFourCase181
import Proofs.RadenkovicGutmanActualSmallGeFourCase182
import Proofs.RadenkovicGutmanActualSmallGeFourCase183
import Proofs.RadenkovicGutmanActualSmallGeFourCase184
import Proofs.RadenkovicGutmanActualSmallGeFourCase185
import Proofs.RadenkovicGutmanActualSmallGeFourCase186
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys10 : ∀ k ∈ keys10, Certified k := by
  apply certified_cons (by exact certified170)
  apply certified_cons (by exact certified171)
  apply certified_cons (by exact certified172)
  apply certified_cons (by exact certified173)
  apply certified_cons (by exact certified174)
  apply certified_cons (by exact certified175)
  apply certified_cons (by exact certified176)
  apply certified_cons (by exact certified177)
  apply certified_cons (by exact certified178)
  apply certified_cons (by exact certified179)
  apply certified_cons (by exact certified180)
  apply certified_cons (by exact certified181)
  apply certified_cons (by exact certified182)
  apply certified_cons (by exact certified183)
  apply certified_cons (by exact certified184)
  apply certified_cons (by exact certified185)
  apply certified_cons (by exact certified186)
  simp
#print axioms certified_keys10
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
