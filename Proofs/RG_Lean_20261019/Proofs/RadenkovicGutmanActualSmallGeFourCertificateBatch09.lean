/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase153
import Proofs.RadenkovicGutmanActualSmallGeFourCase154
import Proofs.RadenkovicGutmanActualSmallGeFourCase155
import Proofs.RadenkovicGutmanActualSmallGeFourCase156
import Proofs.RadenkovicGutmanActualSmallGeFourCase157
import Proofs.RadenkovicGutmanActualSmallGeFourCase158
import Proofs.RadenkovicGutmanActualSmallGeFourCase159
import Proofs.RadenkovicGutmanActualSmallGeFourCase160
import Proofs.RadenkovicGutmanActualSmallGeFourCase161
import Proofs.RadenkovicGutmanActualSmallGeFourCase162
import Proofs.RadenkovicGutmanActualSmallGeFourCase163
import Proofs.RadenkovicGutmanActualSmallGeFourCase164
import Proofs.RadenkovicGutmanActualSmallGeFourCase165
import Proofs.RadenkovicGutmanActualSmallGeFourCase166
import Proofs.RadenkovicGutmanActualSmallGeFourCase167
import Proofs.RadenkovicGutmanActualSmallGeFourCase168
import Proofs.RadenkovicGutmanActualSmallGeFourCase169
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys09 : ∀ k ∈ keys09, Certified k := by
  apply certified_cons (by exact certified153)
  apply certified_cons (by exact certified153swap)
  apply certified_cons (by exact certified154)
  apply certified_cons (by exact certified155)
  apply certified_cons (by exact certified155swap)
  apply certified_cons (by exact certified156)
  apply certified_cons (by exact certified157)
  apply certified_cons (by exact certified157swap)
  apply certified_cons (by exact certified158)
  apply certified_cons (by exact certified159)
  apply certified_cons (by exact certified159swap)
  apply certified_cons (by exact certified160)
  apply certified_cons (by exact certified161)
  apply certified_cons (by exact certified161swap)
  apply certified_cons (by exact certified162)
  apply certified_cons (by exact certified163)
  apply certified_cons (by exact certified163swap)
  apply certified_cons (by exact certified164)
  apply certified_cons (by exact certified165)
  apply certified_cons (by exact certified165swap)
  apply certified_cons (by exact certified166)
  apply certified_cons (by exact certified167)
  apply certified_cons (by exact certified167swap)
  apply certified_cons (by exact certified168)
  apply certified_cons (by exact certified169)
  apply certified_cons (by exact certified169swap)
  simp
#print axioms certified_keys09
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
