/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase102
import Proofs.RadenkovicGutmanActualSmallGeFourCase103
import Proofs.RadenkovicGutmanActualSmallGeFourCase104
import Proofs.RadenkovicGutmanActualSmallGeFourCase105
import Proofs.RadenkovicGutmanActualSmallGeFourCase106
import Proofs.RadenkovicGutmanActualSmallGeFourCase107
import Proofs.RadenkovicGutmanActualSmallGeFourCase108
import Proofs.RadenkovicGutmanActualSmallGeFourCase109
import Proofs.RadenkovicGutmanActualSmallGeFourCase110
import Proofs.RadenkovicGutmanActualSmallGeFourCase111
import Proofs.RadenkovicGutmanActualSmallGeFourCase112
import Proofs.RadenkovicGutmanActualSmallGeFourCase113
import Proofs.RadenkovicGutmanActualSmallGeFourCase114
import Proofs.RadenkovicGutmanActualSmallGeFourCase115
import Proofs.RadenkovicGutmanActualSmallGeFourCase116
import Proofs.RadenkovicGutmanActualSmallGeFourCase117
import Proofs.RadenkovicGutmanActualSmallGeFourCase118
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys06 : ∀ k ∈ keys06, Certified k := by
  apply certified_cons (by exact certified102)
  apply certified_cons (by exact certified102swap)
  apply certified_cons (by exact certified103)
  apply certified_cons (by exact certified104)
  apply certified_cons (by exact certified105)
  apply certified_cons (by exact certified105swap)
  apply certified_cons (by exact certified106)
  apply certified_cons (by exact certified106swap)
  apply certified_cons (by exact certified107)
  apply certified_cons (by exact certified108)
  apply certified_cons (by exact certified109)
  apply certified_cons (by exact certified109swap)
  apply certified_cons (by exact certified110)
  apply certified_cons (by exact certified111)
  apply certified_cons (by exact certified111swap)
  apply certified_cons (by exact certified112)
  apply certified_cons (by exact certified113)
  apply certified_cons (by exact certified113swap)
  apply certified_cons (by exact certified114)
  apply certified_cons (by exact certified115)
  apply certified_cons (by exact certified115swap)
  apply certified_cons (by exact certified116)
  apply certified_cons (by exact certified117)
  apply certified_cons (by exact certified117swap)
  apply certified_cons (by exact certified118)
  simp
#print axioms certified_keys06
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
