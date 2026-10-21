/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase017
import Proofs.RadenkovicGutmanActualSmallGeFourCase018
import Proofs.RadenkovicGutmanActualSmallGeFourCase019
import Proofs.RadenkovicGutmanActualSmallGeFourCase020
import Proofs.RadenkovicGutmanActualSmallGeFourCase021
import Proofs.RadenkovicGutmanActualSmallGeFourCase022
import Proofs.RadenkovicGutmanActualSmallGeFourCase023
import Proofs.RadenkovicGutmanActualSmallGeFourCase024
import Proofs.RadenkovicGutmanActualSmallGeFourCase025
import Proofs.RadenkovicGutmanActualSmallGeFourCase026
import Proofs.RadenkovicGutmanActualSmallGeFourCase027
import Proofs.RadenkovicGutmanActualSmallGeFourCase028
import Proofs.RadenkovicGutmanActualSmallGeFourCase029
import Proofs.RadenkovicGutmanActualSmallGeFourCase030
import Proofs.RadenkovicGutmanActualSmallGeFourCase031
import Proofs.RadenkovicGutmanActualSmallGeFourCase032
import Proofs.RadenkovicGutmanActualSmallGeFourCase033
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys01 : ∀ k ∈ keys01, Certified k := by
  apply certified_cons (by exact certified017)
  apply certified_cons (by exact certified018)
  apply certified_cons (by exact certified018swap)
  apply certified_cons (by exact certified019)
  apply certified_cons (by exact certified019swap)
  apply certified_cons (by exact certified020)
  apply certified_cons (by exact certified021)
  apply certified_cons (by exact certified022)
  apply certified_cons (by exact certified022swap)
  apply certified_cons (by exact certified023)
  apply certified_cons (by exact certified023swap)
  apply certified_cons (by exact certified024)
  apply certified_cons (by exact certified024swap)
  apply certified_cons (by exact certified025)
  apply certified_cons (by exact certified025swap)
  apply certified_cons (by exact certified026)
  apply certified_cons (by exact certified027)
  apply certified_cons (by exact certified027swap)
  apply certified_cons (by exact certified028)
  apply certified_cons (by exact certified028swap)
  apply certified_cons (by exact certified029)
  apply certified_cons (by exact certified030)
  apply certified_cons (by exact certified031)
  apply certified_cons (by exact certified031swap)
  apply certified_cons (by exact certified032)
  apply certified_cons (by exact certified032swap)
  apply certified_cons (by exact certified033)
  apply certified_cons (by exact certified033swap)
  simp
#print axioms certified_keys01
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
