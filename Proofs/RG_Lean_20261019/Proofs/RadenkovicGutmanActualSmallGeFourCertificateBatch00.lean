/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase000
import Proofs.RadenkovicGutmanActualSmallGeFourCase001
import Proofs.RadenkovicGutmanActualSmallGeFourCase002
import Proofs.RadenkovicGutmanActualSmallGeFourCase003
import Proofs.RadenkovicGutmanActualSmallGeFourCase004
import Proofs.RadenkovicGutmanActualSmallGeFourCase005
import Proofs.RadenkovicGutmanActualSmallGeFourCase006
import Proofs.RadenkovicGutmanActualSmallGeFourCase007
import Proofs.RadenkovicGutmanActualSmallGeFourCase008
import Proofs.RadenkovicGutmanActualSmallGeFourCase009
import Proofs.RadenkovicGutmanActualSmallGeFourCase010
import Proofs.RadenkovicGutmanActualSmallGeFourCase011
import Proofs.RadenkovicGutmanActualSmallGeFourCase012
import Proofs.RadenkovicGutmanActualSmallGeFourCase013
import Proofs.RadenkovicGutmanActualSmallGeFourCase014
import Proofs.RadenkovicGutmanActualSmallGeFourCase015
import Proofs.RadenkovicGutmanActualSmallGeFourCase016
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys00 : ∀ k ∈ keys00, Certified k := by
  apply certified_cons (by exact certified000)
  apply certified_cons (by exact certified001)
  apply certified_cons (by exact certified001swap)
  apply certified_cons (by exact certified002)
  apply certified_cons (by exact certified002swap)
  apply certified_cons (by exact certified003)
  apply certified_cons (by exact certified003swap)
  apply certified_cons (by exact certified004)
  apply certified_cons (by exact certified004swap)
  apply certified_cons (by exact certified005)
  apply certified_cons (by exact certified005swap)
  apply certified_cons (by exact certified006)
  apply certified_cons (by exact certified007)
  apply certified_cons (by exact certified007swap)
  apply certified_cons (by exact certified008)
  apply certified_cons (by exact certified008swap)
  apply certified_cons (by exact certified009)
  apply certified_cons (by exact certified009swap)
  apply certified_cons (by exact certified010)
  apply certified_cons (by exact certified011)
  apply certified_cons (by exact certified011swap)
  apply certified_cons (by exact certified012)
  apply certified_cons (by exact certified013)
  apply certified_cons (by exact certified013swap)
  apply certified_cons (by exact certified014)
  apply certified_cons (by exact certified014swap)
  apply certified_cons (by exact certified015)
  apply certified_cons (by exact certified015swap)
  apply certified_cons (by exact certified016)
  apply certified_cons (by exact certified016swap)
  simp
#print axioms certified_keys00
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
