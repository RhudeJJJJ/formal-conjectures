/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase068
import Proofs.RadenkovicGutmanActualSmallGeFourCase069
import Proofs.RadenkovicGutmanActualSmallGeFourCase070
import Proofs.RadenkovicGutmanActualSmallGeFourCase071
import Proofs.RadenkovicGutmanActualSmallGeFourCase072
import Proofs.RadenkovicGutmanActualSmallGeFourCase073
import Proofs.RadenkovicGutmanActualSmallGeFourCase074
import Proofs.RadenkovicGutmanActualSmallGeFourCase075
import Proofs.RadenkovicGutmanActualSmallGeFourCase076
import Proofs.RadenkovicGutmanActualSmallGeFourCase077
import Proofs.RadenkovicGutmanActualSmallGeFourCase078
import Proofs.RadenkovicGutmanActualSmallGeFourCase079
import Proofs.RadenkovicGutmanActualSmallGeFourCase080
import Proofs.RadenkovicGutmanActualSmallGeFourCase081
import Proofs.RadenkovicGutmanActualSmallGeFourCase082
import Proofs.RadenkovicGutmanActualSmallGeFourCase083
import Proofs.RadenkovicGutmanActualSmallGeFourCase084
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys04 : ∀ k ∈ keys04, Certified k := by
  apply certified_cons (by exact certified068)
  apply certified_cons (by exact certified069)
  apply certified_cons (by exact certified069swap)
  apply certified_cons (by exact certified070)
  apply certified_cons (by exact certified070swap)
  apply certified_cons (by exact certified071)
  apply certified_cons (by exact certified072)
  apply certified_cons (by exact certified073)
  apply certified_cons (by exact certified073swap)
  apply certified_cons (by exact certified074)
  apply certified_cons (by exact certified074swap)
  apply certified_cons (by exact certified075)
  apply certified_cons (by exact certified076)
  apply certified_cons (by exact certified077)
  apply certified_cons (by exact certified077swap)
  apply certified_cons (by exact certified078)
  apply certified_cons (by exact certified078swap)
  apply certified_cons (by exact certified079)
  apply certified_cons (by exact certified080)
  apply certified_cons (by exact certified081)
  apply certified_cons (by exact certified081swap)
  apply certified_cons (by exact certified082)
  apply certified_cons (by exact certified082swap)
  apply certified_cons (by exact certified083)
  apply certified_cons (by exact certified084)
  simp
#print axioms certified_keys04
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
