/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase085
import Proofs.RadenkovicGutmanActualSmallGeFourCase086
import Proofs.RadenkovicGutmanActualSmallGeFourCase087
import Proofs.RadenkovicGutmanActualSmallGeFourCase088
import Proofs.RadenkovicGutmanActualSmallGeFourCase089
import Proofs.RadenkovicGutmanActualSmallGeFourCase090
import Proofs.RadenkovicGutmanActualSmallGeFourCase091
import Proofs.RadenkovicGutmanActualSmallGeFourCase092
import Proofs.RadenkovicGutmanActualSmallGeFourCase093
import Proofs.RadenkovicGutmanActualSmallGeFourCase094
import Proofs.RadenkovicGutmanActualSmallGeFourCase095
import Proofs.RadenkovicGutmanActualSmallGeFourCase096
import Proofs.RadenkovicGutmanActualSmallGeFourCase097
import Proofs.RadenkovicGutmanActualSmallGeFourCase098
import Proofs.RadenkovicGutmanActualSmallGeFourCase099
import Proofs.RadenkovicGutmanActualSmallGeFourCase100
import Proofs.RadenkovicGutmanActualSmallGeFourCase101
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys05 : ∀ k ∈ keys05, Certified k := by
  apply certified_cons (by exact certified085)
  apply certified_cons (by exact certified085swap)
  apply certified_cons (by exact certified086)
  apply certified_cons (by exact certified086swap)
  apply certified_cons (by exact certified087)
  apply certified_cons (by exact certified088)
  apply certified_cons (by exact certified089)
  apply certified_cons (by exact certified089swap)
  apply certified_cons (by exact certified090)
  apply certified_cons (by exact certified090swap)
  apply certified_cons (by exact certified091)
  apply certified_cons (by exact certified092)
  apply certified_cons (by exact certified093)
  apply certified_cons (by exact certified093swap)
  apply certified_cons (by exact certified094)
  apply certified_cons (by exact certified094swap)
  apply certified_cons (by exact certified095)
  apply certified_cons (by exact certified096)
  apply certified_cons (by exact certified097)
  apply certified_cons (by exact certified097swap)
  apply certified_cons (by exact certified098)
  apply certified_cons (by exact certified098swap)
  apply certified_cons (by exact certified099)
  apply certified_cons (by exact certified100)
  apply certified_cons (by exact certified101)
  apply certified_cons (by exact certified101swap)
  simp
#print axioms certified_keys05
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
