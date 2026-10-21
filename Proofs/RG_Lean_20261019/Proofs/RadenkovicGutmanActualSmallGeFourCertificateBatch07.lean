/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase119
import Proofs.RadenkovicGutmanActualSmallGeFourCase120
import Proofs.RadenkovicGutmanActualSmallGeFourCase121
import Proofs.RadenkovicGutmanActualSmallGeFourCase122
import Proofs.RadenkovicGutmanActualSmallGeFourCase123
import Proofs.RadenkovicGutmanActualSmallGeFourCase124
import Proofs.RadenkovicGutmanActualSmallGeFourCase125
import Proofs.RadenkovicGutmanActualSmallGeFourCase126
import Proofs.RadenkovicGutmanActualSmallGeFourCase127
import Proofs.RadenkovicGutmanActualSmallGeFourCase128
import Proofs.RadenkovicGutmanActualSmallGeFourCase129
import Proofs.RadenkovicGutmanActualSmallGeFourCase130
import Proofs.RadenkovicGutmanActualSmallGeFourCase131
import Proofs.RadenkovicGutmanActualSmallGeFourCase132
import Proofs.RadenkovicGutmanActualSmallGeFourCase133
import Proofs.RadenkovicGutmanActualSmallGeFourCase134
import Proofs.RadenkovicGutmanActualSmallGeFourCase135
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys07 : ∀ k ∈ keys07, Certified k := by
  apply certified_cons (by exact certified119)
  apply certified_cons (by exact certified119swap)
  apply certified_cons (by exact certified120)
  apply certified_cons (by exact certified121)
  apply certified_cons (by exact certified121swap)
  apply certified_cons (by exact certified122)
  apply certified_cons (by exact certified123)
  apply certified_cons (by exact certified123swap)
  apply certified_cons (by exact certified124)
  apply certified_cons (by exact certified125)
  apply certified_cons (by exact certified125swap)
  apply certified_cons (by exact certified126)
  apply certified_cons (by exact certified127)
  apply certified_cons (by exact certified127swap)
  apply certified_cons (by exact certified128)
  apply certified_cons (by exact certified129)
  apply certified_cons (by exact certified129swap)
  apply certified_cons (by exact certified130)
  apply certified_cons (by exact certified131)
  apply certified_cons (by exact certified131swap)
  apply certified_cons (by exact certified132)
  apply certified_cons (by exact certified133)
  apply certified_cons (by exact certified133swap)
  apply certified_cons (by exact certified134)
  apply certified_cons (by exact certified135)
  apply certified_cons (by exact certified135swap)
  simp
#print axioms certified_keys07
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
