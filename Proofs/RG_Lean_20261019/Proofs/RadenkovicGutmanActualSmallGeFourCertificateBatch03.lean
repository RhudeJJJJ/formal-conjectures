/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase051
import Proofs.RadenkovicGutmanActualSmallGeFourCase052
import Proofs.RadenkovicGutmanActualSmallGeFourCase053
import Proofs.RadenkovicGutmanActualSmallGeFourCase054
import Proofs.RadenkovicGutmanActualSmallGeFourCase055
import Proofs.RadenkovicGutmanActualSmallGeFourCase056
import Proofs.RadenkovicGutmanActualSmallGeFourCase057
import Proofs.RadenkovicGutmanActualSmallGeFourCase058
import Proofs.RadenkovicGutmanActualSmallGeFourCase059
import Proofs.RadenkovicGutmanActualSmallGeFourCase060
import Proofs.RadenkovicGutmanActualSmallGeFourCase061
import Proofs.RadenkovicGutmanActualSmallGeFourCase062
import Proofs.RadenkovicGutmanActualSmallGeFourCase063
import Proofs.RadenkovicGutmanActualSmallGeFourCase064
import Proofs.RadenkovicGutmanActualSmallGeFourCase065
import Proofs.RadenkovicGutmanActualSmallGeFourCase066
import Proofs.RadenkovicGutmanActualSmallGeFourCase067
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys03 : ∀ k ∈ keys03, Certified k := by
  apply certified_cons (by exact certified051)
  apply certified_cons (by exact certified051swap)
  apply certified_cons (by exact certified052)
  apply certified_cons (by exact certified053)
  apply certified_cons (by exact certified053swap)
  apply certified_cons (by exact certified054)
  apply certified_cons (by exact certified055)
  apply certified_cons (by exact certified055swap)
  apply certified_cons (by exact certified056)
  apply certified_cons (by exact certified056swap)
  apply certified_cons (by exact certified057)
  apply certified_cons (by exact certified057swap)
  apply certified_cons (by exact certified058)
  apply certified_cons (by exact certified059)
  apply certified_cons (by exact certified059swap)
  apply certified_cons (by exact certified060)
  apply certified_cons (by exact certified061)
  apply certified_cons (by exact certified061swap)
  apply certified_cons (by exact certified062)
  apply certified_cons (by exact certified062swap)
  apply certified_cons (by exact certified063)
  apply certified_cons (by exact certified064)
  apply certified_cons (by exact certified065)
  apply certified_cons (by exact certified065swap)
  apply certified_cons (by exact certified066)
  apply certified_cons (by exact certified066swap)
  apply certified_cons (by exact certified067)
  simp
#print axioms certified_keys03
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
