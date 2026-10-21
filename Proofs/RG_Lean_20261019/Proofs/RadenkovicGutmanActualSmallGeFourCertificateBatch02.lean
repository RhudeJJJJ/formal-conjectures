/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourKeysData
import Proofs.RadenkovicGutmanActualSmallGeFourCase034
import Proofs.RadenkovicGutmanActualSmallGeFourCase035
import Proofs.RadenkovicGutmanActualSmallGeFourCase036
import Proofs.RadenkovicGutmanActualSmallGeFourCase037
import Proofs.RadenkovicGutmanActualSmallGeFourCase038
import Proofs.RadenkovicGutmanActualSmallGeFourCase039
import Proofs.RadenkovicGutmanActualSmallGeFourCase040
import Proofs.RadenkovicGutmanActualSmallGeFourCase041
import Proofs.RadenkovicGutmanActualSmallGeFourCase042
import Proofs.RadenkovicGutmanActualSmallGeFourCase043
import Proofs.RadenkovicGutmanActualSmallGeFourCase044
import Proofs.RadenkovicGutmanActualSmallGeFourCase045
import Proofs.RadenkovicGutmanActualSmallGeFourCase046
import Proofs.RadenkovicGutmanActualSmallGeFourCase047
import Proofs.RadenkovicGutmanActualSmallGeFourCase048
import Proofs.RadenkovicGutmanActualSmallGeFourCase049
import Proofs.RadenkovicGutmanActualSmallGeFourCase050
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
open SmallGeFourActualCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_keys02 : ∀ k ∈ keys02, Certified k := by
  apply certified_cons (by exact certified034)
  apply certified_cons (by exact certified035)
  apply certified_cons (by exact certified035swap)
  apply certified_cons (by exact certified036)
  apply certified_cons (by exact certified037)
  apply certified_cons (by exact certified037swap)
  apply certified_cons (by exact certified038)
  apply certified_cons (by exact certified038swap)
  apply certified_cons (by exact certified039)
  apply certified_cons (by exact certified039swap)
  apply certified_cons (by exact certified040)
  apply certified_cons (by exact certified041)
  apply certified_cons (by exact certified041swap)
  apply certified_cons (by exact certified042)
  apply certified_cons (by exact certified043)
  apply certified_cons (by exact certified043swap)
  apply certified_cons (by exact certified044)
  apply certified_cons (by exact certified044swap)
  apply certified_cons (by exact certified045)
  apply certified_cons (by exact certified045swap)
  apply certified_cons (by exact certified046)
  apply certified_cons (by exact certified047)
  apply certified_cons (by exact certified047swap)
  apply certified_cons (by exact certified048)
  apply certified_cons (by exact certified049)
  apply certified_cons (by exact certified049swap)
  apply certified_cons (by exact certified050)
  apply certified_cons (by exact certified050swap)
  simp
#print axioms certified_keys02
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
