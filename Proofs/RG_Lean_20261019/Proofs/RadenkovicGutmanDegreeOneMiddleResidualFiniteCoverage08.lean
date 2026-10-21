/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block000
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block001
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block002
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block003
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block004
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block005
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block006
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block007
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoreCoverage08Block008
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem covered8 : decide (∀ i : Fin (RootedCatalogueData.catalogue 8).length,
    ∀ p q : Fin 5, eligible 8 i.val p.val q.val=true →
      (⟨8,i.val,p.val,q.val⟩ : Key) ∈ keys)=true := by
  rw [decide_eq_true_eq]
  intro i p q he
  have hi := i.isLt
  change i.val < 286 at hi
  by_cases h0 : i.val < 32
  · exact CoreCoverage.range_sound 8 0 32 CoreCoverage.checked8b000 i.val p q (by omega) (by omega) he
  by_cases h1 : i.val < 64
  · exact CoreCoverage.range_sound 8 32 32 CoreCoverage.checked8b001 i.val p q (by omega) (by omega) he
  by_cases h2 : i.val < 96
  · exact CoreCoverage.range_sound 8 64 32 CoreCoverage.checked8b002 i.val p q (by omega) (by omega) he
  by_cases h3 : i.val < 128
  · exact CoreCoverage.range_sound 8 96 32 CoreCoverage.checked8b003 i.val p q (by omega) (by omega) he
  by_cases h4 : i.val < 160
  · exact CoreCoverage.range_sound 8 128 32 CoreCoverage.checked8b004 i.val p q (by omega) (by omega) he
  by_cases h5 : i.val < 192
  · exact CoreCoverage.range_sound 8 160 32 CoreCoverage.checked8b005 i.val p q (by omega) (by omega) he
  by_cases h6 : i.val < 224
  · exact CoreCoverage.range_sound 8 192 32 CoreCoverage.checked8b006 i.val p q (by omega) (by omega) he
  by_cases h7 : i.val < 256
  · exact CoreCoverage.range_sound 8 224 32 CoreCoverage.checked8b007 i.val p q (by omega) (by omega) he
  exact CoreCoverage.range_sound 8 256 30 CoreCoverage.checked8b008 i.val p q (by omega) (by omega) he
#print axioms covered8
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
