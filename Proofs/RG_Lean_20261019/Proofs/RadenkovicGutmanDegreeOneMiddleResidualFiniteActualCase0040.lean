/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0040 : Family 7 := level7.get ⟨66,by decide⟩
def sourceMap0040 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0040 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0040_checked : acceptsGraphIso
    (source (graph core0040) (root 7) 2 2) DegreeOneMiddleResidualSpectrum097.graph sourceMap0040=true := by decide +kernel
theorem fusedMap0040_checked : acceptsGraphIso
    (fused (graph core0040) (root 7) 2 2) DegreeTwoThreeSpectrum1743.graph fusedMap0040=true := by decide +kernel
theorem certified0040 : Certified (graph core0040) (root 7) 2 2 :=
  of_native_maps core0040 DegreeOneMiddleResidualSpectrum097.graph DegreeTwoThreeSpectrum1743.graph
    sourceMap0040 fusedMap0040 sourceMap0040_checked fusedMap0040_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0040
#print axioms sourceMap0040_checked
#print axioms fusedMap0040_checked
#print axioms certified0040
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
