/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0443 : Family 9 := level9.get ⟨447,by decide⟩
def sourceMap0443 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0443 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0443_checked : acceptsGraphIso
    (source (graph core0443) (root 9) 2 2) DegreeOneMiddleResidualSpectrum843.graph sourceMap0443=true := by decide +kernel
theorem fusedMap0443_checked : acceptsGraphIso
    (fused (graph core0443) (root 9) 2 2) DegreeTwoThreeSpectrum4461.graph fusedMap0443=true := by decide +kernel
theorem certified0443 : Certified (graph core0443) (root 9) 2 2 :=
  of_native_maps core0443 DegreeOneMiddleResidualSpectrum843.graph DegreeTwoThreeSpectrum4461.graph
    sourceMap0443 fusedMap0443 sourceMap0443_checked fusedMap0443_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0443
#print axioms sourceMap0443_checked
#print axioms fusedMap0443_checked
#print axioms certified0443
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
