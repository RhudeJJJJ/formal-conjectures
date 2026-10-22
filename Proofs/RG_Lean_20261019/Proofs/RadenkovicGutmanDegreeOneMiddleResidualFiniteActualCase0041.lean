/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0041 : Family 7 := level7.get ⟨70,by decide⟩
def sourceMap0041 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0041 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0041_checked : acceptsGraphIso
    (source (graph core0041) (root 7) 2 2) DegreeOneMiddleResidualSpectrum098.graph sourceMap0041=true := by decide +kernel
theorem fusedMap0041_checked : acceptsGraphIso
    (fused (graph core0041) (root 7) 2 2) DegreeTwoThreeSpectrum1757.graph fusedMap0041=true := by decide +kernel
theorem certified0041 : Certified (graph core0041) (root 7) 2 2 :=
  of_native_maps core0041 DegreeOneMiddleResidualSpectrum098.graph DegreeTwoThreeSpectrum1757.graph
    sourceMap0041 fusedMap0041 sourceMap0041_checked fusedMap0041_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0041
#print axioms sourceMap0041_checked
#print axioms fusedMap0041_checked
#print axioms certified0041
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
