/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0650 : Family 10 := level10.get ⟨227,by decide⟩
def sourceMap0650 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0650 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0650_checked : acceptsGraphIso
    (source (graph core0650) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1643.graph sourceMap0650=true := by decide +kernel
theorem fusedMap0650_checked : acceptsGraphIso
    (fused (graph core0650) (root 10) 2 2) DegreeTwoThreeSpectrum5272.graph fusedMap0650=true := by decide +kernel
theorem certified0650 : Certified (graph core0650) (root 10) 2 2 :=
  of_native_maps core0650 DegreeOneMiddleResidualSpectrum1643.graph DegreeTwoThreeSpectrum5272.graph
    sourceMap0650 fusedMap0650 sourceMap0650_checked fusedMap0650_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0650
#print axioms sourceMap0650_checked
#print axioms fusedMap0650_checked
#print axioms certified0650
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
