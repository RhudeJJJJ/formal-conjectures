/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1088 : Family 10 := level10.get ⟨1134,by decide⟩
def sourceMap1088 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1088 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1088_checked : acceptsGraphIso
    (source (graph core1088) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2071.graph sourceMap1088=true := by decide +kernel
theorem fusedMap1088_checked : acceptsGraphIso
    (fused (graph core1088) (root 10) 2 2) DegreeTwoThreeSpectrum6257.graph fusedMap1088=true := by decide +kernel
theorem certified1088 : Certified (graph core1088) (root 10) 2 2 :=
  of_native_maps core1088 DegreeOneMiddleResidualSpectrum2071.graph DegreeTwoThreeSpectrum6257.graph
    sourceMap1088 fusedMap1088 sourceMap1088_checked fusedMap1088_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1088
#print axioms sourceMap1088_checked
#print axioms fusedMap1088_checked
#print axioms certified1088
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
