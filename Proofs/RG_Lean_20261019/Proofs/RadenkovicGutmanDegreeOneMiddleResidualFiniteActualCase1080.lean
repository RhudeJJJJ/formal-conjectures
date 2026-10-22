/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1080 : Family 10 := level10.get ⟨1114,by decide⟩
def sourceMap1080 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1080 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1080_checked : acceptsGraphIso
    (source (graph core1080) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2055.graph sourceMap1080=true := by decide +kernel
theorem fusedMap1080_checked : acceptsGraphIso
    (fused (graph core1080) (root 10) 2 2) DegreeTwoThreeSpectrum6216.graph fusedMap1080=true := by decide +kernel
theorem certified1080 : Certified (graph core1080) (root 10) 2 2 :=
  of_native_maps core1080 DegreeOneMiddleResidualSpectrum2055.graph DegreeTwoThreeSpectrum6216.graph
    sourceMap1080 fusedMap1080 sourceMap1080_checked fusedMap1080_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1080
#print axioms sourceMap1080_checked
#print axioms fusedMap1080_checked
#print axioms certified1080
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
