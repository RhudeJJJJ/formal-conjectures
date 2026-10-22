/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1177 : Family 10 := level10.get ⟨1531,by decide⟩
def sourceMap1177 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1177 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1177_checked : acceptsGraphIso
    (source (graph core1177) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2333.graph sourceMap1177=true := by decide +kernel
theorem fusedMap1177_checked : acceptsGraphIso
    (fused (graph core1177) (root 10) 2 2) DegreeTwoThreeSpectrum5971.graph fusedMap1177=true := by decide +kernel
theorem certified1177 : Certified (graph core1177) (root 10) 2 2 :=
  of_native_maps core1177 DegreeOneMiddleResidualSpectrum2333.graph DegreeTwoThreeSpectrum5971.graph
    sourceMap1177 fusedMap1177 sourceMap1177_checked fusedMap1177_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1177
#print axioms sourceMap1177_checked
#print axioms fusedMap1177_checked
#print axioms certified1177
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
