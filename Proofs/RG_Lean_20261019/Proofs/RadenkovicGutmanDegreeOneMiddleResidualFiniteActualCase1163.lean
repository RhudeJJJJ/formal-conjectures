/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1163 : Family 10 := level10.get ⟨1418,by decide⟩
def sourceMap1163 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap1163 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1163_checked : acceptsGraphIso
    (source (graph core1163) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2268.graph sourceMap1163=true := by decide +kernel
theorem fusedMap1163_checked : acceptsGraphIso
    (fused (graph core1163) (root 10) 2 2) DegreeTwoThreeSpectrum6869.graph fusedMap1163=true := by decide +kernel
theorem certified1163 : Certified (graph core1163) (root 10) 2 2 :=
  of_native_maps core1163 DegreeOneMiddleResidualSpectrum2268.graph DegreeTwoThreeSpectrum6869.graph
    sourceMap1163 fusedMap1163 sourceMap1163_checked fusedMap1163_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1163
#print axioms sourceMap1163_checked
#print axioms fusedMap1163_checked
#print axioms certified1163
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
