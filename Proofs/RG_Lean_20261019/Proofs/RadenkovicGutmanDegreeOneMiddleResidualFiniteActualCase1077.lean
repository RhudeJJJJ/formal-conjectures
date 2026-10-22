/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1077 : Family 10 := level10.get ⟨1107,by decide⟩
def sourceMap1077 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1077 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1077_checked : acceptsGraphIso
    (source (graph core1077) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2049.graph sourceMap1077=true := by decide +kernel
theorem fusedMap1077_checked : acceptsGraphIso
    (fused (graph core1077) (root 10) 2 2) DegreeTwoThreeSpectrum6199.graph fusedMap1077=true := by decide +kernel
theorem certified1077 : Certified (graph core1077) (root 10) 2 2 :=
  of_native_maps core1077 DegreeOneMiddleResidualSpectrum2049.graph DegreeTwoThreeSpectrum6199.graph
    sourceMap1077 fusedMap1077 sourceMap1077_checked fusedMap1077_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1077
#print axioms sourceMap1077_checked
#print axioms fusedMap1077_checked
#print axioms certified1077
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
