/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1065 : Family 10 := level10.get ⟨1070,by decide⟩
def sourceMap1065 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1065 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1065_checked : acceptsGraphIso
    (source (graph core1065) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2022.graph sourceMap1065=true := by decide +kernel
theorem fusedMap1065_checked : acceptsGraphIso
    (fused (graph core1065) (root 10) 2 2) DegreeTwoThreeSpectrum6129.graph fusedMap1065=true := by decide +kernel
theorem certified1065 : Certified (graph core1065) (root 10) 2 2 :=
  of_native_maps core1065 DegreeOneMiddleResidualSpectrum2022.graph DegreeTwoThreeSpectrum6129.graph
    sourceMap1065 fusedMap1065 sourceMap1065_checked fusedMap1065_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1065
#print axioms sourceMap1065_checked
#print axioms fusedMap1065_checked
#print axioms certified1065
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
