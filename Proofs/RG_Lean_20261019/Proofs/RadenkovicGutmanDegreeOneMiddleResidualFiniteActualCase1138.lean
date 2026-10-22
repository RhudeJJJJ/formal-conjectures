/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1138 : Family 10 := level10.get ⟨1306,by decide⟩
def sourceMap1138 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1138 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1138_checked : acceptsGraphIso
    (source (graph core1138) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2193.graph sourceMap1138=true := by decide +kernel
theorem fusedMap1138_checked : acceptsGraphIso
    (fused (graph core1138) (root 10) 2 2) DegreeTwoThreeSpectrum6602.graph fusedMap1138=true := by decide +kernel
theorem certified1138 : Certified (graph core1138) (root 10) 2 2 :=
  of_native_maps core1138 DegreeOneMiddleResidualSpectrum2193.graph DegreeTwoThreeSpectrum6602.graph
    sourceMap1138 fusedMap1138 sourceMap1138_checked fusedMap1138_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1138
#print axioms sourceMap1138_checked
#print axioms fusedMap1138_checked
#print axioms certified1138
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
