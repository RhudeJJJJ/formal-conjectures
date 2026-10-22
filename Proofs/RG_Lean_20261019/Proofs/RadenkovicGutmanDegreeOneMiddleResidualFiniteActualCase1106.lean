/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1106 : Family 10 := level10.get ⟨1186,by decide⟩
def sourceMap1106 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1106 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1106_checked : acceptsGraphIso
    (source (graph core1106) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2110.graph sourceMap1106=true := by decide +kernel
theorem fusedMap1106_checked : acceptsGraphIso
    (fused (graph core1106) (root 10) 2 2) DegreeTwoThreeSpectrum6358.graph fusedMap1106=true := by decide +kernel
theorem certified1106 : Certified (graph core1106) (root 10) 2 2 :=
  of_native_maps core1106 DegreeOneMiddleResidualSpectrum2110.graph DegreeTwoThreeSpectrum6358.graph
    sourceMap1106 fusedMap1106 sourceMap1106_checked fusedMap1106_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1106
#print axioms sourceMap1106_checked
#print axioms fusedMap1106_checked
#print axioms certified1106
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
