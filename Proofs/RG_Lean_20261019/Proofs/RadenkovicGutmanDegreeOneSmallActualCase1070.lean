/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1070 : Family 8 := level8.get ⟨134,by decide⟩
def sourceMap1070 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap1070 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1070_checked : acceptsGraphIso
    (source (graph core1070) (root 8) 1 1) DegreeOneSmallSpectrum1908.graph sourceMap1070=true := by decide +kernel
theorem fusedMap1070_checked : acceptsGraphIso
    (fused (graph core1070) (root 8) 1 1) DegreeOneSmallSpectrum1306.graph fusedMap1070=true := by decide +kernel
theorem certified1070 : Certified (graph core1070) (root 8) 1 1 :=
  of_native_maps core1070 DegreeOneSmallSpectrum1908.graph DegreeOneSmallSpectrum1306.graph
    sourceMap1070 fusedMap1070 sourceMap1070_checked fusedMap1070_checked
    DegreeOneSmallComparisons.comparison1070
#print axioms sourceMap1070_checked
#print axioms fusedMap1070_checked
#print axioms certified1070
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
