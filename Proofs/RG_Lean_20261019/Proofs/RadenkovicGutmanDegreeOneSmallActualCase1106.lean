/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1106 : Family 8 := level8.get ⟨151,by decide⟩
def sourceMap1106 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1106 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1106_checked : acceptsGraphIso
    (source (graph core1106) (root 8) 1 1) DegreeOneSmallSpectrum1924.graph sourceMap1106=true := by decide +kernel
theorem fusedMap1106_checked : acceptsGraphIso
    (fused (graph core1106) (root 8) 1 1) DegreeOneSmallSpectrum1408.graph fusedMap1106=true := by decide +kernel
theorem certified1106 : Certified (graph core1106) (root 8) 1 1 :=
  of_native_maps core1106 DegreeOneSmallSpectrum1924.graph DegreeOneSmallSpectrum1408.graph
    sourceMap1106 fusedMap1106 sourceMap1106_checked fusedMap1106_checked
    DegreeOneSmallComparisons.comparison1106
#print axioms sourceMap1106_checked
#print axioms fusedMap1106_checked
#print axioms certified1106
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
