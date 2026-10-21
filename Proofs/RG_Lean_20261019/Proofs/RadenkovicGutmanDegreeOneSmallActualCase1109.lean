/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1109 : Family 8 := level8.get ⟨153,by decide⟩
def sourceMap1109 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1109 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1109_checked : acceptsGraphIso
    (source (graph core1109) (root 8) 0 2) DegreeOneSmallSpectrum1417.graph sourceMap1109=true := by decide +kernel
theorem fusedMap1109_checked : acceptsGraphIso
    (fused (graph core1109) (root 8) 0 2) DegreeOneSmallSpectrum1418.graph fusedMap1109=true := by decide +kernel
theorem certified1109 : Certified (graph core1109) (root 8) 0 2 :=
  of_native_maps core1109 DegreeOneSmallSpectrum1417.graph DegreeOneSmallSpectrum1418.graph
    sourceMap1109 fusedMap1109 sourceMap1109_checked fusedMap1109_checked
    DegreeOneSmallComparisons.comparison1109
#print axioms sourceMap1109_checked
#print axioms fusedMap1109_checked
#print axioms certified1109
def sourceMap1109swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1109swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1109swap_checked : acceptsGraphIso
    (source (graph core1109) (root 8) 2 0) DegreeOneSmallSpectrum1417.graph sourceMap1109swap=true := by decide +kernel
theorem fusedMap1109swap_checked : acceptsGraphIso
    (fused (graph core1109) (root 8) 2 0) DegreeOneSmallSpectrum1418.graph fusedMap1109swap=true := by decide +kernel
theorem certified1109swap : Certified (graph core1109) (root 8) 2 0 :=
  of_native_maps core1109 DegreeOneSmallSpectrum1417.graph DegreeOneSmallSpectrum1418.graph
    sourceMap1109swap fusedMap1109swap sourceMap1109swap_checked fusedMap1109swap_checked
    DegreeOneSmallComparisons.comparison1109
#print axioms sourceMap1109swap_checked
#print axioms fusedMap1109swap_checked
#print axioms certified1109swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
