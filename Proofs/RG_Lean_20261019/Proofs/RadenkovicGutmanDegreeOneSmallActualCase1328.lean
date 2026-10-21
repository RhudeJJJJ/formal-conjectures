/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1328 : Family 9 := level9.get ⟨85,by decide⟩
def sourceMap1328 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1328 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1328_checked : acceptsGraphIso
    (source (graph core1328) (root 9) 0 1) DegreeOneSmallSpectrum1437.graph sourceMap1328=true := by decide +kernel
theorem fusedMap1328_checked : acceptsGraphIso
    (fused (graph core1328) (root 9) 0 1) DegreeOneSmallSpectrum931.graph fusedMap1328=true := by decide +kernel
theorem certified1328 : Certified (graph core1328) (root 9) 0 1 :=
  of_native_maps core1328 DegreeOneSmallSpectrum1437.graph DegreeOneSmallSpectrum931.graph
    sourceMap1328 fusedMap1328 sourceMap1328_checked fusedMap1328_checked
    DegreeOneSmallComparisons.comparison1328
#print axioms sourceMap1328_checked
#print axioms fusedMap1328_checked
#print axioms certified1328
def sourceMap1328swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1328swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1328swap_checked : acceptsGraphIso
    (source (graph core1328) (root 9) 1 0) DegreeOneSmallSpectrum1437.graph sourceMap1328swap=true := by decide +kernel
theorem fusedMap1328swap_checked : acceptsGraphIso
    (fused (graph core1328) (root 9) 1 0) DegreeOneSmallSpectrum931.graph fusedMap1328swap=true := by decide +kernel
theorem certified1328swap : Certified (graph core1328) (root 9) 1 0 :=
  of_native_maps core1328 DegreeOneSmallSpectrum1437.graph DegreeOneSmallSpectrum931.graph
    sourceMap1328swap fusedMap1328swap sourceMap1328swap_checked fusedMap1328swap_checked
    DegreeOneSmallComparisons.comparison1328
#print axioms sourceMap1328swap_checked
#print axioms fusedMap1328swap_checked
#print axioms certified1328swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
