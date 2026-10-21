/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1654 : Family 9 := level9.get ⟨398,by decide⟩
def sourceMap1654 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1654 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1654_checked : acceptsGraphIso
    (source (graph core1654) (root 9) 0 1) DegreeOneSmallSpectrum1875.graph sourceMap1654=true := by decide +kernel
theorem fusedMap1654_checked : acceptsGraphIso
    (fused (graph core1654) (root 9) 0 1) DegreeOneSmallSpectrum1212.graph fusedMap1654=true := by decide +kernel
theorem certified1654 : Certified (graph core1654) (root 9) 0 1 :=
  of_native_maps core1654 DegreeOneSmallSpectrum1875.graph DegreeOneSmallSpectrum1212.graph
    sourceMap1654 fusedMap1654 sourceMap1654_checked fusedMap1654_checked
    DegreeOneSmallComparisons.comparison1654
#print axioms sourceMap1654_checked
#print axioms fusedMap1654_checked
#print axioms certified1654
def sourceMap1654swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1654swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1654swap_checked : acceptsGraphIso
    (source (graph core1654) (root 9) 1 0) DegreeOneSmallSpectrum1875.graph sourceMap1654swap=true := by decide +kernel
theorem fusedMap1654swap_checked : acceptsGraphIso
    (fused (graph core1654) (root 9) 1 0) DegreeOneSmallSpectrum1212.graph fusedMap1654swap=true := by decide +kernel
theorem certified1654swap : Certified (graph core1654) (root 9) 1 0 :=
  of_native_maps core1654 DegreeOneSmallSpectrum1875.graph DegreeOneSmallSpectrum1212.graph
    sourceMap1654swap fusedMap1654swap sourceMap1654swap_checked fusedMap1654swap_checked
    DegreeOneSmallComparisons.comparison1654
#print axioms sourceMap1654swap_checked
#print axioms fusedMap1654swap_checked
#print axioms certified1654swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
