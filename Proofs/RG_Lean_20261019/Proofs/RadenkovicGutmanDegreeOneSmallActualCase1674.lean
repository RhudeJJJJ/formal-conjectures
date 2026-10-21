/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1674 : Family 9 := level9.get ⟨430,by decide⟩
def sourceMap1674 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (sourceLabel 9 0 1 v)
def fusedMap1674 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1674_checked : acceptsGraphIso
    (source (graph core1674) (root 9) 0 1) DegreeOneSmallSpectrum1925.graph sourceMap1674=true := by decide +kernel
theorem fusedMap1674_checked : acceptsGraphIso
    (fused (graph core1674) (root 9) 0 1) DegreeOneSmallSpectrum1320.graph fusedMap1674=true := by decide +kernel
theorem certified1674 : Certified (graph core1674) (root 9) 0 1 :=
  of_native_maps core1674 DegreeOneSmallSpectrum1925.graph DegreeOneSmallSpectrum1320.graph
    sourceMap1674 fusedMap1674 sourceMap1674_checked fusedMap1674_checked
    DegreeOneSmallComparisons.comparison1674
#print axioms sourceMap1674_checked
#print axioms fusedMap1674_checked
#print axioms certified1674
def sourceMap1674swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 9 1 0 v)
def fusedMap1674swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1674swap_checked : acceptsGraphIso
    (source (graph core1674) (root 9) 1 0) DegreeOneSmallSpectrum1925.graph sourceMap1674swap=true := by decide +kernel
theorem fusedMap1674swap_checked : acceptsGraphIso
    (fused (graph core1674) (root 9) 1 0) DegreeOneSmallSpectrum1320.graph fusedMap1674swap=true := by decide +kernel
theorem certified1674swap : Certified (graph core1674) (root 9) 1 0 :=
  of_native_maps core1674 DegreeOneSmallSpectrum1925.graph DegreeOneSmallSpectrum1320.graph
    sourceMap1674swap fusedMap1674swap sourceMap1674swap_checked fusedMap1674swap_checked
    DegreeOneSmallComparisons.comparison1674
#print axioms sourceMap1674swap_checked
#print axioms fusedMap1674swap_checked
#print axioms certified1674swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
