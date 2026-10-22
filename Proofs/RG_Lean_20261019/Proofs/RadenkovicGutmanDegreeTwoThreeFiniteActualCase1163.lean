/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1163 : Family 8 := level8.get ⟨201,by decide⟩
def sourceMap1163 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1163 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1163_checked : acceptsGraphIso
    (source (graph core1163) (root 8) 0 2) DegreeOneSmallSpectrum1668.graph sourceMap1163=true := by decide +kernel
theorem fusedMap1163_checked : acceptsGraphIso
    (fused (graph core1163) (root 8) 0 2) DegreeOneSmallSpectrum1022.graph fusedMap1163=true := by decide +kernel
theorem certified1163 : Certified (graph core1163) (root 8) 0 2 :=
  of_native_maps core1163 DegreeOneSmallSpectrum1668.graph DegreeOneSmallSpectrum1022.graph
    sourceMap1163 fusedMap1163 sourceMap1163_checked fusedMap1163_checked
    DegreeTwoThreeFiniteComparisons.comparison1163
#print axioms sourceMap1163_checked
#print axioms fusedMap1163_checked
#print axioms certified1163
def sourceMap1163swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1163swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1163swap_checked : acceptsGraphIso
    (source (graph core1163) (root 8) 2 0) DegreeOneSmallSpectrum1668.graph sourceMap1163swap=true := by decide +kernel
theorem fusedMap1163swap_checked : acceptsGraphIso
    (fused (graph core1163) (root 8) 2 0) DegreeOneSmallSpectrum1022.graph fusedMap1163swap=true := by decide +kernel
theorem certified1163swap : Certified (graph core1163) (root 8) 2 0 :=
  of_native_maps core1163 DegreeOneSmallSpectrum1668.graph DegreeOneSmallSpectrum1022.graph
    sourceMap1163swap fusedMap1163swap sourceMap1163swap_checked fusedMap1163swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1163
#print axioms sourceMap1163swap_checked
#print axioms fusedMap1163swap_checked
#print axioms certified1163swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
