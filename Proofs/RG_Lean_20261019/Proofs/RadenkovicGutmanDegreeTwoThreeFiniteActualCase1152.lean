/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1152 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap1152 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,7,4,5,6] (sourceLabel 8 0 2 v)
def fusedMap1152 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 0 2 v)
theorem sourceMap1152_checked : acceptsGraphIso
    (source (graph core1152) (root 8) 0 2) DegreeOneSmallSpectrum1458.graph sourceMap1152=true := by decide +kernel
theorem fusedMap1152_checked : acceptsGraphIso
    (fused (graph core1152) (root 8) 0 2) DegreeOneSmallSpectrum1504.graph fusedMap1152=true := by decide +kernel
theorem certified1152 : Certified (graph core1152) (root 8) 0 2 :=
  of_native_maps core1152 DegreeOneSmallSpectrum1458.graph DegreeOneSmallSpectrum1504.graph
    sourceMap1152 fusedMap1152 sourceMap1152_checked fusedMap1152_checked
    DegreeTwoThreeFiniteComparisons.comparison1152
#print axioms sourceMap1152_checked
#print axioms fusedMap1152_checked
#print axioms certified1152
def sourceMap1152swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 8 2 0 v)
def fusedMap1152swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 2 0 v)
theorem sourceMap1152swap_checked : acceptsGraphIso
    (source (graph core1152) (root 8) 2 0) DegreeOneSmallSpectrum1458.graph sourceMap1152swap=true := by decide +kernel
theorem fusedMap1152swap_checked : acceptsGraphIso
    (fused (graph core1152) (root 8) 2 0) DegreeOneSmallSpectrum1504.graph fusedMap1152swap=true := by decide +kernel
theorem certified1152swap : Certified (graph core1152) (root 8) 2 0 :=
  of_native_maps core1152 DegreeOneSmallSpectrum1458.graph DegreeOneSmallSpectrum1504.graph
    sourceMap1152swap fusedMap1152swap sourceMap1152swap_checked fusedMap1152swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1152
#print axioms sourceMap1152swap_checked
#print axioms fusedMap1152swap_checked
#print axioms certified1152swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
