/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1123 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap1123 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1123 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1123_checked : acceptsGraphIso
    (source (graph core1123) (root 8) 0 2) DegreeOneSmallSpectrum1035.graph sourceMap1123=true := by decide +kernel
theorem fusedMap1123_checked : acceptsGraphIso
    (fused (graph core1123) (root 8) 0 2) DegreeOneSmallSpectrum1037.graph fusedMap1123=true := by decide +kernel
theorem certified1123 : Certified (graph core1123) (root 8) 0 2 :=
  of_native_maps core1123 DegreeOneSmallSpectrum1035.graph DegreeOneSmallSpectrum1037.graph
    sourceMap1123 fusedMap1123 sourceMap1123_checked fusedMap1123_checked
    DegreeTwoThreeFiniteComparisons.comparison1123
#print axioms sourceMap1123_checked
#print axioms fusedMap1123_checked
#print axioms certified1123
def sourceMap1123swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1123swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1123swap_checked : acceptsGraphIso
    (source (graph core1123) (root 8) 2 0) DegreeOneSmallSpectrum1035.graph sourceMap1123swap=true := by decide +kernel
theorem fusedMap1123swap_checked : acceptsGraphIso
    (fused (graph core1123) (root 8) 2 0) DegreeOneSmallSpectrum1037.graph fusedMap1123swap=true := by decide +kernel
theorem certified1123swap : Certified (graph core1123) (root 8) 2 0 :=
  of_native_maps core1123 DegreeOneSmallSpectrum1035.graph DegreeOneSmallSpectrum1037.graph
    sourceMap1123swap fusedMap1123swap sourceMap1123swap_checked fusedMap1123swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1123
#print axioms sourceMap1123swap_checked
#print axioms fusedMap1123swap_checked
#print axioms certified1123swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
