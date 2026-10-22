/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1179 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap1179 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1179 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1179_checked : acceptsGraphIso
    (source (graph core1179) (root 8) 0 2) DegreeOneSmallSpectrum1926.graph sourceMap1179=true := by decide +kernel
theorem fusedMap1179_checked : acceptsGraphIso
    (fused (graph core1179) (root 8) 0 2) DegreeOneSmallSpectrum1314.graph fusedMap1179=true := by decide +kernel
theorem certified1179 : Certified (graph core1179) (root 8) 0 2 :=
  of_native_maps core1179 DegreeOneSmallSpectrum1926.graph DegreeOneSmallSpectrum1314.graph
    sourceMap1179 fusedMap1179 sourceMap1179_checked fusedMap1179_checked
    DegreeTwoThreeFiniteComparisons.comparison1179
#print axioms sourceMap1179_checked
#print axioms fusedMap1179_checked
#print axioms certified1179
def sourceMap1179swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1179swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1179swap_checked : acceptsGraphIso
    (source (graph core1179) (root 8) 2 0) DegreeOneSmallSpectrum1926.graph sourceMap1179swap=true := by decide +kernel
theorem fusedMap1179swap_checked : acceptsGraphIso
    (fused (graph core1179) (root 8) 2 0) DegreeOneSmallSpectrum1314.graph fusedMap1179swap=true := by decide +kernel
theorem certified1179swap : Certified (graph core1179) (root 8) 2 0 :=
  of_native_maps core1179 DegreeOneSmallSpectrum1926.graph DegreeOneSmallSpectrum1314.graph
    sourceMap1179swap fusedMap1179swap sourceMap1179swap_checked fusedMap1179swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1179
#print axioms sourceMap1179swap_checked
#print axioms fusedMap1179swap_checked
#print axioms certified1179swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
