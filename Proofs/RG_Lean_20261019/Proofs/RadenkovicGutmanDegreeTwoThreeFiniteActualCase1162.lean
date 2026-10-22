/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1162 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap1162 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1162 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1162_checked : acceptsGraphIso
    (source (graph core1162) (root 8) 0 2) DegreeOneSmallSpectrum1654.graph sourceMap1162=true := by decide +kernel
theorem fusedMap1162_checked : acceptsGraphIso
    (fused (graph core1162) (root 8) 0 2) DegreeOneSmallSpectrum1017.graph fusedMap1162=true := by decide +kernel
theorem certified1162 : Certified (graph core1162) (root 8) 0 2 :=
  of_native_maps core1162 DegreeOneSmallSpectrum1654.graph DegreeOneSmallSpectrum1017.graph
    sourceMap1162 fusedMap1162 sourceMap1162_checked fusedMap1162_checked
    DegreeTwoThreeFiniteComparisons.comparison1162
#print axioms sourceMap1162_checked
#print axioms fusedMap1162_checked
#print axioms certified1162
def sourceMap1162swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1162swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1162swap_checked : acceptsGraphIso
    (source (graph core1162) (root 8) 2 0) DegreeOneSmallSpectrum1654.graph sourceMap1162swap=true := by decide +kernel
theorem fusedMap1162swap_checked : acceptsGraphIso
    (fused (graph core1162) (root 8) 2 0) DegreeOneSmallSpectrum1017.graph fusedMap1162swap=true := by decide +kernel
theorem certified1162swap : Certified (graph core1162) (root 8) 2 0 :=
  of_native_maps core1162 DegreeOneSmallSpectrum1654.graph DegreeOneSmallSpectrum1017.graph
    sourceMap1162swap fusedMap1162swap sourceMap1162swap_checked fusedMap1162swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1162
#print axioms sourceMap1162swap_checked
#print axioms fusedMap1162swap_checked
#print axioms certified1162swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
