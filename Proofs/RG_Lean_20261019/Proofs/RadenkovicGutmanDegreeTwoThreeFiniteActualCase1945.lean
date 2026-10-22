/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1945 : Family 10 := level10.get ⟨1475,by decide⟩
def sourceMap1945 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1945 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1945_checked : acceptsGraphIso
    (source (graph core1945) (root 10) 0 2) DegreeTwoThreeSpectrum3717.graph sourceMap1945=true := by decide +kernel
theorem fusedMap1945_checked : acceptsGraphIso
    (fused (graph core1945) (root 10) 0 2) DegreeTwoThreeSpectrum3716.graph fusedMap1945=true := by decide +kernel
theorem certified1945 : Certified (graph core1945) (root 10) 0 2 :=
  of_native_maps core1945 DegreeTwoThreeSpectrum3717.graph DegreeTwoThreeSpectrum3716.graph
    sourceMap1945 fusedMap1945 sourceMap1945_checked fusedMap1945_checked
    DegreeTwoThreeFiniteComparisons.comparison1945
#print axioms sourceMap1945_checked
#print axioms fusedMap1945_checked
#print axioms certified1945
def sourceMap1945swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1945swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1945swap_checked : acceptsGraphIso
    (source (graph core1945) (root 10) 2 0) DegreeTwoThreeSpectrum3717.graph sourceMap1945swap=true := by decide +kernel
theorem fusedMap1945swap_checked : acceptsGraphIso
    (fused (graph core1945) (root 10) 2 0) DegreeTwoThreeSpectrum3716.graph fusedMap1945swap=true := by decide +kernel
theorem certified1945swap : Certified (graph core1945) (root 10) 2 0 :=
  of_native_maps core1945 DegreeTwoThreeSpectrum3717.graph DegreeTwoThreeSpectrum3716.graph
    sourceMap1945swap fusedMap1945swap sourceMap1945swap_checked fusedMap1945swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1945
#print axioms sourceMap1945swap_checked
#print axioms fusedMap1945swap_checked
#print axioms certified1945swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
