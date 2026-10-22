/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1921 : Family 10 := level10.get ⟨1423,by decide⟩
def sourceMap1921 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1921 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1921_checked : acceptsGraphIso
    (source (graph core1921) (root 10) 0 2) DegreeTwoThreeSpectrum3646.graph sourceMap1921=true := by decide +kernel
theorem fusedMap1921_checked : acceptsGraphIso
    (fused (graph core1921) (root 10) 0 2) DegreeTwoThreeSpectrum3648.graph fusedMap1921=true := by decide +kernel
theorem certified1921 : Certified (graph core1921) (root 10) 0 2 :=
  of_native_maps core1921 DegreeTwoThreeSpectrum3646.graph DegreeTwoThreeSpectrum3648.graph
    sourceMap1921 fusedMap1921 sourceMap1921_checked fusedMap1921_checked
    DegreeTwoThreeFiniteComparisons.comparison1921
#print axioms sourceMap1921_checked
#print axioms fusedMap1921_checked
#print axioms certified1921
def sourceMap1921swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1921swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1921swap_checked : acceptsGraphIso
    (source (graph core1921) (root 10) 2 0) DegreeTwoThreeSpectrum3646.graph sourceMap1921swap=true := by decide +kernel
theorem fusedMap1921swap_checked : acceptsGraphIso
    (fused (graph core1921) (root 10) 2 0) DegreeTwoThreeSpectrum3648.graph fusedMap1921swap=true := by decide +kernel
theorem certified1921swap : Certified (graph core1921) (root 10) 2 0 :=
  of_native_maps core1921 DegreeTwoThreeSpectrum3646.graph DegreeTwoThreeSpectrum3648.graph
    sourceMap1921swap fusedMap1921swap sourceMap1921swap_checked fusedMap1921swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1921
#print axioms sourceMap1921swap_checked
#print axioms fusedMap1921swap_checked
#print axioms certified1921swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
