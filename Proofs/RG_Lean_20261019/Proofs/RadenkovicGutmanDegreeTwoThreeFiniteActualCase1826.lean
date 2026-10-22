/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1826 : Family 10 := level10.get ⟨1198,by decide⟩
def sourceMap1826 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1826 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1826_checked : acceptsGraphIso
    (source (graph core1826) (root 10) 0 2) DegreeTwoThreeSpectrum3316.graph sourceMap1826=true := by decide +kernel
theorem fusedMap1826_checked : acceptsGraphIso
    (fused (graph core1826) (root 10) 0 2) DegreeTwoThreeSpectrum3318.graph fusedMap1826=true := by decide +kernel
theorem certified1826 : Certified (graph core1826) (root 10) 0 2 :=
  of_native_maps core1826 DegreeTwoThreeSpectrum3316.graph DegreeTwoThreeSpectrum3318.graph
    sourceMap1826 fusedMap1826 sourceMap1826_checked fusedMap1826_checked
    DegreeTwoThreeFiniteComparisons.comparison1826
#print axioms sourceMap1826_checked
#print axioms fusedMap1826_checked
#print axioms certified1826
def sourceMap1826swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1826swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1826swap_checked : acceptsGraphIso
    (source (graph core1826) (root 10) 2 0) DegreeTwoThreeSpectrum3316.graph sourceMap1826swap=true := by decide +kernel
theorem fusedMap1826swap_checked : acceptsGraphIso
    (fused (graph core1826) (root 10) 2 0) DegreeTwoThreeSpectrum3318.graph fusedMap1826swap=true := by decide +kernel
theorem certified1826swap : Certified (graph core1826) (root 10) 2 0 :=
  of_native_maps core1826 DegreeTwoThreeSpectrum3316.graph DegreeTwoThreeSpectrum3318.graph
    sourceMap1826swap fusedMap1826swap sourceMap1826swap_checked fusedMap1826swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1826
#print axioms sourceMap1826swap_checked
#print axioms fusedMap1826swap_checked
#print axioms certified1826swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
