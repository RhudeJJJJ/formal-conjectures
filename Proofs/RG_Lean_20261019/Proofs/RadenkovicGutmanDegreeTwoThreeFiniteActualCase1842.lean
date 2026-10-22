/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1842 : Family 10 := level10.get ⟨1228,by decide⟩
def sourceMap1842 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1842 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1842_checked : acceptsGraphIso
    (source (graph core1842) (root 10) 0 2) DegreeTwoThreeSpectrum3351.graph sourceMap1842=true := by decide +kernel
theorem fusedMap1842_checked : acceptsGraphIso
    (fused (graph core1842) (root 10) 0 2) DegreeTwoThreeSpectrum3373.graph fusedMap1842=true := by decide +kernel
theorem certified1842 : Certified (graph core1842) (root 10) 0 2 :=
  of_native_maps core1842 DegreeTwoThreeSpectrum3351.graph DegreeTwoThreeSpectrum3373.graph
    sourceMap1842 fusedMap1842 sourceMap1842_checked fusedMap1842_checked
    DegreeTwoThreeFiniteComparisons.comparison1842
#print axioms sourceMap1842_checked
#print axioms fusedMap1842_checked
#print axioms certified1842
def sourceMap1842swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1842swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1842swap_checked : acceptsGraphIso
    (source (graph core1842) (root 10) 2 0) DegreeTwoThreeSpectrum3351.graph sourceMap1842swap=true := by decide +kernel
theorem fusedMap1842swap_checked : acceptsGraphIso
    (fused (graph core1842) (root 10) 2 0) DegreeTwoThreeSpectrum3373.graph fusedMap1842swap=true := by decide +kernel
theorem certified1842swap : Certified (graph core1842) (root 10) 2 0 :=
  of_native_maps core1842 DegreeTwoThreeSpectrum3351.graph DegreeTwoThreeSpectrum3373.graph
    sourceMap1842swap fusedMap1842swap sourceMap1842swap_checked fusedMap1842swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1842
#print axioms sourceMap1842swap_checked
#print axioms fusedMap1842swap_checked
#print axioms certified1842swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
