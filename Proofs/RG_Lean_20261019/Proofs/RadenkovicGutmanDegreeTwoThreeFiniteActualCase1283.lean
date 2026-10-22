/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1283 : Family 9 := level9.get ⟨308,by decide⟩
def sourceMap1283 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1283 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (fusedLabel 9 0 2 v)
theorem sourceMap1283_checked : acceptsGraphIso
    (source (graph core1283) (root 9) 0 2) DegreeTwoThreeSpectrum1905.graph sourceMap1283=true := by decide +kernel
theorem fusedMap1283_checked : acceptsGraphIso
    (fused (graph core1283) (root 9) 0 2) DegreeTwoThreeSpectrum1902.graph fusedMap1283=true := by decide +kernel
theorem certified1283 : Certified (graph core1283) (root 9) 0 2 :=
  of_native_maps core1283 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1902.graph
    sourceMap1283 fusedMap1283 sourceMap1283_checked fusedMap1283_checked
    DegreeTwoThreeFiniteComparisons.comparison1283
#print axioms sourceMap1283_checked
#print axioms fusedMap1283_checked
#print axioms certified1283
def sourceMap1283swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1283swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (fusedLabel 9 2 0 v)
theorem sourceMap1283swap_checked : acceptsGraphIso
    (source (graph core1283) (root 9) 2 0) DegreeTwoThreeSpectrum1905.graph sourceMap1283swap=true := by decide +kernel
theorem fusedMap1283swap_checked : acceptsGraphIso
    (fused (graph core1283) (root 9) 2 0) DegreeTwoThreeSpectrum1902.graph fusedMap1283swap=true := by decide +kernel
theorem certified1283swap : Certified (graph core1283) (root 9) 2 0 :=
  of_native_maps core1283 DegreeTwoThreeSpectrum1905.graph DegreeTwoThreeSpectrum1902.graph
    sourceMap1283swap fusedMap1283swap sourceMap1283swap_checked fusedMap1283swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1283
#print axioms sourceMap1283swap_checked
#print axioms fusedMap1283swap_checked
#print axioms certified1283swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
