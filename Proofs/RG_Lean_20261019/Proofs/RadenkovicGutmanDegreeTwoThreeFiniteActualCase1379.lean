/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1379 : Family 9 := level9.get ⟨552,by decide⟩
def sourceMap1379 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1379 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1379_checked : acceptsGraphIso
    (source (graph core1379) (root 9) 0 2) DegreeTwoThreeSpectrum2250.graph sourceMap1379=true := by decide +kernel
theorem fusedMap1379_checked : acceptsGraphIso
    (fused (graph core1379) (root 9) 0 2) DegreeTwoThreeSpectrum1933.graph fusedMap1379=true := by decide +kernel
theorem certified1379 : Certified (graph core1379) (root 9) 0 2 :=
  of_native_maps core1379 DegreeTwoThreeSpectrum2250.graph DegreeTwoThreeSpectrum1933.graph
    sourceMap1379 fusedMap1379 sourceMap1379_checked fusedMap1379_checked
    DegreeTwoThreeFiniteComparisons.comparison1379
#print axioms sourceMap1379_checked
#print axioms fusedMap1379_checked
#print axioms certified1379
def sourceMap1379swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1379swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1379swap_checked : acceptsGraphIso
    (source (graph core1379) (root 9) 2 0) DegreeTwoThreeSpectrum2250.graph sourceMap1379swap=true := by decide +kernel
theorem fusedMap1379swap_checked : acceptsGraphIso
    (fused (graph core1379) (root 9) 2 0) DegreeTwoThreeSpectrum1933.graph fusedMap1379swap=true := by decide +kernel
theorem certified1379swap : Certified (graph core1379) (root 9) 2 0 :=
  of_native_maps core1379 DegreeTwoThreeSpectrum2250.graph DegreeTwoThreeSpectrum1933.graph
    sourceMap1379swap fusedMap1379swap sourceMap1379swap_checked fusedMap1379swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1379
#print axioms sourceMap1379swap_checked
#print axioms fusedMap1379swap_checked
#print axioms certified1379swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
