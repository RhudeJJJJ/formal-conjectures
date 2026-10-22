/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1236 : Family 9 := level9.get ⟨178,by decide⟩
def sourceMap1236 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1236 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1236_checked : acceptsGraphIso
    (source (graph core1236) (root 9) 0 2) DegreeTwoThreeSpectrum2053.graph sourceMap1236=true := by decide +kernel
theorem fusedMap1236_checked : acceptsGraphIso
    (fused (graph core1236) (root 9) 0 2) DegreeTwoThreeSpectrum1778.graph fusedMap1236=true := by decide +kernel
theorem certified1236 : Certified (graph core1236) (root 9) 0 2 :=
  of_native_maps core1236 DegreeTwoThreeSpectrum2053.graph DegreeTwoThreeSpectrum1778.graph
    sourceMap1236 fusedMap1236 sourceMap1236_checked fusedMap1236_checked
    DegreeTwoThreeFiniteComparisons.comparison1236
#print axioms sourceMap1236_checked
#print axioms fusedMap1236_checked
#print axioms certified1236
def sourceMap1236swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1236swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1236swap_checked : acceptsGraphIso
    (source (graph core1236) (root 9) 2 0) DegreeTwoThreeSpectrum2053.graph sourceMap1236swap=true := by decide +kernel
theorem fusedMap1236swap_checked : acceptsGraphIso
    (fused (graph core1236) (root 9) 2 0) DegreeTwoThreeSpectrum1778.graph fusedMap1236swap=true := by decide +kernel
theorem certified1236swap : Certified (graph core1236) (root 9) 2 0 :=
  of_native_maps core1236 DegreeTwoThreeSpectrum2053.graph DegreeTwoThreeSpectrum1778.graph
    sourceMap1236swap fusedMap1236swap sourceMap1236swap_checked fusedMap1236swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1236
#print axioms sourceMap1236swap_checked
#print axioms fusedMap1236swap_checked
#print axioms certified1236swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
