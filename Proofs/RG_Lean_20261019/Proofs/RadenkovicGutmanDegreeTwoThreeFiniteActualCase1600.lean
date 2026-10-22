/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1600 : Family 10 := level10.get ⟨606,by decide⟩
def sourceMap1600 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1600 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1600_checked : acceptsGraphIso
    (source (graph core1600) (root 10) 0 2) DegreeTwoThreeSpectrum3272.graph sourceMap1600=true := by decide +kernel
theorem fusedMap1600_checked : acceptsGraphIso
    (fused (graph core1600) (root 10) 0 2) DegreeTwoThreeSpectrum2546.graph fusedMap1600=true := by decide +kernel
theorem certified1600 : Certified (graph core1600) (root 10) 0 2 :=
  of_native_maps core1600 DegreeTwoThreeSpectrum3272.graph DegreeTwoThreeSpectrum2546.graph
    sourceMap1600 fusedMap1600 sourceMap1600_checked fusedMap1600_checked
    DegreeTwoThreeFiniteComparisons.comparison1600
#print axioms sourceMap1600_checked
#print axioms fusedMap1600_checked
#print axioms certified1600
def sourceMap1600swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1600swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1600swap_checked : acceptsGraphIso
    (source (graph core1600) (root 10) 2 0) DegreeTwoThreeSpectrum3272.graph sourceMap1600swap=true := by decide +kernel
theorem fusedMap1600swap_checked : acceptsGraphIso
    (fused (graph core1600) (root 10) 2 0) DegreeTwoThreeSpectrum2546.graph fusedMap1600swap=true := by decide +kernel
theorem certified1600swap : Certified (graph core1600) (root 10) 2 0 :=
  of_native_maps core1600 DegreeTwoThreeSpectrum3272.graph DegreeTwoThreeSpectrum2546.graph
    sourceMap1600swap fusedMap1600swap sourceMap1600swap_checked fusedMap1600swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1600
#print axioms sourceMap1600swap_checked
#print axioms fusedMap1600swap_checked
#print axioms certified1600swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
