/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1252 : Family 9 := level9.get ⟨224,by decide⟩
def sourceMap1252 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1252 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1252_checked : acceptsGraphIso
    (source (graph core1252) (root 9) 0 2) DegreeTwoThreeSpectrum2137.graph sourceMap1252=true := by decide +kernel
theorem fusedMap1252_checked : acceptsGraphIso
    (fused (graph core1252) (root 9) 0 2) DegreeTwoThreeSpectrum1828.graph fusedMap1252=true := by decide +kernel
theorem certified1252 : Certified (graph core1252) (root 9) 0 2 :=
  of_native_maps core1252 DegreeTwoThreeSpectrum2137.graph DegreeTwoThreeSpectrum1828.graph
    sourceMap1252 fusedMap1252 sourceMap1252_checked fusedMap1252_checked
    DegreeTwoThreeFiniteComparisons.comparison1252
#print axioms sourceMap1252_checked
#print axioms fusedMap1252_checked
#print axioms certified1252
def sourceMap1252swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1252swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1252swap_checked : acceptsGraphIso
    (source (graph core1252) (root 9) 2 0) DegreeTwoThreeSpectrum2137.graph sourceMap1252swap=true := by decide +kernel
theorem fusedMap1252swap_checked : acceptsGraphIso
    (fused (graph core1252) (root 9) 2 0) DegreeTwoThreeSpectrum1828.graph fusedMap1252swap=true := by decide +kernel
theorem certified1252swap : Certified (graph core1252) (root 9) 2 0 :=
  of_native_maps core1252 DegreeTwoThreeSpectrum2137.graph DegreeTwoThreeSpectrum1828.graph
    sourceMap1252swap fusedMap1252swap sourceMap1252swap_checked fusedMap1252swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1252
#print axioms sourceMap1252swap_checked
#print axioms fusedMap1252swap_checked
#print axioms certified1252swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
