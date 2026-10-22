/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1249 : Family 9 := level9.get ⟨216,by decide⟩
def sourceMap1249 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1249 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1249_checked : acceptsGraphIso
    (source (graph core1249) (root 9) 0 2) DegreeTwoThreeSpectrum2122.graph sourceMap1249=true := by decide +kernel
theorem fusedMap1249_checked : acceptsGraphIso
    (fused (graph core1249) (root 9) 0 2) DegreeTwoThreeSpectrum1819.graph fusedMap1249=true := by decide +kernel
theorem certified1249 : Certified (graph core1249) (root 9) 0 2 :=
  of_native_maps core1249 DegreeTwoThreeSpectrum2122.graph DegreeTwoThreeSpectrum1819.graph
    sourceMap1249 fusedMap1249 sourceMap1249_checked fusedMap1249_checked
    DegreeTwoThreeFiniteComparisons.comparison1249
#print axioms sourceMap1249_checked
#print axioms fusedMap1249_checked
#print axioms certified1249
def sourceMap1249swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1249swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1249swap_checked : acceptsGraphIso
    (source (graph core1249) (root 9) 2 0) DegreeTwoThreeSpectrum2122.graph sourceMap1249swap=true := by decide +kernel
theorem fusedMap1249swap_checked : acceptsGraphIso
    (fused (graph core1249) (root 9) 2 0) DegreeTwoThreeSpectrum1819.graph fusedMap1249swap=true := by decide +kernel
theorem certified1249swap : Certified (graph core1249) (root 9) 2 0 :=
  of_native_maps core1249 DegreeTwoThreeSpectrum2122.graph DegreeTwoThreeSpectrum1819.graph
    sourceMap1249swap fusedMap1249swap sourceMap1249swap_checked fusedMap1249swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1249
#print axioms sourceMap1249swap_checked
#print axioms fusedMap1249swap_checked
#print axioms certified1249swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
