/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1237 : Family 9 := level9.get ⟨181,by decide⟩
def sourceMap1237 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1237 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1237_checked : acceptsGraphIso
    (source (graph core1237) (root 9) 0 2) DegreeTwoThreeSpectrum2058.graph sourceMap1237=true := by decide +kernel
theorem fusedMap1237_checked : acceptsGraphIso
    (fused (graph core1237) (root 9) 0 2) DegreeTwoThreeSpectrum1780.graph fusedMap1237=true := by decide +kernel
theorem certified1237 : Certified (graph core1237) (root 9) 0 2 :=
  of_native_maps core1237 DegreeTwoThreeSpectrum2058.graph DegreeTwoThreeSpectrum1780.graph
    sourceMap1237 fusedMap1237 sourceMap1237_checked fusedMap1237_checked
    DegreeTwoThreeFiniteComparisons.comparison1237
#print axioms sourceMap1237_checked
#print axioms fusedMap1237_checked
#print axioms certified1237
def sourceMap1237swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1237swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1237swap_checked : acceptsGraphIso
    (source (graph core1237) (root 9) 2 0) DegreeTwoThreeSpectrum2058.graph sourceMap1237swap=true := by decide +kernel
theorem fusedMap1237swap_checked : acceptsGraphIso
    (fused (graph core1237) (root 9) 2 0) DegreeTwoThreeSpectrum1780.graph fusedMap1237swap=true := by decide +kernel
theorem certified1237swap : Certified (graph core1237) (root 9) 2 0 :=
  of_native_maps core1237 DegreeTwoThreeSpectrum2058.graph DegreeTwoThreeSpectrum1780.graph
    sourceMap1237swap fusedMap1237swap sourceMap1237swap_checked fusedMap1237swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1237
#print axioms sourceMap1237swap_checked
#print axioms fusedMap1237swap_checked
#print axioms certified1237swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
