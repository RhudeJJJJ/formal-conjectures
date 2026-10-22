/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1313 : Family 9 := level9.get ⟨392,by decide⟩
def sourceMap1313 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1313 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1313_checked : acceptsGraphIso
    (source (graph core1313) (root 9) 0 2) DegreeTwoThreeSpectrum2047.graph sourceMap1313=true := by decide +kernel
theorem fusedMap1313_checked : acceptsGraphIso
    (fused (graph core1313) (root 9) 0 2) DegreeTwoThreeSpectrum2048.graph fusedMap1313=true := by decide +kernel
theorem certified1313 : Certified (graph core1313) (root 9) 0 2 :=
  of_native_maps core1313 DegreeTwoThreeSpectrum2047.graph DegreeTwoThreeSpectrum2048.graph
    sourceMap1313 fusedMap1313 sourceMap1313_checked fusedMap1313_checked
    DegreeTwoThreeFiniteComparisons.comparison1313
#print axioms sourceMap1313_checked
#print axioms fusedMap1313_checked
#print axioms certified1313
def sourceMap1313swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1313swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1313swap_checked : acceptsGraphIso
    (source (graph core1313) (root 9) 2 0) DegreeTwoThreeSpectrum2047.graph sourceMap1313swap=true := by decide +kernel
theorem fusedMap1313swap_checked : acceptsGraphIso
    (fused (graph core1313) (root 9) 2 0) DegreeTwoThreeSpectrum2048.graph fusedMap1313swap=true := by decide +kernel
theorem certified1313swap : Certified (graph core1313) (root 9) 2 0 :=
  of_native_maps core1313 DegreeTwoThreeSpectrum2047.graph DegreeTwoThreeSpectrum2048.graph
    sourceMap1313swap fusedMap1313swap sourceMap1313swap_checked fusedMap1313swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1313
#print axioms sourceMap1313swap_checked
#print axioms fusedMap1313swap_checked
#print axioms certified1313swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
