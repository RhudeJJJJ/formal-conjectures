/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1299 : Family 9 := level9.get ⟨351,by decide⟩
def sourceMap1299 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1299 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1299_checked : acceptsGraphIso
    (source (graph core1299) (root 9) 0 2) DegreeTwoThreeSpectrum1982.graph sourceMap1299=true := by decide +kernel
theorem fusedMap1299_checked : acceptsGraphIso
    (fused (graph core1299) (root 9) 0 2) DegreeTwoThreeSpectrum1986.graph fusedMap1299=true := by decide +kernel
theorem certified1299 : Certified (graph core1299) (root 9) 0 2 :=
  of_native_maps core1299 DegreeTwoThreeSpectrum1982.graph DegreeTwoThreeSpectrum1986.graph
    sourceMap1299 fusedMap1299 sourceMap1299_checked fusedMap1299_checked
    DegreeTwoThreeFiniteComparisons.comparison1299
#print axioms sourceMap1299_checked
#print axioms fusedMap1299_checked
#print axioms certified1299
def sourceMap1299swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9,13] (sourceLabel 9 2 0 v)
def fusedMap1299swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1299swap_checked : acceptsGraphIso
    (source (graph core1299) (root 9) 2 0) DegreeTwoThreeSpectrum1982.graph sourceMap1299swap=true := by decide +kernel
theorem fusedMap1299swap_checked : acceptsGraphIso
    (fused (graph core1299) (root 9) 2 0) DegreeTwoThreeSpectrum1986.graph fusedMap1299swap=true := by decide +kernel
theorem certified1299swap : Certified (graph core1299) (root 9) 2 0 :=
  of_native_maps core1299 DegreeTwoThreeSpectrum1982.graph DegreeTwoThreeSpectrum1986.graph
    sourceMap1299swap fusedMap1299swap sourceMap1299swap_checked fusedMap1299swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1299
#print axioms sourceMap1299swap_checked
#print axioms fusedMap1299swap_checked
#print axioms certified1299swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
