/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1234 : Family 9 := level9.get ⟨171,by decide⟩
def sourceMap1234 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,12,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1234 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1234_checked : acceptsGraphIso
    (source (graph core1234) (root 9) 0 2) DegreeTwoThreeSpectrum2034.graph sourceMap1234=true := by decide +kernel
theorem fusedMap1234_checked : acceptsGraphIso
    (fused (graph core1234) (root 9) 0 2) DegreeTwoThreeSpectrum1770.graph fusedMap1234=true := by decide +kernel
theorem certified1234 : Certified (graph core1234) (root 9) 0 2 :=
  of_native_maps core1234 DegreeTwoThreeSpectrum2034.graph DegreeTwoThreeSpectrum1770.graph
    sourceMap1234 fusedMap1234 sourceMap1234_checked fusedMap1234_checked
    DegreeTwoThreeFiniteComparisons.comparison1234
#print axioms sourceMap1234_checked
#print axioms fusedMap1234_checked
#print axioms certified1234
def sourceMap1234swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,11,8,9,10,12] (sourceLabel 9 2 0 v)
def fusedMap1234swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1234swap_checked : acceptsGraphIso
    (source (graph core1234) (root 9) 2 0) DegreeTwoThreeSpectrum2034.graph sourceMap1234swap=true := by decide +kernel
theorem fusedMap1234swap_checked : acceptsGraphIso
    (fused (graph core1234) (root 9) 2 0) DegreeTwoThreeSpectrum1770.graph fusedMap1234swap=true := by decide +kernel
theorem certified1234swap : Certified (graph core1234) (root 9) 2 0 :=
  of_native_maps core1234 DegreeTwoThreeSpectrum2034.graph DegreeTwoThreeSpectrum1770.graph
    sourceMap1234swap fusedMap1234swap sourceMap1234swap_checked fusedMap1234swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1234
#print axioms sourceMap1234swap_checked
#print axioms fusedMap1234swap_checked
#print axioms certified1234swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
