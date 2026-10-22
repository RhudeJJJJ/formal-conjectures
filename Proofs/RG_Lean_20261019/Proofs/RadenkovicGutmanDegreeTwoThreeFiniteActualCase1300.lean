/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1300 : Family 9 := level9.get ⟨356,by decide⟩
def sourceMap1300 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1300 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1300_checked : acceptsGraphIso
    (source (graph core1300) (root 9) 0 2) DegreeTwoThreeSpectrum1991.graph sourceMap1300=true := by decide +kernel
theorem fusedMap1300_checked : acceptsGraphIso
    (fused (graph core1300) (root 9) 0 2) DegreeTwoThreeSpectrum1992.graph fusedMap1300=true := by decide +kernel
theorem certified1300 : Certified (graph core1300) (root 9) 0 2 :=
  of_native_maps core1300 DegreeTwoThreeSpectrum1991.graph DegreeTwoThreeSpectrum1992.graph
    sourceMap1300 fusedMap1300 sourceMap1300_checked fusedMap1300_checked
    DegreeTwoThreeFiniteComparisons.comparison1300
#print axioms sourceMap1300_checked
#print axioms fusedMap1300_checked
#print axioms certified1300
def sourceMap1300swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1300swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1300swap_checked : acceptsGraphIso
    (source (graph core1300) (root 9) 2 0) DegreeTwoThreeSpectrum1991.graph sourceMap1300swap=true := by decide +kernel
theorem fusedMap1300swap_checked : acceptsGraphIso
    (fused (graph core1300) (root 9) 2 0) DegreeTwoThreeSpectrum1992.graph fusedMap1300swap=true := by decide +kernel
theorem certified1300swap : Certified (graph core1300) (root 9) 2 0 :=
  of_native_maps core1300 DegreeTwoThreeSpectrum1991.graph DegreeTwoThreeSpectrum1992.graph
    sourceMap1300swap fusedMap1300swap sourceMap1300swap_checked fusedMap1300swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1300
#print axioms sourceMap1300swap_checked
#print axioms fusedMap1300swap_checked
#print axioms certified1300swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
