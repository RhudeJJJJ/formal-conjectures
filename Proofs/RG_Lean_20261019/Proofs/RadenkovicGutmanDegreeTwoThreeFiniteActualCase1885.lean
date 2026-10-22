/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1885 : Family 10 := level10.get ⟨1337,by decide⟩
def sourceMap1885 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1885 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1885_checked : acceptsGraphIso
    (source (graph core1885) (root 10) 0 2) DegreeTwoThreeSpectrum3292.graph sourceMap1885=true := by decide +kernel
theorem fusedMap1885_checked : acceptsGraphIso
    (fused (graph core1885) (root 10) 0 2) DegreeTwoThreeSpectrum3524.graph fusedMap1885=true := by decide +kernel
theorem certified1885 : Certified (graph core1885) (root 10) 0 2 :=
  of_native_maps core1885 DegreeTwoThreeSpectrum3292.graph DegreeTwoThreeSpectrum3524.graph
    sourceMap1885 fusedMap1885 sourceMap1885_checked fusedMap1885_checked
    DegreeTwoThreeFiniteComparisons.comparison1885
#print axioms sourceMap1885_checked
#print axioms fusedMap1885_checked
#print axioms certified1885
def sourceMap1885swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1885swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1885swap_checked : acceptsGraphIso
    (source (graph core1885) (root 10) 2 0) DegreeTwoThreeSpectrum3292.graph sourceMap1885swap=true := by decide +kernel
theorem fusedMap1885swap_checked : acceptsGraphIso
    (fused (graph core1885) (root 10) 2 0) DegreeTwoThreeSpectrum3524.graph fusedMap1885swap=true := by decide +kernel
theorem certified1885swap : Certified (graph core1885) (root 10) 2 0 :=
  of_native_maps core1885 DegreeTwoThreeSpectrum3292.graph DegreeTwoThreeSpectrum3524.graph
    sourceMap1885swap fusedMap1885swap sourceMap1885swap_checked fusedMap1885swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1885
#print axioms sourceMap1885swap_checked
#print axioms fusedMap1885swap_checked
#print axioms certified1885swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
