/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1556 : Family 10 := level10.get ⟨471,by decide⟩
def sourceMap1556 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1556 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1556_checked : acceptsGraphIso
    (source (graph core1556) (root 10) 0 2) DegreeTwoThreeSpectrum2879.graph sourceMap1556=true := by decide +kernel
theorem fusedMap1556_checked : acceptsGraphIso
    (fused (graph core1556) (root 10) 0 2) DegreeTwoThreeSpectrum2989.graph fusedMap1556=true := by decide +kernel
theorem certified1556 : Certified (graph core1556) (root 10) 0 2 :=
  of_native_maps core1556 DegreeTwoThreeSpectrum2879.graph DegreeTwoThreeSpectrum2989.graph
    sourceMap1556 fusedMap1556 sourceMap1556_checked fusedMap1556_checked
    DegreeTwoThreeFiniteComparisons.comparison1556
#print axioms sourceMap1556_checked
#print axioms fusedMap1556_checked
#print axioms certified1556
def sourceMap1556swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1556swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1556swap_checked : acceptsGraphIso
    (source (graph core1556) (root 10) 2 0) DegreeTwoThreeSpectrum2879.graph sourceMap1556swap=true := by decide +kernel
theorem fusedMap1556swap_checked : acceptsGraphIso
    (fused (graph core1556) (root 10) 2 0) DegreeTwoThreeSpectrum2989.graph fusedMap1556swap=true := by decide +kernel
theorem certified1556swap : Certified (graph core1556) (root 10) 2 0 :=
  of_native_maps core1556 DegreeTwoThreeSpectrum2879.graph DegreeTwoThreeSpectrum2989.graph
    sourceMap1556swap fusedMap1556swap sourceMap1556swap_checked fusedMap1556swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1556
#print axioms sourceMap1556swap_checked
#print axioms fusedMap1556swap_checked
#print axioms certified1556swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
