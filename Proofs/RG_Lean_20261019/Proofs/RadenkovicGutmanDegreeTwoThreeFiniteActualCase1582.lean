/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1582 : Family 10 := level10.get ⟨550,by decide⟩
def sourceMap1582 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1582 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1582_checked : acceptsGraphIso
    (source (graph core1582) (root 10) 0 2) DegreeTwoThreeSpectrum3150.graph sourceMap1582=true := by decide +kernel
theorem fusedMap1582_checked : acceptsGraphIso
    (fused (graph core1582) (root 10) 0 2) DegreeTwoThreeSpectrum2487.graph fusedMap1582=true := by decide +kernel
theorem certified1582 : Certified (graph core1582) (root 10) 0 2 :=
  of_native_maps core1582 DegreeTwoThreeSpectrum3150.graph DegreeTwoThreeSpectrum2487.graph
    sourceMap1582 fusedMap1582 sourceMap1582_checked fusedMap1582_checked
    DegreeTwoThreeFiniteComparisons.comparison1582
#print axioms sourceMap1582_checked
#print axioms fusedMap1582_checked
#print axioms certified1582
def sourceMap1582swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1582swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1582swap_checked : acceptsGraphIso
    (source (graph core1582) (root 10) 2 0) DegreeTwoThreeSpectrum3150.graph sourceMap1582swap=true := by decide +kernel
theorem fusedMap1582swap_checked : acceptsGraphIso
    (fused (graph core1582) (root 10) 2 0) DegreeTwoThreeSpectrum2487.graph fusedMap1582swap=true := by decide +kernel
theorem certified1582swap : Certified (graph core1582) (root 10) 2 0 :=
  of_native_maps core1582 DegreeTwoThreeSpectrum3150.graph DegreeTwoThreeSpectrum2487.graph
    sourceMap1582swap fusedMap1582swap sourceMap1582swap_checked fusedMap1582swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1582
#print axioms sourceMap1582swap_checked
#print axioms fusedMap1582swap_checked
#print axioms certified1582swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
