/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1774 : Family 10 := level10.get ⟨1071,by decide⟩
def sourceMap1774 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1774 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1774_checked : acceptsGraphIso
    (source (graph core1774) (root 10) 0 2) DegreeTwoThreeSpectrum3124.graph sourceMap1774=true := by decide +kernel
theorem fusedMap1774_checked : acceptsGraphIso
    (fused (graph core1774) (root 10) 0 2) DegreeTwoThreeSpectrum3125.graph fusedMap1774=true := by decide +kernel
theorem certified1774 : Certified (graph core1774) (root 10) 0 2 :=
  of_native_maps core1774 DegreeTwoThreeSpectrum3124.graph DegreeTwoThreeSpectrum3125.graph
    sourceMap1774 fusedMap1774 sourceMap1774_checked fusedMap1774_checked
    DegreeTwoThreeFiniteComparisons.comparison1774
#print axioms sourceMap1774_checked
#print axioms fusedMap1774_checked
#print axioms certified1774
def sourceMap1774swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1774swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1774swap_checked : acceptsGraphIso
    (source (graph core1774) (root 10) 2 0) DegreeTwoThreeSpectrum3124.graph sourceMap1774swap=true := by decide +kernel
theorem fusedMap1774swap_checked : acceptsGraphIso
    (fused (graph core1774) (root 10) 2 0) DegreeTwoThreeSpectrum3125.graph fusedMap1774swap=true := by decide +kernel
theorem certified1774swap : Certified (graph core1774) (root 10) 2 0 :=
  of_native_maps core1774 DegreeTwoThreeSpectrum3124.graph DegreeTwoThreeSpectrum3125.graph
    sourceMap1774swap fusedMap1774swap sourceMap1774swap_checked fusedMap1774swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1774
#print axioms sourceMap1774swap_checked
#print axioms fusedMap1774swap_checked
#print axioms certified1774swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
