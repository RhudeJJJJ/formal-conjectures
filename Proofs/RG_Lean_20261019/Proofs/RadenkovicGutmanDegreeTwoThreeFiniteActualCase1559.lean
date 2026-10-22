/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1559 : Family 10 := level10.get ⟨478,by decide⟩
def sourceMap1559 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1559 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1559_checked : acceptsGraphIso
    (source (graph core1559) (root 10) 0 2) DegreeTwoThreeSpectrum2844.graph sourceMap1559=true := by decide +kernel
theorem fusedMap1559_checked : acceptsGraphIso
    (fused (graph core1559) (root 10) 0 2) DegreeTwoThreeSpectrum2981.graph fusedMap1559=true := by decide +kernel
theorem certified1559 : Certified (graph core1559) (root 10) 0 2 :=
  of_native_maps core1559 DegreeTwoThreeSpectrum2844.graph DegreeTwoThreeSpectrum2981.graph
    sourceMap1559 fusedMap1559 sourceMap1559_checked fusedMap1559_checked
    DegreeTwoThreeFiniteComparisons.comparison1559
#print axioms sourceMap1559_checked
#print axioms fusedMap1559_checked
#print axioms certified1559
def sourceMap1559swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1559swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1559swap_checked : acceptsGraphIso
    (source (graph core1559) (root 10) 2 0) DegreeTwoThreeSpectrum2844.graph sourceMap1559swap=true := by decide +kernel
theorem fusedMap1559swap_checked : acceptsGraphIso
    (fused (graph core1559) (root 10) 2 0) DegreeTwoThreeSpectrum2981.graph fusedMap1559swap=true := by decide +kernel
theorem certified1559swap : Certified (graph core1559) (root 10) 2 0 :=
  of_native_maps core1559 DegreeTwoThreeSpectrum2844.graph DegreeTwoThreeSpectrum2981.graph
    sourceMap1559swap fusedMap1559swap sourceMap1559swap_checked fusedMap1559swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1559
#print axioms sourceMap1559swap_checked
#print axioms fusedMap1559swap_checked
#print axioms certified1559swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
