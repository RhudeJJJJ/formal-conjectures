/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1442 : Family 10 := level10.get ⟨72,by decide⟩
def sourceMap1442 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1442 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1442_checked : acceptsGraphIso
    (source (graph core1442) (root 10) 0 2) DegreeTwoThreeSpectrum2596.graph sourceMap1442=true := by decide +kernel
theorem fusedMap1442_checked : acceptsGraphIso
    (fused (graph core1442) (root 10) 0 2) DegreeTwoThreeSpectrum2332.graph fusedMap1442=true := by decide +kernel
theorem certified1442 : Certified (graph core1442) (root 10) 0 2 :=
  of_native_maps core1442 DegreeTwoThreeSpectrum2596.graph DegreeTwoThreeSpectrum2332.graph
    sourceMap1442 fusedMap1442 sourceMap1442_checked fusedMap1442_checked
    DegreeTwoThreeFiniteComparisons.comparison1442
#print axioms sourceMap1442_checked
#print axioms fusedMap1442_checked
#print axioms certified1442
def sourceMap1442swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1442swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1442swap_checked : acceptsGraphIso
    (source (graph core1442) (root 10) 2 0) DegreeTwoThreeSpectrum2596.graph sourceMap1442swap=true := by decide +kernel
theorem fusedMap1442swap_checked : acceptsGraphIso
    (fused (graph core1442) (root 10) 2 0) DegreeTwoThreeSpectrum2332.graph fusedMap1442swap=true := by decide +kernel
theorem certified1442swap : Certified (graph core1442) (root 10) 2 0 :=
  of_native_maps core1442 DegreeTwoThreeSpectrum2596.graph DegreeTwoThreeSpectrum2332.graph
    sourceMap1442swap fusedMap1442swap sourceMap1442swap_checked fusedMap1442swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1442
#print axioms sourceMap1442swap_checked
#print axioms fusedMap1442swap_checked
#print axioms certified1442swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
