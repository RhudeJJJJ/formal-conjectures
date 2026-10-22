/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1549 : Family 10 := level10.get ⟨452,by decide⟩
def sourceMap1549 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1549 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1549_checked : acceptsGraphIso
    (source (graph core1549) (root 10) 0 2) DegreeTwoThreeSpectrum2893.graph sourceMap1549=true := by decide +kernel
theorem fusedMap1549_checked : acceptsGraphIso
    (fused (graph core1549) (root 10) 0 2) DegreeTwoThreeSpectrum2985.graph fusedMap1549=true := by decide +kernel
theorem certified1549 : Certified (graph core1549) (root 10) 0 2 :=
  of_native_maps core1549 DegreeTwoThreeSpectrum2893.graph DegreeTwoThreeSpectrum2985.graph
    sourceMap1549 fusedMap1549 sourceMap1549_checked fusedMap1549_checked
    DegreeTwoThreeFiniteComparisons.comparison1549
#print axioms sourceMap1549_checked
#print axioms fusedMap1549_checked
#print axioms certified1549
def sourceMap1549swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1549swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1549swap_checked : acceptsGraphIso
    (source (graph core1549) (root 10) 2 0) DegreeTwoThreeSpectrum2893.graph sourceMap1549swap=true := by decide +kernel
theorem fusedMap1549swap_checked : acceptsGraphIso
    (fused (graph core1549) (root 10) 2 0) DegreeTwoThreeSpectrum2985.graph fusedMap1549swap=true := by decide +kernel
theorem certified1549swap : Certified (graph core1549) (root 10) 2 0 :=
  of_native_maps core1549 DegreeTwoThreeSpectrum2893.graph DegreeTwoThreeSpectrum2985.graph
    sourceMap1549swap fusedMap1549swap sourceMap1549swap_checked fusedMap1549swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1549
#print axioms sourceMap1549swap_checked
#print axioms fusedMap1549swap_checked
#print axioms certified1549swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
