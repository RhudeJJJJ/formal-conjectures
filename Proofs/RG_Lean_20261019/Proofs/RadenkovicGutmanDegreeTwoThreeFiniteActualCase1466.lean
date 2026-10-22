/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1466 : Family 10 := level10.get ⟨171,by decide⟩
def sourceMap1466 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1466 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1466_checked : acceptsGraphIso
    (source (graph core1466) (root 10) 0 2) DegreeTwoThreeSpectrum2909.graph sourceMap1466=true := by decide +kernel
theorem fusedMap1466_checked : acceptsGraphIso
    (fused (graph core1466) (root 10) 0 2) DegreeTwoThreeSpectrum2425.graph fusedMap1466=true := by decide +kernel
theorem certified1466 : Certified (graph core1466) (root 10) 0 2 :=
  of_native_maps core1466 DegreeTwoThreeSpectrum2909.graph DegreeTwoThreeSpectrum2425.graph
    sourceMap1466 fusedMap1466 sourceMap1466_checked fusedMap1466_checked
    DegreeTwoThreeFiniteComparisons.comparison1466
#print axioms sourceMap1466_checked
#print axioms fusedMap1466_checked
#print axioms certified1466
def sourceMap1466swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1466swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1466swap_checked : acceptsGraphIso
    (source (graph core1466) (root 10) 2 0) DegreeTwoThreeSpectrum2909.graph sourceMap1466swap=true := by decide +kernel
theorem fusedMap1466swap_checked : acceptsGraphIso
    (fused (graph core1466) (root 10) 2 0) DegreeTwoThreeSpectrum2425.graph fusedMap1466swap=true := by decide +kernel
theorem certified1466swap : Certified (graph core1466) (root 10) 2 0 :=
  of_native_maps core1466 DegreeTwoThreeSpectrum2909.graph DegreeTwoThreeSpectrum2425.graph
    sourceMap1466swap fusedMap1466swap sourceMap1466swap_checked fusedMap1466swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1466
#print axioms sourceMap1466swap_checked
#print axioms fusedMap1466swap_checked
#print axioms certified1466swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
