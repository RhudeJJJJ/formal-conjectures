/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1521 : Family 10 := level10.get ⟨361,by decide⟩
def sourceMap1521 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,11,12,13,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1521 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,12,13,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1521_checked : acceptsGraphIso
    (source (graph core1521) (root 10) 0 2) DegreeTwoThreeSpectrum2798.graph sourceMap1521=true := by decide +kernel
theorem fusedMap1521_checked : acceptsGraphIso
    (fused (graph core1521) (root 10) 0 2) DegreeTwoThreeSpectrum2811.graph fusedMap1521=true := by decide +kernel
theorem certified1521 : Certified (graph core1521) (root 10) 0 2 :=
  of_native_maps core1521 DegreeTwoThreeSpectrum2798.graph DegreeTwoThreeSpectrum2811.graph
    sourceMap1521 fusedMap1521 sourceMap1521_checked fusedMap1521_checked
    DegreeTwoThreeFiniteComparisons.comparison1521
#print axioms sourceMap1521_checked
#print axioms fusedMap1521_checked
#print axioms certified1521
def sourceMap1521swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,11,12,8,9,10,13] (sourceLabel 10 2 0 v)
def fusedMap1521swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,12,13,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1521swap_checked : acceptsGraphIso
    (source (graph core1521) (root 10) 2 0) DegreeTwoThreeSpectrum2798.graph sourceMap1521swap=true := by decide +kernel
theorem fusedMap1521swap_checked : acceptsGraphIso
    (fused (graph core1521) (root 10) 2 0) DegreeTwoThreeSpectrum2811.graph fusedMap1521swap=true := by decide +kernel
theorem certified1521swap : Certified (graph core1521) (root 10) 2 0 :=
  of_native_maps core1521 DegreeTwoThreeSpectrum2798.graph DegreeTwoThreeSpectrum2811.graph
    sourceMap1521swap fusedMap1521swap sourceMap1521swap_checked fusedMap1521swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1521
#print axioms sourceMap1521swap_checked
#print axioms fusedMap1521swap_checked
#print axioms certified1521swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
