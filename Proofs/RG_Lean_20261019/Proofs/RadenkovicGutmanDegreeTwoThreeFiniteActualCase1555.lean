/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1555 : Family 10 := level10.get ⟨464,by decide⟩
def sourceMap1555 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1555 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1555_checked : acceptsGraphIso
    (source (graph core1555) (root 10) 0 2) DegreeTwoThreeSpectrum2833.graph sourceMap1555=true := by decide +kernel
theorem fusedMap1555_checked : acceptsGraphIso
    (fused (graph core1555) (root 10) 0 2) DegreeTwoThreeSpectrum2970.graph fusedMap1555=true := by decide +kernel
theorem certified1555 : Certified (graph core1555) (root 10) 0 2 :=
  of_native_maps core1555 DegreeTwoThreeSpectrum2833.graph DegreeTwoThreeSpectrum2970.graph
    sourceMap1555 fusedMap1555 sourceMap1555_checked fusedMap1555_checked
    DegreeTwoThreeFiniteComparisons.comparison1555
#print axioms sourceMap1555_checked
#print axioms fusedMap1555_checked
#print axioms certified1555
def sourceMap1555swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1555swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1555swap_checked : acceptsGraphIso
    (source (graph core1555) (root 10) 2 0) DegreeTwoThreeSpectrum2833.graph sourceMap1555swap=true := by decide +kernel
theorem fusedMap1555swap_checked : acceptsGraphIso
    (fused (graph core1555) (root 10) 2 0) DegreeTwoThreeSpectrum2970.graph fusedMap1555swap=true := by decide +kernel
theorem certified1555swap : Certified (graph core1555) (root 10) 2 0 :=
  of_native_maps core1555 DegreeTwoThreeSpectrum2833.graph DegreeTwoThreeSpectrum2970.graph
    sourceMap1555swap fusedMap1555swap sourceMap1555swap_checked fusedMap1555swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1555
#print axioms sourceMap1555swap_checked
#print axioms fusedMap1555swap_checked
#print axioms certified1555swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
