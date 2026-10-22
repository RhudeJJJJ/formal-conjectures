/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1457 : Family 10 := level10.get ⟨139,by decide⟩
def sourceMap1457 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1457 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1457_checked : acceptsGraphIso
    (source (graph core1457) (root 10) 0 2) DegreeTwoThreeSpectrum2900.graph sourceMap1457=true := by decide +kernel
theorem fusedMap1457_checked : acceptsGraphIso
    (fused (graph core1457) (root 10) 0 2) DegreeTwoThreeSpectrum2401.graph fusedMap1457=true := by decide +kernel
theorem certified1457 : Certified (graph core1457) (root 10) 0 2 :=
  of_native_maps core1457 DegreeTwoThreeSpectrum2900.graph DegreeTwoThreeSpectrum2401.graph
    sourceMap1457 fusedMap1457 sourceMap1457_checked fusedMap1457_checked
    DegreeTwoThreeFiniteComparisons.comparison1457
#print axioms sourceMap1457_checked
#print axioms fusedMap1457_checked
#print axioms certified1457
def sourceMap1457swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1457swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1457swap_checked : acceptsGraphIso
    (source (graph core1457) (root 10) 2 0) DegreeTwoThreeSpectrum2900.graph sourceMap1457swap=true := by decide +kernel
theorem fusedMap1457swap_checked : acceptsGraphIso
    (fused (graph core1457) (root 10) 2 0) DegreeTwoThreeSpectrum2401.graph fusedMap1457swap=true := by decide +kernel
theorem certified1457swap : Certified (graph core1457) (root 10) 2 0 :=
  of_native_maps core1457 DegreeTwoThreeSpectrum2900.graph DegreeTwoThreeSpectrum2401.graph
    sourceMap1457swap fusedMap1457swap sourceMap1457swap_checked fusedMap1457swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1457
#print axioms sourceMap1457swap_checked
#print axioms fusedMap1457swap_checked
#print axioms certified1457swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
