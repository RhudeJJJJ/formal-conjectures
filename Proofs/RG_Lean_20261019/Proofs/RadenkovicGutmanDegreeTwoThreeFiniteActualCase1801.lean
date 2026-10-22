/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1801 : Family 10 := level10.get ⟨1139,by decide⟩
def sourceMap1801 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1801 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1801_checked : acceptsGraphIso
    (source (graph core1801) (root 10) 0 2) DegreeTwoThreeSpectrum3224.graph sourceMap1801=true := by decide +kernel
theorem fusedMap1801_checked : acceptsGraphIso
    (fused (graph core1801) (root 10) 0 2) DegreeTwoThreeSpectrum3225.graph fusedMap1801=true := by decide +kernel
theorem certified1801 : Certified (graph core1801) (root 10) 0 2 :=
  of_native_maps core1801 DegreeTwoThreeSpectrum3224.graph DegreeTwoThreeSpectrum3225.graph
    sourceMap1801 fusedMap1801 sourceMap1801_checked fusedMap1801_checked
    DegreeTwoThreeFiniteComparisons.comparison1801
#print axioms sourceMap1801_checked
#print axioms fusedMap1801_checked
#print axioms certified1801
def sourceMap1801swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1801swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1801swap_checked : acceptsGraphIso
    (source (graph core1801) (root 10) 2 0) DegreeTwoThreeSpectrum3224.graph sourceMap1801swap=true := by decide +kernel
theorem fusedMap1801swap_checked : acceptsGraphIso
    (fused (graph core1801) (root 10) 2 0) DegreeTwoThreeSpectrum3225.graph fusedMap1801swap=true := by decide +kernel
theorem certified1801swap : Certified (graph core1801) (root 10) 2 0 :=
  of_native_maps core1801 DegreeTwoThreeSpectrum3224.graph DegreeTwoThreeSpectrum3225.graph
    sourceMap1801swap fusedMap1801swap sourceMap1801swap_checked fusedMap1801swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1801
#print axioms sourceMap1801swap_checked
#print axioms fusedMap1801swap_checked
#print axioms certified1801swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
