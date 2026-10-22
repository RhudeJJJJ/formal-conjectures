/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3256 : Family 9 := level9.get ⟨98,by decide⟩
def sourceMap3256 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3256 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3256_checked : acceptsGraphIso
    (source (graph core3256) (root 9) 0 5) DegreeTwoThreeSpectrum5725.graph sourceMap3256=true := by decide +kernel
theorem fusedMap3256_checked : acceptsGraphIso
    (fused (graph core3256) (root 9) 0 5) DegreeTwoThreeSpectrum5053.graph fusedMap3256=true := by decide +kernel
theorem certified3256 : Certified (graph core3256) (root 9) 0 5 :=
  of_native_maps core3256 DegreeTwoThreeSpectrum5725.graph DegreeTwoThreeSpectrum5053.graph
    sourceMap3256 fusedMap3256 sourceMap3256_checked fusedMap3256_checked
    DegreeTwoThreeFiniteComparisons.comparison3256
#print axioms sourceMap3256_checked
#print axioms fusedMap3256_checked
#print axioms certified3256
def sourceMap3256swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3256swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3256swap_checked : acceptsGraphIso
    (source (graph core3256) (root 9) 5 0) DegreeTwoThreeSpectrum5725.graph sourceMap3256swap=true := by decide +kernel
theorem fusedMap3256swap_checked : acceptsGraphIso
    (fused (graph core3256) (root 9) 5 0) DegreeTwoThreeSpectrum5053.graph fusedMap3256swap=true := by decide +kernel
theorem certified3256swap : Certified (graph core3256) (root 9) 5 0 :=
  of_native_maps core3256 DegreeTwoThreeSpectrum5725.graph DegreeTwoThreeSpectrum5053.graph
    sourceMap3256swap fusedMap3256swap sourceMap3256swap_checked fusedMap3256swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3256
#print axioms sourceMap3256swap_checked
#print axioms fusedMap3256swap_checked
#print axioms certified3256swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
