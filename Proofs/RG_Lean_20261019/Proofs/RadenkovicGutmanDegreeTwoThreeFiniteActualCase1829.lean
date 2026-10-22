/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1829 : Family 10 := level10.get ⟨1205,by decide⟩
def sourceMap1829 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1829 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1829_checked : acceptsGraphIso
    (source (graph core1829) (root 10) 0 2) DegreeTwoThreeSpectrum3325.graph sourceMap1829=true := by decide +kernel
theorem fusedMap1829_checked : acceptsGraphIso
    (fused (graph core1829) (root 10) 0 2) DegreeTwoThreeSpectrum3326.graph fusedMap1829=true := by decide +kernel
theorem certified1829 : Certified (graph core1829) (root 10) 0 2 :=
  of_native_maps core1829 DegreeTwoThreeSpectrum3325.graph DegreeTwoThreeSpectrum3326.graph
    sourceMap1829 fusedMap1829 sourceMap1829_checked fusedMap1829_checked
    DegreeTwoThreeFiniteComparisons.comparison1829
#print axioms sourceMap1829_checked
#print axioms fusedMap1829_checked
#print axioms certified1829
def sourceMap1829swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1829swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1829swap_checked : acceptsGraphIso
    (source (graph core1829) (root 10) 2 0) DegreeTwoThreeSpectrum3325.graph sourceMap1829swap=true := by decide +kernel
theorem fusedMap1829swap_checked : acceptsGraphIso
    (fused (graph core1829) (root 10) 2 0) DegreeTwoThreeSpectrum3326.graph fusedMap1829swap=true := by decide +kernel
theorem certified1829swap : Certified (graph core1829) (root 10) 2 0 :=
  of_native_maps core1829 DegreeTwoThreeSpectrum3325.graph DegreeTwoThreeSpectrum3326.graph
    sourceMap1829swap fusedMap1829swap sourceMap1829swap_checked fusedMap1829swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1829
#print axioms sourceMap1829swap_checked
#print axioms fusedMap1829swap_checked
#print axioms certified1829swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
