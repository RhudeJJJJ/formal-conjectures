/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1956 : Family 10 := level10.get ⟨1504,by decide⟩
def sourceMap1956 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1956 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1956_checked : acceptsGraphIso
    (source (graph core1956) (root 10) 0 2) DegreeTwoThreeSpectrum3472.graph sourceMap1956=true := by decide +kernel
theorem fusedMap1956_checked : acceptsGraphIso
    (fused (graph core1956) (root 10) 0 2) DegreeTwoThreeSpectrum3728.graph fusedMap1956=true := by decide +kernel
theorem certified1956 : Certified (graph core1956) (root 10) 0 2 :=
  of_native_maps core1956 DegreeTwoThreeSpectrum3472.graph DegreeTwoThreeSpectrum3728.graph
    sourceMap1956 fusedMap1956 sourceMap1956_checked fusedMap1956_checked
    DegreeTwoThreeFiniteComparisons.comparison1956
#print axioms sourceMap1956_checked
#print axioms fusedMap1956_checked
#print axioms certified1956
def sourceMap1956swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1956swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1956swap_checked : acceptsGraphIso
    (source (graph core1956) (root 10) 2 0) DegreeTwoThreeSpectrum3472.graph sourceMap1956swap=true := by decide +kernel
theorem fusedMap1956swap_checked : acceptsGraphIso
    (fused (graph core1956) (root 10) 2 0) DegreeTwoThreeSpectrum3728.graph fusedMap1956swap=true := by decide +kernel
theorem certified1956swap : Certified (graph core1956) (root 10) 2 0 :=
  of_native_maps core1956 DegreeTwoThreeSpectrum3472.graph DegreeTwoThreeSpectrum3728.graph
    sourceMap1956swap fusedMap1956swap sourceMap1956swap_checked fusedMap1956swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1956
#print axioms sourceMap1956swap_checked
#print axioms fusedMap1956swap_checked
#print axioms certified1956swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
