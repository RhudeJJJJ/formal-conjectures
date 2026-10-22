/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1980 : Family 10 := level10.get ⟨1576,by decide⟩
def sourceMap1980 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1980 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1980_checked : acceptsGraphIso
    (source (graph core1980) (root 10) 0 2) DegreeTwoThreeSpectrum3764.graph sourceMap1980=true := by decide +kernel
theorem fusedMap1980_checked : acceptsGraphIso
    (fused (graph core1980) (root 10) 0 2) DegreeTwoThreeSpectrum3070.graph fusedMap1980=true := by decide +kernel
theorem certified1980 : Certified (graph core1980) (root 10) 0 2 :=
  of_native_maps core1980 DegreeTwoThreeSpectrum3764.graph DegreeTwoThreeSpectrum3070.graph
    sourceMap1980 fusedMap1980 sourceMap1980_checked fusedMap1980_checked
    DegreeTwoThreeFiniteComparisons.comparison1980
#print axioms sourceMap1980_checked
#print axioms fusedMap1980_checked
#print axioms certified1980
def sourceMap1980swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1980swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1980swap_checked : acceptsGraphIso
    (source (graph core1980) (root 10) 2 0) DegreeTwoThreeSpectrum3764.graph sourceMap1980swap=true := by decide +kernel
theorem fusedMap1980swap_checked : acceptsGraphIso
    (fused (graph core1980) (root 10) 2 0) DegreeTwoThreeSpectrum3070.graph fusedMap1980swap=true := by decide +kernel
theorem certified1980swap : Certified (graph core1980) (root 10) 2 0 :=
  of_native_maps core1980 DegreeTwoThreeSpectrum3764.graph DegreeTwoThreeSpectrum3070.graph
    sourceMap1980swap fusedMap1980swap sourceMap1980swap_checked fusedMap1980swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1980
#print axioms sourceMap1980swap_checked
#print axioms fusedMap1980swap_checked
#print axioms certified1980swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
