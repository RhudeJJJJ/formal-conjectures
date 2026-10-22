/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1971 : Family 10 := level10.get ⟨1554,by decide⟩
def sourceMap1971 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1971 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1971_checked : acceptsGraphIso
    (source (graph core1971) (root 10) 0 2) DegreeTwoThreeSpectrum3754.graph sourceMap1971=true := by decide +kernel
theorem fusedMap1971_checked : acceptsGraphIso
    (fused (graph core1971) (root 10) 0 2) DegreeTwoThreeSpectrum3033.graph fusedMap1971=true := by decide +kernel
theorem certified1971 : Certified (graph core1971) (root 10) 0 2 :=
  of_native_maps core1971 DegreeTwoThreeSpectrum3754.graph DegreeTwoThreeSpectrum3033.graph
    sourceMap1971 fusedMap1971 sourceMap1971_checked fusedMap1971_checked
    DegreeTwoThreeFiniteComparisons.comparison1971
#print axioms sourceMap1971_checked
#print axioms fusedMap1971_checked
#print axioms certified1971
def sourceMap1971swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1971swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1971swap_checked : acceptsGraphIso
    (source (graph core1971) (root 10) 2 0) DegreeTwoThreeSpectrum3754.graph sourceMap1971swap=true := by decide +kernel
theorem fusedMap1971swap_checked : acceptsGraphIso
    (fused (graph core1971) (root 10) 2 0) DegreeTwoThreeSpectrum3033.graph fusedMap1971swap=true := by decide +kernel
theorem certified1971swap : Certified (graph core1971) (root 10) 2 0 :=
  of_native_maps core1971 DegreeTwoThreeSpectrum3754.graph DegreeTwoThreeSpectrum3033.graph
    sourceMap1971swap fusedMap1971swap sourceMap1971swap_checked fusedMap1971swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1971
#print axioms sourceMap1971swap_checked
#print axioms fusedMap1971swap_checked
#print axioms certified1971swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
