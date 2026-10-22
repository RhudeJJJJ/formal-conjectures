/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1974 : Family 10 := level10.get ⟨1559,by decide⟩
def sourceMap1974 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1974 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1974_checked : acceptsGraphIso
    (source (graph core1974) (root 10) 0 2) DegreeTwoThreeSpectrum3757.graph sourceMap1974=true := by decide +kernel
theorem fusedMap1974_checked : acceptsGraphIso
    (fused (graph core1974) (root 10) 0 2) DegreeTwoThreeSpectrum3042.graph fusedMap1974=true := by decide +kernel
theorem certified1974 : Certified (graph core1974) (root 10) 0 2 :=
  of_native_maps core1974 DegreeTwoThreeSpectrum3757.graph DegreeTwoThreeSpectrum3042.graph
    sourceMap1974 fusedMap1974 sourceMap1974_checked fusedMap1974_checked
    DegreeTwoThreeFiniteComparisons.comparison1974
#print axioms sourceMap1974_checked
#print axioms fusedMap1974_checked
#print axioms certified1974
def sourceMap1974swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1974swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1974swap_checked : acceptsGraphIso
    (source (graph core1974) (root 10) 2 0) DegreeTwoThreeSpectrum3757.graph sourceMap1974swap=true := by decide +kernel
theorem fusedMap1974swap_checked : acceptsGraphIso
    (fused (graph core1974) (root 10) 2 0) DegreeTwoThreeSpectrum3042.graph fusedMap1974swap=true := by decide +kernel
theorem certified1974swap : Certified (graph core1974) (root 10) 2 0 :=
  of_native_maps core1974 DegreeTwoThreeSpectrum3757.graph DegreeTwoThreeSpectrum3042.graph
    sourceMap1974swap fusedMap1974swap sourceMap1974swap_checked fusedMap1974swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1974
#print axioms sourceMap1974swap_checked
#print axioms fusedMap1974swap_checked
#print axioms certified1974swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
