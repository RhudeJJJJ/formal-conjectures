/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3818 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap3818 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3818 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3818_checked : acceptsGraphIso
    (source (graph core3818) (root 7) 1 4) DegreeTwoThreeSpectrum3429.graph sourceMap3818=true := by decide +kernel
theorem fusedMap3818_checked : acceptsGraphIso
    (fused (graph core3818) (root 7) 1 4) DegreeTwoThreeSpectrum2665.graph fusedMap3818=true := by decide +kernel
theorem certified3818 : Certified (graph core3818) (root 7) 1 4 :=
  of_native_maps core3818 DegreeTwoThreeSpectrum3429.graph DegreeTwoThreeSpectrum2665.graph
    sourceMap3818 fusedMap3818 sourceMap3818_checked fusedMap3818_checked
    DegreeTwoThreeFiniteComparisons.comparison3818
#print axioms sourceMap3818_checked
#print axioms fusedMap3818_checked
#print axioms certified3818
def sourceMap3818swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3818swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3818swap_checked : acceptsGraphIso
    (source (graph core3818) (root 7) 4 1) DegreeTwoThreeSpectrum3429.graph sourceMap3818swap=true := by decide +kernel
theorem fusedMap3818swap_checked : acceptsGraphIso
    (fused (graph core3818) (root 7) 4 1) DegreeTwoThreeSpectrum2665.graph fusedMap3818swap=true := by decide +kernel
theorem certified3818swap : Certified (graph core3818) (root 7) 4 1 :=
  of_native_maps core3818 DegreeTwoThreeSpectrum3429.graph DegreeTwoThreeSpectrum2665.graph
    sourceMap3818swap fusedMap3818swap sourceMap3818swap_checked fusedMap3818swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3818
#print axioms sourceMap3818swap_checked
#print axioms fusedMap3818swap_checked
#print axioms certified3818swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
