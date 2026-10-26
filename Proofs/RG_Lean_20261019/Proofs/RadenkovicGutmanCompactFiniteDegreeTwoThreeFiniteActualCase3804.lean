/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3804 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap3804 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3804 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3804_checked : acceptsGraphIso
    (source (graph core3804) (root 7) 1 4) DegreeTwoThreeSpectrum2857.graph sourceMap3804=true := by decide +kernel
theorem fusedMap3804_checked : acceptsGraphIso
    (fused (graph core3804) (root 7) 1 4) DegreeTwoThreeSpectrum2384.graph fusedMap3804=true := by decide +kernel
theorem certified3804 : Certified (graph core3804) (root 7) 1 4 :=
  of_native_maps core3804 DegreeTwoThreeSpectrum2857.graph DegreeTwoThreeSpectrum2384.graph
    sourceMap3804 fusedMap3804 sourceMap3804_checked fusedMap3804_checked
    DegreeTwoThreeFiniteComparisons.comparison3804
#print axioms sourceMap3804_checked
#print axioms fusedMap3804_checked
#print axioms certified3804
def sourceMap3804swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3804swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3804swap_checked : acceptsGraphIso
    (source (graph core3804) (root 7) 4 1) DegreeTwoThreeSpectrum2857.graph sourceMap3804swap=true := by decide +kernel
theorem fusedMap3804swap_checked : acceptsGraphIso
    (fused (graph core3804) (root 7) 4 1) DegreeTwoThreeSpectrum2384.graph fusedMap3804swap=true := by decide +kernel
theorem certified3804swap : Certified (graph core3804) (root 7) 4 1 :=
  of_native_maps core3804 DegreeTwoThreeSpectrum2857.graph DegreeTwoThreeSpectrum2384.graph
    sourceMap3804swap fusedMap3804swap sourceMap3804swap_checked fusedMap3804swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3804
#print axioms sourceMap3804swap_checked
#print axioms fusedMap3804swap_checked
#print axioms certified3804swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
