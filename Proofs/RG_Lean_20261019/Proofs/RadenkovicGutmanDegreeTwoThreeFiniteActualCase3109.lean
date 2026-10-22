/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3109 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap3109 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3109 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3109_checked : acceptsGraphIso
    (source (graph core3109) (root 7) 0 5) DegreeTwoThreeSpectrum2490.graph sourceMap3109=true := by decide +kernel
theorem fusedMap3109_checked : acceptsGraphIso
    (fused (graph core3109) (root 7) 0 5) DegreeTwoThreeSpectrum2317.graph fusedMap3109=true := by decide +kernel
theorem certified3109 : Certified (graph core3109) (root 7) 0 5 :=
  of_native_maps core3109 DegreeTwoThreeSpectrum2490.graph DegreeTwoThreeSpectrum2317.graph
    sourceMap3109 fusedMap3109 sourceMap3109_checked fusedMap3109_checked
    DegreeTwoThreeFiniteComparisons.comparison3109
#print axioms sourceMap3109_checked
#print axioms fusedMap3109_checked
#print axioms certified3109
def sourceMap3109swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3109swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3109swap_checked : acceptsGraphIso
    (source (graph core3109) (root 7) 5 0) DegreeTwoThreeSpectrum2490.graph sourceMap3109swap=true := by decide +kernel
theorem fusedMap3109swap_checked : acceptsGraphIso
    (fused (graph core3109) (root 7) 5 0) DegreeTwoThreeSpectrum2317.graph fusedMap3109swap=true := by decide +kernel
theorem certified3109swap : Certified (graph core3109) (root 7) 5 0 :=
  of_native_maps core3109 DegreeTwoThreeSpectrum2490.graph DegreeTwoThreeSpectrum2317.graph
    sourceMap3109swap fusedMap3109swap sourceMap3109swap_checked fusedMap3109swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3109
#print axioms sourceMap3109swap_checked
#print axioms fusedMap3109swap_checked
#print axioms certified3109swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
