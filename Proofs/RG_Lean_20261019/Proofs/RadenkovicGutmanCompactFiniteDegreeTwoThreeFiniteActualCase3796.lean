/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3796 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap3796 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3796 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3796_checked : acceptsGraphIso
    (source (graph core3796) (root 7) 1 4) DegreeTwoThreeSpectrum2486.graph sourceMap3796=true := by decide +kernel
theorem fusedMap3796_checked : acceptsGraphIso
    (fused (graph core3796) (root 7) 1 4) DegreeTwoThreeSpectrum2317.graph fusedMap3796=true := by decide +kernel
theorem certified3796 : Certified (graph core3796) (root 7) 1 4 :=
  of_native_maps core3796 DegreeTwoThreeSpectrum2486.graph DegreeTwoThreeSpectrum2317.graph
    sourceMap3796 fusedMap3796 sourceMap3796_checked fusedMap3796_checked
    DegreeTwoThreeFiniteComparisons.comparison3796
#print axioms sourceMap3796_checked
#print axioms fusedMap3796_checked
#print axioms certified3796
def sourceMap3796swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,14,7,8] (sourceLabel 7 4 1 v)
def fusedMap3796swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3796swap_checked : acceptsGraphIso
    (source (graph core3796) (root 7) 4 1) DegreeTwoThreeSpectrum2486.graph sourceMap3796swap=true := by decide +kernel
theorem fusedMap3796swap_checked : acceptsGraphIso
    (fused (graph core3796) (root 7) 4 1) DegreeTwoThreeSpectrum2317.graph fusedMap3796swap=true := by decide +kernel
theorem certified3796swap : Certified (graph core3796) (root 7) 4 1 :=
  of_native_maps core3796 DegreeTwoThreeSpectrum2486.graph DegreeTwoThreeSpectrum2317.graph
    sourceMap3796swap fusedMap3796swap sourceMap3796swap_checked fusedMap3796swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3796
#print axioms sourceMap3796swap_checked
#print axioms fusedMap3796swap_checked
#print axioms certified3796swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
