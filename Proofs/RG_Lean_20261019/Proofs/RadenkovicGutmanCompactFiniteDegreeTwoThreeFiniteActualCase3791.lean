/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3791 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap3791 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,12,13,7,8,9,10,11] (sourceLabel 7 1 4 v)
def fusedMap3791 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3791_checked : acceptsGraphIso
    (source (graph core3791) (root 7) 1 4) DegreeTwoThreeSpectrum2645.graph sourceMap3791=true := by decide +kernel
theorem fusedMap3791_checked : acceptsGraphIso
    (fused (graph core3791) (root 7) 1 4) DegreeTwoThreeSpectrum2342.graph fusedMap3791=true := by decide +kernel
theorem certified3791 : Certified (graph core3791) (root 7) 1 4 :=
  of_native_maps core3791 DegreeTwoThreeSpectrum2645.graph DegreeTwoThreeSpectrum2342.graph
    sourceMap3791 fusedMap3791 sourceMap3791_checked fusedMap3791_checked
    DegreeTwoThreeFiniteComparisons.comparison3791
#print axioms sourceMap3791_checked
#print axioms fusedMap3791_checked
#print axioms certified3791
def sourceMap3791swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,7,8,9,10,11,12,13] (sourceLabel 7 4 1 v)
def fusedMap3791swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3791swap_checked : acceptsGraphIso
    (source (graph core3791) (root 7) 4 1) DegreeTwoThreeSpectrum2645.graph sourceMap3791swap=true := by decide +kernel
theorem fusedMap3791swap_checked : acceptsGraphIso
    (fused (graph core3791) (root 7) 4 1) DegreeTwoThreeSpectrum2342.graph fusedMap3791swap=true := by decide +kernel
theorem certified3791swap : Certified (graph core3791) (root 7) 4 1 :=
  of_native_maps core3791 DegreeTwoThreeSpectrum2645.graph DegreeTwoThreeSpectrum2342.graph
    sourceMap3791swap fusedMap3791swap sourceMap3791swap_checked fusedMap3791swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3791
#print axioms sourceMap3791swap_checked
#print axioms fusedMap3791swap_checked
#print axioms certified3791swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
