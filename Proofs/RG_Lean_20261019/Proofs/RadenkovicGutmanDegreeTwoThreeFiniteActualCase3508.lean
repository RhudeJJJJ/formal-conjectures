/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3508 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap3508 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3508 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3508_checked : acceptsGraphIso
    (source (graph core3508) (root 7) 0 6) DegreeTwoThreeSpectrum3909.graph sourceMap3508=true := by decide +kernel
theorem fusedMap3508_checked : acceptsGraphIso
    (fused (graph core3508) (root 7) 0 6) DegreeTwoThreeSpectrum3911.graph fusedMap3508=true := by decide +kernel
theorem certified3508 : Certified (graph core3508) (root 7) 0 6 :=
  of_native_maps core3508 DegreeTwoThreeSpectrum3909.graph DegreeTwoThreeSpectrum3911.graph
    sourceMap3508 fusedMap3508 sourceMap3508_checked fusedMap3508_checked
    DegreeTwoThreeFiniteComparisons.comparison3508
#print axioms sourceMap3508_checked
#print axioms fusedMap3508_checked
#print axioms certified3508
def sourceMap3508swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3508swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3508swap_checked : acceptsGraphIso
    (source (graph core3508) (root 7) 6 0) DegreeTwoThreeSpectrum3909.graph sourceMap3508swap=true := by decide +kernel
theorem fusedMap3508swap_checked : acceptsGraphIso
    (fused (graph core3508) (root 7) 6 0) DegreeTwoThreeSpectrum3911.graph fusedMap3508swap=true := by decide +kernel
theorem certified3508swap : Certified (graph core3508) (root 7) 6 0 :=
  of_native_maps core3508 DegreeTwoThreeSpectrum3909.graph DegreeTwoThreeSpectrum3911.graph
    sourceMap3508swap fusedMap3508swap sourceMap3508swap_checked fusedMap3508swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3508
#print axioms sourceMap3508swap_checked
#print axioms fusedMap3508swap_checked
#print axioms certified3508swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
