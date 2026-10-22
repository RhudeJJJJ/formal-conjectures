/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3957 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap3957 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3957 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3957_checked : acceptsGraphIso
    (source (graph core3957) (root 7) 1 5) DegreeTwoThreeSpectrum4325.graph sourceMap3957=true := by decide +kernel
theorem fusedMap3957_checked : acceptsGraphIso
    (fused (graph core3957) (root 7) 1 5) DegreeTwoThreeSpectrum3935.graph fusedMap3957=true := by decide +kernel
theorem certified3957 : Certified (graph core3957) (root 7) 1 5 :=
  of_native_maps core3957 DegreeTwoThreeSpectrum4325.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap3957 fusedMap3957 sourceMap3957_checked fusedMap3957_checked
    DegreeTwoThreeFiniteComparisons.comparison3957
#print axioms sourceMap3957_checked
#print axioms fusedMap3957_checked
#print axioms certified3957
def sourceMap3957swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3957swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3957swap_checked : acceptsGraphIso
    (source (graph core3957) (root 7) 5 1) DegreeTwoThreeSpectrum4325.graph sourceMap3957swap=true := by decide +kernel
theorem fusedMap3957swap_checked : acceptsGraphIso
    (fused (graph core3957) (root 7) 5 1) DegreeTwoThreeSpectrum3935.graph fusedMap3957swap=true := by decide +kernel
theorem certified3957swap : Certified (graph core3957) (root 7) 5 1 :=
  of_native_maps core3957 DegreeTwoThreeSpectrum4325.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap3957swap fusedMap3957swap sourceMap3957swap_checked fusedMap3957swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3957
#print axioms sourceMap3957swap_checked
#print axioms fusedMap3957swap_checked
#print axioms certified3957swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
