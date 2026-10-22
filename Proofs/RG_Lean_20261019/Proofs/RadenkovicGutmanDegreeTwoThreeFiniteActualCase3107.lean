/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3107 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap3107 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3107 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3107_checked : acceptsGraphIso
    (source (graph core3107) (root 7) 0 5) DegreeTwoThreeSpectrum2419.graph sourceMap3107=true := by decide +kernel
theorem fusedMap3107_checked : acceptsGraphIso
    (fused (graph core3107) (root 7) 0 5) DegreeTwoThreeSpectrum2422.graph fusedMap3107=true := by decide +kernel
theorem certified3107 : Certified (graph core3107) (root 7) 0 5 :=
  of_native_maps core3107 DegreeTwoThreeSpectrum2419.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap3107 fusedMap3107 sourceMap3107_checked fusedMap3107_checked
    DegreeTwoThreeFiniteComparisons.comparison3107
#print axioms sourceMap3107_checked
#print axioms fusedMap3107_checked
#print axioms certified3107
def sourceMap3107swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,14,8] (sourceLabel 7 5 0 v)
def fusedMap3107swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3107swap_checked : acceptsGraphIso
    (source (graph core3107) (root 7) 5 0) DegreeTwoThreeSpectrum2419.graph sourceMap3107swap=true := by decide +kernel
theorem fusedMap3107swap_checked : acceptsGraphIso
    (fused (graph core3107) (root 7) 5 0) DegreeTwoThreeSpectrum2422.graph fusedMap3107swap=true := by decide +kernel
theorem certified3107swap : Certified (graph core3107) (root 7) 5 0 :=
  of_native_maps core3107 DegreeTwoThreeSpectrum2419.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap3107swap fusedMap3107swap sourceMap3107swap_checked fusedMap3107swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3107
#print axioms sourceMap3107swap_checked
#print axioms fusedMap3107swap_checked
#print axioms certified3107swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
