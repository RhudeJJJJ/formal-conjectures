/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3794 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap3794 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,12,13,7,8,9,10,11] (sourceLabel 7 1 4 v)
def fusedMap3794 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3794_checked : acceptsGraphIso
    (source (graph core3794) (root 7) 1 4) DegreeTwoThreeSpectrum2991.graph sourceMap3794=true := by decide +kernel
theorem fusedMap3794_checked : acceptsGraphIso
    (fused (graph core3794) (root 7) 1 4) DegreeTwoThreeSpectrum2422.graph fusedMap3794=true := by decide +kernel
theorem certified3794 : Certified (graph core3794) (root 7) 1 4 :=
  of_native_maps core3794 DegreeTwoThreeSpectrum2991.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap3794 fusedMap3794 sourceMap3794_checked fusedMap3794_checked
    DegreeTwoThreeFiniteComparisons.comparison3794
#print axioms sourceMap3794_checked
#print axioms fusedMap3794_checked
#print axioms certified3794
def sourceMap3794swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,14,7,8,9,10,11,12,13] (sourceLabel 7 4 1 v)
def fusedMap3794swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3794swap_checked : acceptsGraphIso
    (source (graph core3794) (root 7) 4 1) DegreeTwoThreeSpectrum2991.graph sourceMap3794swap=true := by decide +kernel
theorem fusedMap3794swap_checked : acceptsGraphIso
    (fused (graph core3794) (root 7) 4 1) DegreeTwoThreeSpectrum2422.graph fusedMap3794swap=true := by decide +kernel
theorem certified3794swap : Certified (graph core3794) (root 7) 4 1 :=
  of_native_maps core3794 DegreeTwoThreeSpectrum2991.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap3794swap fusedMap3794swap sourceMap3794swap_checked fusedMap3794swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3794
#print axioms sourceMap3794swap_checked
#print axioms fusedMap3794swap_checked
#print axioms certified3794swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
