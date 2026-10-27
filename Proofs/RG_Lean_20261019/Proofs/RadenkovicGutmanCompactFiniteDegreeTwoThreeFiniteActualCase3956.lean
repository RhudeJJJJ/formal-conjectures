/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3956 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap3956 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3956 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3956_checked : acceptsGraphIso
    (source (graph core3956) (root 7) 1 5) DegreeTwoThreeSpectrum4255.graph sourceMap3956=true := by decide +kernel
theorem fusedMap3956_checked : acceptsGraphIso
    (fused (graph core3956) (root 7) 1 5) DegreeTwoThreeSpectrum3911.graph fusedMap3956=true := by decide +kernel
theorem certified3956 : Certified (graph core3956) (root 7) 1 5 :=
  of_native_maps core3956 DegreeTwoThreeSpectrum4255.graph DegreeTwoThreeSpectrum3911.graph
    sourceMap3956 fusedMap3956 sourceMap3956_checked fusedMap3956_checked
    DegreeTwoThreeFiniteComparisons.comparison3956
#print axioms sourceMap3956_checked
#print axioms fusedMap3956_checked
#print axioms certified3956
def sourceMap3956swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3956swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3956swap_checked : acceptsGraphIso
    (source (graph core3956) (root 7) 5 1) DegreeTwoThreeSpectrum4255.graph sourceMap3956swap=true := by decide +kernel
theorem fusedMap3956swap_checked : acceptsGraphIso
    (fused (graph core3956) (root 7) 5 1) DegreeTwoThreeSpectrum3911.graph fusedMap3956swap=true := by decide +kernel
theorem certified3956swap : Certified (graph core3956) (root 7) 5 1 :=
  of_native_maps core3956 DegreeTwoThreeSpectrum4255.graph DegreeTwoThreeSpectrum3911.graph
    sourceMap3956swap fusedMap3956swap sourceMap3956swap_checked fusedMap3956swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3956
#print axioms sourceMap3956swap_checked
#print axioms fusedMap3956swap_checked
#print axioms certified3956swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
