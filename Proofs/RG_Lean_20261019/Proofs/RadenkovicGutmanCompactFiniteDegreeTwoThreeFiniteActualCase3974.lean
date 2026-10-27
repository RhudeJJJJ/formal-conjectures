/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3974 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap3974 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3974 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3974_checked : acceptsGraphIso
    (source (graph core3974) (root 7) 1 5) DegreeTwoThreeSpectrum4310.graph sourceMap3974=true := by decide +kernel
theorem fusedMap3974_checked : acceptsGraphIso
    (fused (graph core3974) (root 7) 1 5) DegreeTwoThreeSpectrum3927.graph fusedMap3974=true := by decide +kernel
theorem certified3974 : Certified (graph core3974) (root 7) 1 5 :=
  of_native_maps core3974 DegreeTwoThreeSpectrum4310.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap3974 fusedMap3974 sourceMap3974_checked fusedMap3974_checked
    DegreeTwoThreeFiniteComparisons.comparison3974
#print axioms sourceMap3974_checked
#print axioms fusedMap3974_checked
#print axioms certified3974
def sourceMap3974swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3974swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3974swap_checked : acceptsGraphIso
    (source (graph core3974) (root 7) 5 1) DegreeTwoThreeSpectrum4310.graph sourceMap3974swap=true := by decide +kernel
theorem fusedMap3974swap_checked : acceptsGraphIso
    (fused (graph core3974) (root 7) 5 1) DegreeTwoThreeSpectrum3927.graph fusedMap3974swap=true := by decide +kernel
theorem certified3974swap : Certified (graph core3974) (root 7) 5 1 :=
  of_native_maps core3974 DegreeTwoThreeSpectrum4310.graph DegreeTwoThreeSpectrum3927.graph
    sourceMap3974swap fusedMap3974swap sourceMap3974swap_checked fusedMap3974swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3974
#print axioms sourceMap3974swap_checked
#print axioms fusedMap3974swap_checked
#print axioms certified3974swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
