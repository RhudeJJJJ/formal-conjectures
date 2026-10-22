/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3098 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap3098 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3098 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3098_checked : acceptsGraphIso
    (source (graph core3098) (root 6) 0 5) DegreeTwoThreeSpectrum1859.graph sourceMap3098=true := by decide +kernel
theorem fusedMap3098_checked : acceptsGraphIso
    (fused (graph core3098) (root 6) 0 5) DegreeTwoThreeSpectrum1861.graph fusedMap3098=true := by decide +kernel
theorem certified3098 : Certified (graph core3098) (root 6) 0 5 :=
  of_native_maps core3098 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1861.graph
    sourceMap3098 fusedMap3098 sourceMap3098_checked fusedMap3098_checked
    DegreeTwoThreeFiniteComparisons.comparison3098
#print axioms sourceMap3098_checked
#print axioms fusedMap3098_checked
#print axioms certified3098
def sourceMap3098swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3098swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3098swap_checked : acceptsGraphIso
    (source (graph core3098) (root 6) 5 0) DegreeTwoThreeSpectrum1859.graph sourceMap3098swap=true := by decide +kernel
theorem fusedMap3098swap_checked : acceptsGraphIso
    (fused (graph core3098) (root 6) 5 0) DegreeTwoThreeSpectrum1861.graph fusedMap3098swap=true := by decide +kernel
theorem certified3098swap : Certified (graph core3098) (root 6) 5 0 :=
  of_native_maps core3098 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1861.graph
    sourceMap3098swap fusedMap3098swap sourceMap3098swap_checked fusedMap3098swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3098
#print axioms sourceMap3098swap_checked
#print axioms fusedMap3098swap_checked
#print axioms certified3098swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
