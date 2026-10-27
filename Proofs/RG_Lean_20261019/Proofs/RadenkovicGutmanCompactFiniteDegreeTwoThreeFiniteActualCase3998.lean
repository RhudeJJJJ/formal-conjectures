/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3998 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3998 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap3998 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap3998_checked : acceptsGraphIso
    (source (graph core3998) (root 6) 1 6) DegreeTwoThreeSpectrum4160.graph sourceMap3998=true := by decide +kernel
theorem fusedMap3998_checked : acceptsGraphIso
    (fused (graph core3998) (root 6) 1 6) DegreeTwoThreeSpectrum3887.graph fusedMap3998=true := by decide +kernel
theorem certified3998 : Certified (graph core3998) (root 6) 1 6 :=
  of_native_maps core3998 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap3998 fusedMap3998 sourceMap3998_checked fusedMap3998_checked
    DegreeTwoThreeFiniteComparisons.comparison3998
#print axioms sourceMap3998_checked
#print axioms fusedMap3998_checked
#print axioms certified3998
def sourceMap3998swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,15,7,8] (sourceLabel 6 6 1 v)
def fusedMap3998swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap3998swap_checked : acceptsGraphIso
    (source (graph core3998) (root 6) 6 1) DegreeTwoThreeSpectrum4160.graph sourceMap3998swap=true := by decide +kernel
theorem fusedMap3998swap_checked : acceptsGraphIso
    (fused (graph core3998) (root 6) 6 1) DegreeTwoThreeSpectrum3887.graph fusedMap3998swap=true := by decide +kernel
theorem certified3998swap : Certified (graph core3998) (root 6) 6 1 :=
  of_native_maps core3998 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap3998swap fusedMap3998swap sourceMap3998swap_checked fusedMap3998swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3998
#print axioms sourceMap3998swap_checked
#print axioms fusedMap3998swap_checked
#print axioms certified3998swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
