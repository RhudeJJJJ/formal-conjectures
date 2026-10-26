/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3895 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap3895 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3895 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3895_checked : acceptsGraphIso
    (source (graph core3895) (root 8) 1 4) DegreeTwoThreeSpectrum4711.graph sourceMap3895=true := by decide +kernel
theorem fusedMap3895_checked : acceptsGraphIso
    (fused (graph core3895) (root 8) 1 4) DegreeTwoThreeSpectrum4236.graph fusedMap3895=true := by decide +kernel
theorem certified3895 : Certified (graph core3895) (root 8) 1 4 :=
  of_native_maps core3895 DegreeTwoThreeSpectrum4711.graph DegreeTwoThreeSpectrum4236.graph
    sourceMap3895 fusedMap3895 sourceMap3895_checked fusedMap3895_checked
    DegreeTwoThreeFiniteComparisons.comparison3895
#print axioms sourceMap3895_checked
#print axioms fusedMap3895_checked
#print axioms certified3895
def sourceMap3895swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3895swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3895swap_checked : acceptsGraphIso
    (source (graph core3895) (root 8) 4 1) DegreeTwoThreeSpectrum4711.graph sourceMap3895swap=true := by decide +kernel
theorem fusedMap3895swap_checked : acceptsGraphIso
    (fused (graph core3895) (root 8) 4 1) DegreeTwoThreeSpectrum4236.graph fusedMap3895swap=true := by decide +kernel
theorem certified3895swap : Certified (graph core3895) (root 8) 4 1 :=
  of_native_maps core3895 DegreeTwoThreeSpectrum4711.graph DegreeTwoThreeSpectrum4236.graph
    sourceMap3895swap fusedMap3895swap sourceMap3895swap_checked fusedMap3895swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3895
#print axioms sourceMap3895swap_checked
#print axioms fusedMap3895swap_checked
#print axioms certified3895swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
