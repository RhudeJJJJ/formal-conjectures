/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3921 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap3921 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3921 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3921_checked : acceptsGraphIso
    (source (graph core3921) (root 8) 1 4) DegreeTwoThreeSpectrum4679.graph sourceMap3921=true := by decide +kernel
theorem fusedMap3921_checked : acceptsGraphIso
    (fused (graph core3921) (root 8) 1 4) DegreeTwoThreeSpectrum4182.graph fusedMap3921=true := by decide +kernel
theorem certified3921 : Certified (graph core3921) (root 8) 1 4 :=
  of_native_maps core3921 DegreeTwoThreeSpectrum4679.graph DegreeTwoThreeSpectrum4182.graph
    sourceMap3921 fusedMap3921 sourceMap3921_checked fusedMap3921_checked
    DegreeTwoThreeFiniteComparisons.comparison3921
#print axioms sourceMap3921_checked
#print axioms fusedMap3921_checked
#print axioms certified3921
def sourceMap3921swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3921swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3921swap_checked : acceptsGraphIso
    (source (graph core3921) (root 8) 4 1) DegreeTwoThreeSpectrum4679.graph sourceMap3921swap=true := by decide +kernel
theorem fusedMap3921swap_checked : acceptsGraphIso
    (fused (graph core3921) (root 8) 4 1) DegreeTwoThreeSpectrum4182.graph fusedMap3921swap=true := by decide +kernel
theorem certified3921swap : Certified (graph core3921) (root 8) 4 1 :=
  of_native_maps core3921 DegreeTwoThreeSpectrum4679.graph DegreeTwoThreeSpectrum4182.graph
    sourceMap3921swap fusedMap3921swap sourceMap3921swap_checked fusedMap3921swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3921
#print axioms sourceMap3921swap_checked
#print axioms fusedMap3921swap_checked
#print axioms certified3921swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
