/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3681 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap3681 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3681 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3681_checked : acceptsGraphIso
    (source (graph core3681) (root 7) 0 7) DegreeTwoThreeSpectrum5146.graph sourceMap3681=true := by decide +kernel
theorem fusedMap3681_checked : acceptsGraphIso
    (fused (graph core3681) (root 7) 0 7) DegreeTwoThreeSpectrum5149.graph fusedMap3681=true := by decide +kernel
theorem certified3681 : Certified (graph core3681) (root 7) 0 7 :=
  of_native_maps core3681 DegreeTwoThreeSpectrum5146.graph DegreeTwoThreeSpectrum5149.graph
    sourceMap3681 fusedMap3681 sourceMap3681_checked fusedMap3681_checked
    DegreeTwoThreeFiniteComparisons.comparison3681
#print axioms sourceMap3681_checked
#print axioms fusedMap3681_checked
#print axioms certified3681
def sourceMap3681swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3681swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3681swap_checked : acceptsGraphIso
    (source (graph core3681) (root 7) 7 0) DegreeTwoThreeSpectrum5146.graph sourceMap3681swap=true := by decide +kernel
theorem fusedMap3681swap_checked : acceptsGraphIso
    (fused (graph core3681) (root 7) 7 0) DegreeTwoThreeSpectrum5149.graph fusedMap3681swap=true := by decide +kernel
theorem certified3681swap : Certified (graph core3681) (root 7) 7 0 :=
  of_native_maps core3681 DegreeTwoThreeSpectrum5146.graph DegreeTwoThreeSpectrum5149.graph
    sourceMap3681swap fusedMap3681swap sourceMap3681swap_checked fusedMap3681swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3681
#print axioms sourceMap3681swap_checked
#print axioms fusedMap3681swap_checked
#print axioms certified3681swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
