/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3680 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap3680 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3680 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3680_checked : acceptsGraphIso
    (source (graph core3680) (root 7) 0 7) DegreeTwoThreeSpectrum5844.graph sourceMap3680=true := by decide +kernel
theorem fusedMap3680_checked : acceptsGraphIso
    (fused (graph core3680) (root 7) 0 7) DegreeTwoThreeSpectrum5082.graph fusedMap3680=true := by decide +kernel
theorem certified3680 : Certified (graph core3680) (root 7) 0 7 :=
  of_native_maps core3680 DegreeTwoThreeSpectrum5844.graph DegreeTwoThreeSpectrum5082.graph
    sourceMap3680 fusedMap3680 sourceMap3680_checked fusedMap3680_checked
    DegreeTwoThreeFiniteComparisons.comparison3680
#print axioms sourceMap3680_checked
#print axioms fusedMap3680_checked
#print axioms certified3680
def sourceMap3680swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3680swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3680swap_checked : acceptsGraphIso
    (source (graph core3680) (root 7) 7 0) DegreeTwoThreeSpectrum5844.graph sourceMap3680swap=true := by decide +kernel
theorem fusedMap3680swap_checked : acceptsGraphIso
    (fused (graph core3680) (root 7) 7 0) DegreeTwoThreeSpectrum5082.graph fusedMap3680swap=true := by decide +kernel
theorem certified3680swap : Certified (graph core3680) (root 7) 7 0 :=
  of_native_maps core3680 DegreeTwoThreeSpectrum5844.graph DegreeTwoThreeSpectrum5082.graph
    sourceMap3680swap fusedMap3680swap sourceMap3680swap_checked fusedMap3680swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3680
#print axioms sourceMap3680swap_checked
#print axioms fusedMap3680swap_checked
#print axioms certified3680swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
