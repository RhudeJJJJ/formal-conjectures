/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3682 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap3682 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3682 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3682_checked : acceptsGraphIso
    (source (graph core3682) (root 7) 0 7) DegreeTwoThreeSpectrum5170.graph sourceMap3682=true := by decide +kernel
theorem fusedMap3682_checked : acceptsGraphIso
    (fused (graph core3682) (root 7) 0 7) DegreeTwoThreeSpectrum5173.graph fusedMap3682=true := by decide +kernel
theorem certified3682 : Certified (graph core3682) (root 7) 0 7 :=
  of_native_maps core3682 DegreeTwoThreeSpectrum5170.graph DegreeTwoThreeSpectrum5173.graph
    sourceMap3682 fusedMap3682 sourceMap3682_checked fusedMap3682_checked
    DegreeTwoThreeFiniteComparisons.comparison3682
#print axioms sourceMap3682_checked
#print axioms fusedMap3682_checked
#print axioms certified3682
def sourceMap3682swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3682swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3682swap_checked : acceptsGraphIso
    (source (graph core3682) (root 7) 7 0) DegreeTwoThreeSpectrum5170.graph sourceMap3682swap=true := by decide +kernel
theorem fusedMap3682swap_checked : acceptsGraphIso
    (fused (graph core3682) (root 7) 7 0) DegreeTwoThreeSpectrum5173.graph fusedMap3682swap=true := by decide +kernel
theorem certified3682swap : Certified (graph core3682) (root 7) 7 0 :=
  of_native_maps core3682 DegreeTwoThreeSpectrum5170.graph DegreeTwoThreeSpectrum5173.graph
    sourceMap3682swap fusedMap3682swap sourceMap3682swap_checked fusedMap3682swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3682
#print axioms sourceMap3682swap_checked
#print axioms fusedMap3682swap_checked
#print axioms certified3682swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
