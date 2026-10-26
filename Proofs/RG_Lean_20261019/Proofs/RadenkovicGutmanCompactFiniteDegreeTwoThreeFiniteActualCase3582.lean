/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3582 : Family 8 := level8.get ⟨146,by decide⟩
def sourceMap3582 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3582 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3582_checked : acceptsGraphIso
    (source (graph core3582) (root 8) 0 6) DegreeTwoThreeSpectrum5509.graph sourceMap3582=true := by decide +kernel
theorem fusedMap3582_checked : acceptsGraphIso
    (fused (graph core3582) (root 8) 0 6) DegreeTwoThreeSpectrum5511.graph fusedMap3582=true := by decide +kernel
theorem certified3582 : Certified (graph core3582) (root 8) 0 6 :=
  of_native_maps core3582 DegreeTwoThreeSpectrum5509.graph DegreeTwoThreeSpectrum5511.graph
    sourceMap3582 fusedMap3582 sourceMap3582_checked fusedMap3582_checked
    DegreeTwoThreeFiniteComparisons.comparison3582
#print axioms sourceMap3582_checked
#print axioms fusedMap3582_checked
#print axioms certified3582
def sourceMap3582swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3582swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3582swap_checked : acceptsGraphIso
    (source (graph core3582) (root 8) 6 0) DegreeTwoThreeSpectrum5509.graph sourceMap3582swap=true := by decide +kernel
theorem fusedMap3582swap_checked : acceptsGraphIso
    (fused (graph core3582) (root 8) 6 0) DegreeTwoThreeSpectrum5511.graph fusedMap3582swap=true := by decide +kernel
theorem certified3582swap : Certified (graph core3582) (root 8) 6 0 :=
  of_native_maps core3582 DegreeTwoThreeSpectrum5509.graph DegreeTwoThreeSpectrum5511.graph
    sourceMap3582swap fusedMap3582swap sourceMap3582swap_checked fusedMap3582swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3582
#print axioms sourceMap3582swap_checked
#print axioms fusedMap3582swap_checked
#print axioms certified3582swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
